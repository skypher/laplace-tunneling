#!/usr/bin/env python3
"""Galerkin check of the distant-interval eigenvalue asymptotics.

For 0 < s < 1/2, cell indicators belong to the zero-exterior fractional
Sobolev space.  Every stiffness-matrix entry used below is the exact integral
of the Gagliardo kernel over a pair of uniform cells.  The finite-dimensional
eigenproblems are therefore conforming Rayleigh--Ritz approximations, rather
than pointwise collocation problems.
"""

from __future__ import annotations

import argparse
import math
import time

import numpy as np
from scipy.linalg import eigh
from scipy.special import gamma


def normalization_constant(s: float) -> float:
    """The standard c_{1,s} in the singular-integral fractional Laplacian."""
    return 4.0**s * s * gamma(0.5 + s) / (math.sqrt(math.pi) * gamma(1.0 - s))


def galerkin_matrix(
    component_centers: np.ndarray, cells_per_component: int, s: float
) -> tuple[np.ndarray, float]:
    """Return the L2-orthonormal stiffness matrix and the cell width.

    Each component is an interval of length one centered at an entry of
    ``component_centers``.  The basis consists of normalized cell indicators.
    """
    if not 0.0 < s < 0.5:
        raise ValueError("piecewise-constant conformity requires 0 < s < 1/2")
    if cells_per_component < 2:
        raise ValueError("at least two cells per component are required")

    h = 1.0 / cells_per_component
    # Extended precision prevents cancellation in the second difference below
    # when two cells are far apart compared with their width.
    h_extended = np.longdouble(h)
    component_centers_extended = np.asarray(
        component_centers, dtype=np.longdouble
    )
    if component_centers_extended.ndim != 1 or component_centers_extended.size == 0:
        raise ValueError("component_centers must be a nonempty one-dimensional array")
    local_centers = np.longdouble(-0.5) + (
        np.arange(cells_per_component, dtype=np.longdouble) + np.longdouble(0.5)
    ) * h_extended

    power = 1.0 - 2.0 * s
    coefficient = np.longdouble(normalization_constant(s))

    def interaction_from_distance(distance: np.ndarray) -> np.ndarray:
        interaction = np.zeros_like(distance, dtype=np.longdouble)
        mask = distance > 0.0
        r = distance[mask]
        interaction[mask] = (
            2.0 * r**power
            - (r + h_extended) ** power
            - np.maximum(r - h_extended, np.longdouble(0.0)) ** power
        ) / (2.0 * s * power)
        return interaction

    # Assemble one local block once.  Reusing it for every component preserves
    # the exact translation invariance of the Galerkin discretization instead
    # of subtracting large translated cell coordinates.
    local_distance = np.abs(local_centers[:, None] - local_centers[None, :])
    local_stiffness = -coefficient * interaction_from_distance(local_distance)
    diagonal = coefficient * 2.0 * h_extended**power / (2.0 * s * power)
    np.fill_diagonal(local_stiffness, diagonal)

    component_count = component_centers_extended.size
    total_cells = component_count * cells_per_component
    stiffness = np.empty((total_cells, total_cells), dtype=np.longdouble)
    for i in range(component_count):
        i_slice = slice(i * cells_per_component, (i + 1) * cells_per_component)
        stiffness[i_slice, i_slice] = local_stiffness
        for j in range(i + 1, component_count):
            j_slice = slice(j * cells_per_component, (j + 1) * cells_per_component)
            displacement = component_centers_extended[i] - component_centers_extended[j]
            distance = np.abs(
                displacement + local_centers[:, None] - local_centers[None, :]
            )
            cross_stiffness = -coefficient * interaction_from_distance(distance)
            stiffness[i_slice, j_slice] = cross_stiffness
            stiffness[j_slice, i_slice] = cross_stiffness.T

    # The normalized indicator basis has mass matrix I, so divide by h.
    return np.asarray(stiffness / h_extended, dtype=np.float64), h


def first_eigenpairs(
    component_centers: np.ndarray, cells: int, s: float, count: int
) -> tuple[np.ndarray, np.ndarray, float]:
    matrix, h = galerkin_matrix(component_centers, cells, s)
    values, vectors = eigh(
        matrix,
        subset_by_index=(0, count - 1),
        driver="evr",
        check_finite=False,
    )
    return values, vectors, h


def one_well_data(cells: int, s: float) -> tuple[float, float, float]:
    values, vectors, h = first_eigenpairs(np.array([0.0]), cells, s, 2)
    ground = vectors[:, 0]
    if np.sum(ground) < 0.0:
        ground = -ground
    mass = math.sqrt(h) * float(np.sum(ground))
    return float(values[0]), float(values[1] - values[0]), mass


def effective_eigenvalues(
    normalized_centers: np.ndarray, s: float, mass: float
) -> np.ndarray:
    kappa = 1.0 + 2.0 * s
    coefficient = normalization_constant(s)
    distance = np.abs(normalized_centers[:, None] - normalized_centers[None, :])
    matrix = np.zeros_like(distance)
    mask = distance > 0.0
    matrix[mask] = -coefficient * mass**2 * distance[mask] ** (-kappa)
    return np.linalg.eigvalsh(matrix)


def check_constant_energy(cells: int, s: float) -> None:
    matrix, h = galerkin_matrix(np.array([0.0]), cells, s)
    coefficient = normalization_constant(s)
    values = np.full(cells, math.sqrt(h))
    computed = float(values @ matrix @ values)
    expected = coefficient * 2.0 / (2.0 * s * (1.0 - 2.0 * s))
    if not math.isclose(computed, expected, rel_tol=2e-10, abs_tol=2e-10):
        raise RuntimeError(
            f"constant-function energy identity failed: computed={computed}, expected={expected}"
        )


def check_translation_invariance(cells: int, s: float) -> None:
    """Check that translated components reuse the identical one-well block."""
    one_well, _ = galerkin_matrix(np.array([0.0]), cells, s)
    centers = np.array([-24.0, 0.0, 24.0])
    translated, _ = galerkin_matrix(centers, cells, s)
    for component in range(centers.size):
        block = translated[
            component * cells : (component + 1) * cells,
            component * cells : (component + 1) * cells,
        ]
        if not np.array_equal(block, one_well):
            raise RuntimeError(
                f"translation-invariance check failed for component {component}"
            )


def print_configuration(
    label: str,
    normalized_centers: np.ndarray,
    separations: list[float],
    cells: int,
    s: float,
    mu1: float,
    mass: float,
) -> None:
    kappa = 1.0 + 2.0 * s
    theta = effective_eigenvalues(normalized_centers, s, mass)
    count = len(normalized_centers)
    theta_text = " ".join(f"{value:+.8f}" for value in theta)
    print(f"configuration={label} theta=[{theta_text}]", flush=True)
    print("L scaled_shifts max_abs_error", flush=True)
    for separation in separations:
        physical_centers = separation * normalized_centers
        values, _, _ = first_eigenpairs(physical_centers, cells, s, count)
        scaled = separation**kappa * (values - mu1)
        error = float(np.max(np.abs(scaled - theta)))
        shifts = " ".join(f"{value:+.8f}" for value in scaled)
        print(f"{separation:5.1f} [{shifts}] {error:.8e}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=180)
    parser.add_argument("--s", type=float, default=0.25)
    args = parser.parse_args()

    started = time.perf_counter()
    check_constant_energy(args.cells, args.s)
    check_translation_invariance(args.cells, args.s)
    kappa = 1.0 + 2.0 * args.s
    coefficient = normalization_constant(args.s)
    print(
        f"s={args.s:.8f} kappa={kappa:.8f} c_1s={coefficient:.12f}",
        flush=True,
    )
    print("mesh_convergence", flush=True)
    print("cells mu1 gap m1", flush=True)
    mesh_sizes = sorted(set([max(30, args.cells // 3), max(40, 2 * args.cells // 3), args.cells]))
    for cells in mesh_sizes:
        check_constant_energy(cells, args.s)
        mu1, gap, mass = one_well_data(cells, args.s)
        print(f"{cells:5d} {mu1:.10f} {gap:.10f} {mass:.10f}", flush=True)

    mu1, gap, mass = one_well_data(args.cells, args.s)
    print(
        f"asymptotic_mesh cells={args.cells} mu1={mu1:.10f} "
        f"gap={gap:.10f} m1={mass:.10f}",
        flush=True,
    )
    separations = [3.0, 4.0, 6.0, 8.0, 12.0, 16.0, 24.0]
    print_configuration(
        "two_wells",
        np.array([-0.5, 0.5]),
        separations,
        args.cells,
        args.s,
        mu1,
        mass,
    )
    print_configuration(
        "three_collinear_wells",
        np.array([-1.0, 0.0, 1.0]),
        separations,
        args.cells,
        args.s,
        mu1,
        mass,
    )
    elapsed = time.perf_counter() - started
    print(f"completed elapsed_seconds={elapsed:.3f}", flush=True)


if __name__ == "__main__":
    main()
