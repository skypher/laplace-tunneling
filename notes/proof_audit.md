# Two-well proof audit

## Source checks

- Brasco--Parini, Theorem 2.8, specialized to `p=2`: the first restricted
  fractional eigenvalue on a bounded open set is simple and its eigenfunction
  has one strict sign.
- Brasco--Parini, Theorem 6.2, specialized to `p=2`: the nonlocal
  Hong--Krahn--Szegő bound is strict, and two equal balls whose mutual distance
  tends to infinity form a minimizing sequence.
- Di Nezza--Palatucci--Valdinoci, Theorem 5.4: bounded Lipschitz domains are
  fractional Sobolev extension domains.  Their Theorem 7.1 then gives the
  compact embedding needed for compact resolvent and discreteness.  The form
  norm is the inherited fractional Sobolev norm up to fixed constants, so
  the zero-exterior form is closed.
- Parini--Salort, Theorems 1.2 and 1.3: the cited dichotomy is qualitative
  resolvent convergence for components whose distance tends to infinity.

## Sign and coefficient check

For functions `u` and `v` supported on the two different components, direct
expansion of the Gagliardo form gives

`q[u+v] - q[u] - q[v] = -2 c Re integral(u conjugate(v) K)`.

Thus the off-diagonal operator has negative kernel.  Compression to the two
translated ground states gives the matrix

`[[mu, t_L], [t_L, mu]]`,

where

`t_L = -c double_integral(phi(x) phi(y) K_L(x,y)) < 0`.

Its levels are `mu+t_L` and `mu-t_L`; their difference is `-2t_L`.  Since
`K_L = L^(-d-2s) + lower-order terms`, the coefficient of the difference is
`2 c (integral phi)^2`.

Central symmetry makes the ground state even.  Consequently the integral of
the first Taylor term, proportional to `e dot (x+y)`, vanishes.  The kernel
remainder is therefore order `L^(-d-2s-2)`.  The spectral perturbation
remainder is quadratic in the coupling, hence order `L^(-2d-4s)`.

## Applications and release status

- The source search and bounded priority claim are recorded in
  `notes/literature_audit.md`.
- Proposition 5.1 and Corollary 5.2 supply the exact fixed-mesh matrix and its
  cluster asymptotic.
- The 180-cell two- and three-well data are saved in
  `numerics/asymptotics_180.txt` and reproduced in Tables 1--2.
- The final theorem, source, numerical, and archive checks are recorded in
  `notes/final_audit.md`.

## Multi-well proof audit

The reference domain in Section 4 is an arbitrary bounded Lipschitz domain.
Central symmetry enters the separate reflection construction of Sections
2--3 and is restored in Corollary 4.7, but it is not used by Theorem 4.6.

### Exact operator and sign

Under the translation map from the component `D + L a_j` to `D`, the diagonal
operator is the direct sum of `N` copies of `A_D`.  Expanding the Gagliardo
form for a pair `i < j` gives exactly

`-2 c Re integral integral(u_i conjugate(u_j) / |L(a_i-a_j)+x-y|^kappa)`.

Thus the off-diagonal block has negative kernel and the `(j,i)` block is the
adjoint of the `(i,j)` block.  No diagonal interaction term is omitted.

### Operator norm

If `L delta_a >= 4R`, then

`|L(a_i-a_j)+x-y| >= L |a_i-a_j| / 2`.

The Schur test bounds each block by

`c 2^kappa |D| L^(-kappa) |a_i-a_j|^(-kappa)`.

Applying the symmetric matrix row-sum bound to the matrix of block norms gives
the stated `gamma_L` bound for the full coupling operator.

### Degenerate spectral cluster

For `psi = p + q` with `p` in the `N`-dimensional ground-state space and `q`
orthogonal to it, the spectral gap and `||W|| = b` give

`<psi,(A+W)psi> >= mu||psi||^2 + <p,PWP p> + (g-b)||q||^2 - 2b||p||||q||`.

The inequality

`2b||p||||q|| <= (2b^2/g)||p||^2 + (g/2)||q||^2`

leaves the orthogonal block at height `mu + g/2 - b`.  When `b <= g/4`, this
is above all `N` eigenvalues of the comparison ground-state block.  Min--max
therefore places each full cluster eigenvalue between the corresponding
compressed eigenvalue and that number minus `2b^2/g`.  The same min--max
principle gives `lambda_(N+1) >= mu + g - b`.

### Matrix coefficient and Taylor remainder

Compression to the translated ground states gives the exact off-diagonal
entry

`-c integral integral(phi_1(x) phi_1(y) / |L(a_i-a_j)+x-y|^kappa)`.

The first Taylor term integrates to zero because the integral of
`phi_1(x)phi_1(y)(x-y)` is zero.  The Hessian bound on the segment from `0` to
`x-y` produces

`C_(kappa,R) L^(-kappa-2) |a_i-a_j|^(-kappa-2)`.

The symmetric matrix row-sum bound then gives `epsilon_L`.  Weyl's ordered
finite-dimensional min--max estimate and the cluster bound yield Theorem 4.6.

For the regular-simplex specialization, translating one center to the origin
gives an `(N-1)`-vector Gram matrix with diagonal `r^2` and off-diagonal
`r^2/2`.  Its positive definiteness implies `N-1 <= d`, as now stated in
Corollary 4.9.

### Independent diagnostic

An unbuffered random-matrix replay checked 10,800 finite-dimensional instances
of the isolated-cluster inequalities, with zero violations at numerical
tolerance.  This is a diagnostic check; the manuscript proof is the min--max
argument above.
