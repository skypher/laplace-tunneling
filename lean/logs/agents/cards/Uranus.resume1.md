Main agent to luna_max_Uranus (T11, DecompForm.lean), round 2. Your partial file (interaction_symm proved, formQ_eq sorry) is installed in the repository (Tunneling/Euclid/DecompForm.lean, readable). `formQ_eq` is not blocked: construct the missing pairwise identity now. No time limit.
Target lemma (i ≠ j), with ψ_j := translateL2 (L•a j) (pieceL2 j ψ) (= 1_{D_j} ψ a.e.), both in formDomain κ Ω:
  QuadraticMap.polar (formQ c κ Ω) ψ_i ψ_j = -2 * c * crossPair i j (pieceL2 i ψ) (pieceL2 j ψ).
Proof:
 1. formQ_polar (FormDomain.lean, now PROVED and compiled) gives polar = c ∫ (ψ_i x - ψ_i y)(ψ_j x - ψ_j y) ‖x-y‖^(-κ) d(vol×vol).
 2. Disjoint supports: ψ_i vanishes a.e. off D_i, ψ_j a.e. off D_j, D_i ∩ D_j = ∅ (separation ‖(x - L a_i) - (x - L a_j)‖ = L‖a_i - a_j‖ ≥ 4R > 2R while both points are in ball 0 R). Hence ψ_i(x) ψ_j(x) = 0 for a.e. x, so a.e. on the product (lift through Measure.quasiMeasurePreserving_fst/snd):
    (ψ_i x - ψ_i y)(ψ_j x - ψ_j y) = -ψ_i x ψ_j y - ψ_i y ψ_j x.
 3. Integrability of z ↦ ψ_i(z.1) ψ_j(z.2) ‖z.1 - z.2‖^(-κ): a.e. nonzero only on D_i × D_j where ‖x - y‖ ≥ L‖a_i - a_j‖ - 2R ≥ 2R, so the kernel is ≤ (2R)^(-κ) there; ψ_i, ψ_j ∈ L¹ (L² on finite-measure sets). Use Integrable.mono' with the bound (2R)^(-κ)|ψ_i x||ψ_j y| (integrable product: Integrable.mul_prod / integrable_prod_mul).
 4. Swap symmetry (integral_prod_swap) turns ∫ ψ_i y ψ_j x K into ∫ ψ_i x ψ_j y K, so polar = -2c ∫ ψ_i(x)ψ_j(y)‖x - y‖^(-κ).
 5. Change of variables x = x' + L a_i, y = y' + L a_j (MeasurePreserving.prod of two translations; integral_comp for a measure-preserving equivalence): ψ_i(x'+La_i) = pieceL2 i ψ (x') a.e. (translateL2_ae), ‖(x'+La_i) - (y'+La_j)‖ = ‖L•(a_i - a_j) + x' - y'‖ = multiWellCrossKernel κ (L•(a i - a j)) x' y' raised... (multiWellCrossKernel κ center x y = ‖center + x - y‖^(-κ)). This is kernelCrossPairing (multiWellCrossKernel ...) volume u_i u_j = crossPair i j u_i u_j.
 Then assemble with your existing reconstruction ψ = Σ_j ψ_j and diagonal translation.
Delivery protocol (changed): the main agent extracts your file from the heredoc of your LAST full-file `lean --stdin` command whose output has no errors and compares it with the text between the markers in your final message. Make your last full-file check exactly the delivered file.
