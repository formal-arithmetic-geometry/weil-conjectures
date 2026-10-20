/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.BertiniSingularFirstOrderModel
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Fibre estimates on affine charts of a Bertini singular scheme

Source: Stacks Project, Varieties, Tag 0FD6, the local first-order kernel calculation.
(blueprint: lem-zl-bertini-singular-affine-fibre-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem firstOrderKernel_dimension {K : Type u} [Field K] (r d : ℕ)
    (E : (Fin (r + 1) → K) →ₗ[K] K × (Fin d → K)) (hE : Function.Surjective E) :
    d + Module.finrank K E.ker = r ∧
      topologicalKrullDim (PrimeSpectrum (SymmetricAlgebra K (Module.Dual K E.ker))) =
        (Module.finrank K E.ker : WithBot ℕ∞) := by
  have hrank := E.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hE, finrank_top] at hrank
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
    Fintype.card_fin] at hrank
  refine ⟨by omega, ?_⟩
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv
      (SymmetricAlgebra.equivMvPolynomial (Module.finBasis K (Module.Dual K E.ker))).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp


/-- On an affine chart of dimension at most `d`, the fibres of the singular scheme have
 dimension at most `n`, with `d + n` at most one less than the number of coefficients.

Source: Stacks Project, Varieties, Tag 0FD6, final three proof paragraphs; the containment
at non-flat parameters uses the hypersurface criterion of Algebra Tag 00T7.
(blueprint: lem-zl-bertini-singular-affine-fibre-charts).

Proof: Near a point choose a generating section which trivializes the line bundle and
shrink to an affine smooth chart with free differentials of rank `d`. The rank theorem
identifies its dimension with `d`. Write the other sections as functions `f_j` times this
section, so `f_i = 1`. The conormal surjection for the immersion in the projective chart
says the `df_j` span every cotangent fibre. Thus the matrix with columns `(f_j, df_j)`
has rank `d + 1`: column `i` is `(1, 0)` and subtracting `f_j` times it gives `(0, df_j)`.
The universal equation and its differential are the homogeneous linear expressions
`F = sum x_j f_j` and `dF = sum x_j df_j`. A nonzero relative differential would make
the hypersurface projection smooth, by the hypersurface criterion, so the singular
scheme is contained topologically in `F = dF = 0`. At each residue field, solve an
invertible `(d + 1)`-minor: this kernel is affine space of dimension `r - d` when there
are `r + 1` coefficients. Its closed singular subspace has at most that dimension by
monotonicity of topological Krull dimension. Set `n = r - d`; surjectivity implies
`d ≤ r`, so `d + n = r`. The zero-dimensional and zero-kernel cases use the same argument;
if the source is empty there is no point requiring a chart. No flatness of the universal
hypersurface at the zero coefficient vector is used. -/
theorem bertini_singular_affine_fibre_charts
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible] (r : ℕ)
    (s : ULift.{u} (Fin (r + 1)) → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (fun i ↦
      (SheafOfModules.unitHomEquiv L) (Scheme.Modules.homOfGlobalSection L (s i)))))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin (r + 1))) f L
      (fun i ↦ (SheafOfModules.unitHomEquiv L)
        (Scheme.Modules.homOfGlobalSection L (s i))) hgen)] :
    ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧
      ∃ d n : ℕ, d + n ≤ r ∧ topologicalKrullDim U ≤ (d : WithBot ℕ∞) ∧
        ∀ z : U, topologicalKrullDim ((bertiniSingularToSource f L s ∣_ U).fiber z) ≤
          (n : WithBot ℕ∞) := by
  intro y
  obtain ⟨U, hyU, hU, d, hsm, hmodel⟩ :=
    bertini_singular_first_order_model f L r s hgen y
  have := hsm
  obtain ⟨E, hE, _⟩ := hmodel ⟨y, hyU⟩
  have hd := (firstOrderKernel_dimension r d E hE).1
  refine ⟨U, hyU, hU, d, r - d, by omega,
    topologicalKrullDim_le_of_smoothOfRelativeDimension (U.ι ≫ f) d, ?_⟩
  intro z
  obtain ⟨E, hE, j, hj, _⟩ := hmodel z
  have := hj
  obtain ⟨hrank, hdim⟩ := firstOrderKernel_dimension r d E hE
  have hkernel : Module.finrank ((U : Scheme).residueField z) E.ker = r - d := by omega
  have hbound := j.isClosedEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim ((bertiniSingularToSource f L s ∣_ U).fiber z) ≤
    topologicalKrullDim (PrimeSpectrum
      (SymmetricAlgebra ((U : Scheme).residueField z)
        (Module.Dual ((U : Scheme).residueField z) E.ker))) at hbound
  rwa [hdim, hkernel] at hbound

end AlgebraicGeometry
