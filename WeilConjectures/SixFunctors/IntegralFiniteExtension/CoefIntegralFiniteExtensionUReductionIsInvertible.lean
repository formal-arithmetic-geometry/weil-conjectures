/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionFiniteUIsInvertible
/-! Levelwise reduction invertibility for the canonical integral dualizing comparison.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraph 2
(blueprint: lem-sf-integral-finite-extension-u-invertibility).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
set_option linter.style.haveILetI false in
/-- Every finite reduction of the canonical comparison is invertible.

The reduction equation `u_reduction` identifies the reduction of `u` with the
finite counit comparison. The quotient and reduction presentation maps are
isomorphisms, and the finite-free counit theorem makes `finiteU` invertible.
Pasting these isomorphisms proves the displayed levelwise assertion, including
all ramified and identity levels.
(blueprint: lem-sf-integral-finite-extension-u-reduction-is-invertible)
-/
theorem comparison_reduction_isIso_u :
    ∀ n : ℕ,
      IsIso ((scalarReductionDerivedExtension l L X n).map
        (u l E L ι X D hl wE wL)) := by
  intro n
  let rL := scalarReductionDerivedExtension l L X n
  let q := quotient l E L ι X n wE.omega.obj wE.omega.property.1
  let eE := wE.reduction n
  let eL := wL.reduction n
  let v := finiteU l E L ι X D n
  haveI : IsIso eL.hom := eL.isIso_hom
  haveI : IsIso q.hom := q.isIso_hom
  haveI : IsIso ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
      eE.hom) := Functor.map_isIso _ _
  haveI : IsIso v := finiteU_isIso l E L ι X D hl n
  have hc : IsIso (rL.map (u l E L ι X D hl wE wL) ≫ eL.hom) := by
    rw [u_reduction l E L ι X D hl wE wL n]
    infer_instance
  letI : IsIso (rL.map (u l E L ι X D hl wE wL) ≫ eL.hom) := hc
  exact IsIso.of_isIso_comp_right _ eL.hom
end WeilConjectures.IntegralFiniteExtension
