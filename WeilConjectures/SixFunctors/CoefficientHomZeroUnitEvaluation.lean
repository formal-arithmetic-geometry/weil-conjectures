/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientHomZeroClass
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData

/-! # Evaluation against the native tensor unit

Source: Stacks 08JA and the normalized closed-transpose compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe a av c v u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

/-- Transport the native left unitor along uniqueness of left adjoints to the same
internal Hom. This uses the chosen closed adjunction, without identifying its
monoidal constraints with the native constraints.
Source: adjoint uniqueness and the native unit, Stacks 08J9.
(blueprint: lem-coef-hom-zero-unit-evaluation). -/
def coefficientHomLeftUnit
    {A : Type a} [Category.{av} A] {H : Aᵒᵖ × A ⥤ A}
    (S S₀ : CoefficientClosedStructure H) (K : A) :
    S.tensor.obj (S₀.monoidal.tensorUnit, K) ≅ K :=
  (Adjunction.leftAdjointUniq (S.adjunction K) (S₀.adjunction K)).app
    S₀.monoidal.tensorUnit ≪≫ S₀.monoidal.leftUnitor K

/-- Transporting the unit does not change the unitor-adjusted inverse transpose.
Source: the defining Hom equation of left-adjoint uniqueness, Stacks 08J9.
(blueprint: lem-coef-hom-zero-unit-evaluation).
Proof: naturality of the Hom equivalence says that the uniqueness isomorphism
followed by the second inverse transpose is the first inverse transpose. Cancel
that isomorphism against its inverse in the transported unitor. -/
theorem coefficientHomLeftUnit_uncurry
    {A : Type a} [Category.{av} A] {H : Aᵒᵖ × A ⥤ A}
    (S S₀ : CoefficientClosedStructure H) (K L : A)
    (q : S₀.monoidal.tensorUnit ⟶ H.obj (op K, L)) :
    (coefficientHomLeftUnit S S₀ K).inv ≫
        (S.transpose S₀.monoidal.tensorUnit K L).symm q =
      (S₀.monoidal.leftUnitor K).inv ≫
        (S₀.transpose S₀.monoidal.tensorUnit K L).symm q := by
  let d := Adjunction.leftAdjointUniq (S.adjunction K) (S₀.adjunction K)
  have hd : d.hom.app S₀.monoidal.tensorUnit ≫
      (S₀.transpose S₀.monoidal.tensorUnit K L).symm q =
        (S.transpose S₀.monoidal.tensorUnit K L).symm q := by
    apply (S.transpose S₀.monoidal.tensorUnit K L).injective
    change (S.adjunction K).homEquiv _ _ (_ ≫ _) = _
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
      Equiv.apply_symm_apply]
    change (S₀.transpose _ K L) ((S₀.transpose _ K L).symm q) = q
    exact Equiv.apply_symm_apply _ _
  rw [← hd]
  simp only [coefficientHomLeftUnit, Iso.trans_inv, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app_assoc, d]

section RingedSite
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{c, v, u} J A)]
  (S₀ : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
  (hS₀ : S₀.monoidal = RingedDerivedNative.monoidal.{c, v, u, w} J A)
  (T₀ : CoefficientTensorModels.{u, c, v, w} J A S₀)
  (hT₀ : HEq T₀.comparison (RingedDerivedNative.comparison.{c, v, u, w} J A))

set_option maxHeartbeats 1200000 in
-- Unfold the two fixed additive equivalences, retaining independent site universes.
include hS₀ T₀ hT₀ in
end RingedSite
end WeilConjectures
