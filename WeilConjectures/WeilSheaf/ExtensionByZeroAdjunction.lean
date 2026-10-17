/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# The adjunction `j_! ⊣ j^*` of pro-étale Weil sheaves

Let `j : U ⟶ X` be an open immersion of `k₀`-schemes. The extension by zero `j_!` and the
pullback `j^*` of pro-étale Weil sheaves are the extension by zero and the pullback along the base
change `j̄ : Ū ⟶ X̄`, with the Weil structures transported along the Frobenius exchange
isomorphisms. These exchange isomorphisms are mates under `j̄_! ⊣ j̄^*`
(`ProEtale.mateEquiv_adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso_inv`), so the
adjunction lifts to pro-étale Weil sheaves, with the unit and the counit of `j̄_! ⊣ j̄^*`
(`AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction`). Its unit is an
isomorphism: `j_!` is fully faithful.

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction`: `j_! ⊣ j^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [IsOpenImmersion φ]

/-- **The Frobenius exchange isomorphisms of `φ̄_!` and `φ̄^*` are mates**: under the adjunction
`φ̄_! ⊣ φ̄^*`, the mate of the inverse of the exchange isomorphism
`φ̄_! ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_!` of the extension by zero is the exchange isomorphism
`φ̄^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Y⁻¹)_* ⋙ φ̄^*` of the pullback. -/
lemma mateEquiv_adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso_inv :
    (mateEquiv (adicOpenImmersionLowerShriekAdjunction l (Scheme.Hom.geometricFiberMap φ h))
      (adicOpenImmersionLowerShriekAdjunction l (Scheme.Hom.geometricFiberMap φ h))
      (TwoSquare.mk _ _ _ _
        (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l φ h).inv)).natTrans =
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).hom := by
  sorry

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The adjunction `j_! ⊣ j^*` of pro-étale Weil sheaves along an open immersion `j` of
`k₀`-schemes: the adjunction `j̄_! ⊣ j̄^*` along the base change `j̄ : Ū ⟶ X̄`, which is compatible
with the transported Weil structures. -/
noncomputable def ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j :=
  IsoAlgebra.mapOfNatIsoAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)))
    _ _ (ProEtale.mateEquiv_adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso_inv l j _)

@[simp]
lemma ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction_unit_app_hom_f (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] (F : ProEtaleWeilSheaf k₀ l U) :
    ((ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l j).unit.app F).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app F.carrier :=
  rfl

@[simp]
lemma ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction_counit_app_hom_f (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] (F : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l j).counit.app F).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app F.carrier :=
  rfl

/-- The unit `F ⟶ j^* j_! F` of pro-étale Weil sheaves is an isomorphism: so is the unit of
`j̄_! ⊣ j̄^*`. -/
instance ProEtaleWeilSheaf.isIso_extensionByZeroUpperStarAdjunction_unit (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    IsIso (ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l j).unit :=
  IsoAlgebra.isIso_mapOfNatIsoAdjunction_unit _ _ _ _

end AlgebraicGeometry
