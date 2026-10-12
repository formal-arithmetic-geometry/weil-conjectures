/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The adjunction `φ^* ⊣ φ_*` of pro-étale Weil sheaves

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes. The pullback and the pushforward of pro-étale
Weil sheaves along `φ` are the pullback and the pushforward along the base change
`φ̄ : X̄ ⟶ Ȳ`, with the Weil structures transported along the Frobenius exchange isomorphisms.
These exchange isomorphisms are mates under `φ̄^* ⊣ φ̄_*`
(`AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`), so
the adjunction lifts to pro-étale Weil sheaves, with the unit and the counit of `φ̄^* ⊣ φ̄_*`.

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`: the adjunction
  `φ^* ⊣ φ_*` of pro-étale Weil sheaves.
- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f`: its
  counit is the counit of `φ̄^* ⊣ φ̄_*`; along an open immersion it is invertible.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The adjunction `φ^* ⊣ φ_*` of pro-étale Weil sheaves along a morphism `φ : X ⟶ Y` of
`k₀`-schemes: the adjunction `φ̄^* ⊣ φ̄_*` along the base change `φ̄ : X̄ ⟶ Ȳ`, which is
compatible with the transported Weil structures. -/
noncomputable def ProEtaleWeilSheaf.upperStarLowerStarAdjunction (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.upperStar k₀ l φ ⊣ ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  IsoAlgebra.mapOfNatIsoAdjunction
    (ProEtale.adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ (comp_over φ _)))
    _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l φ _)

omit [Fact (ringChar k₀ ≠ l)] in
@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_f (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (F : ProEtaleWeilSheaf k₀ l Y) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).unit.app F).hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).unit.app F.carrier :=
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (F : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit.app F).hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).counit.app F.carrier :=
  rfl

/-- Along an open immersion `j`, the counit `j^* j_* F ⟶ F` of pro-étale Weil sheaves is
invertible: so is the counit of `j̄^* ⊣ j̄_*`, and the forgetful functor reflects isomorphisms. -/
instance ProEtaleWeilSheaf.isIso_upperStarLowerStarAdjunction_counit (j : X ⟶ Y)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    IsIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  have : IsIso ((IsoAlgebra.forget _).map
      ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).counit.app F)) :=
    inferInstanceAs (IsIso ((ProEtale.adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app F.carrier))
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)

end AlgebraicGeometry
