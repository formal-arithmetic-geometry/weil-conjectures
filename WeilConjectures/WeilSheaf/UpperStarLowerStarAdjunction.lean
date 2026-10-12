/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
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

For a closed immersion `i : Z ⟶ X` with complementary quasi-compact open immersion `j : U ⟶ X`,
the facts behind the closed-support triangle (blueprint `prop-sf-localization-all-stages`, Weil
clause) are transported from the `ℓ`-adic sheaves on the geometric fibers, the base changes
`ī`, `j̄` of `i`, `j` being again complementary
(`AlgebraicGeometry.Scheme.Hom.isCompl_range_geometricFiberMap`):

* the counit `i^* i_* ⟶ 𝟭` is an isomorphism;
* `j^* i_* = 0` (`AlgebraicGeometry.ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj`);
* `i^*` and `j^*` jointly detect zero objects
  (`AlgebraicGeometry.ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl`);
* `i_*` is exact
  (`AlgebraicGeometry.ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl`).

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`: the adjunction
  `φ^* ⊣ φ_*` of pro-étale Weil sheaves.
- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f`: its
  counit is the counit of `φ̄^* ⊣ φ̄_*`; along an open or a closed immersion it is invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section GeometricFiber

variable {k : Type u} [Field k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The base change to `k̄` of a closed immersion is a closed immersion. -/
instance [IsClosedImmersion φ] : IsClosedImmersion (Scheme.Hom.geometricFiberMap φ h) :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsClosedImmersion) φ h ‹_›

/-- The range of the base change `φ̄ : X ⟶ Y` of `φ` to `k̄` is the preimage of the range of `φ`
in the geometric fiber `Y`. -/
lemma Scheme.Hom.range_geometricFiberMap :
    Set.range (Scheme.Hom.geometricFiberMap φ h).base =
      g.geometricFiberProj.base ⁻¹' Set.range φ.base := by
  refine (Scheme.Pullback.range_map f (Scheme.specAlgebraicClosure k).hom g
    (Scheme.specAlgebraicClosure k).hom φ (𝟙 _) (𝟙 _) (by simp [h]) (by simp)).trans ?_
  simp [Scheme.Hom.geometricFiberProj]
  rfl

/-- The base changes to `k̄` of morphisms with complementary ranges have complementary
ranges. -/
lemma Scheme.Hom.isCompl_range_geometricFiberMap {Z₀ U₀ : Scheme.{u}}
    {e : Z₀ ⟶ Spec (.of k)} {d : U₀ ⟶ Spec (.of k)} (i : Z₀ ⟶ X₀) (j : U₀ ⟶ X₀)
    (hi : i ≫ f = e) (hj : j ≫ f = d) (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    IsCompl (Set.range (Scheme.Hom.geometricFiberMap i hi).base)
      (Set.range (Scheme.Hom.geometricFiberMap j hj).base) := by
  rw [range_geometricFiberMap, range_geometricFiberMap]
  exact hij.preimage _

end GeometricFiber

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

omit [Fact (ringChar k₀ ≠ l)] in
/-- A pro-étale Weil sheaf is zero if and only if its underlying sheaf is. -/
lemma ProEtaleWeilSheaf.isZero_iff {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (K : ProEtaleWeilSheaf k₀ l X) : IsZero K ↔ IsZero K.carrier :=
  ⟨fun h ↦ (IsoAlgebra.forget _).map_isZero h,
    fun h ↦ (IsZero.iff_id_eq_zero K).2 ((IsoAlgebra.forget _).map_injective (h.eq_of_src _ _))⟩

section Adjunction

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

/-- Along a closed immersion `i`, the counit `i^* i_* F ⟶ F` of pro-étale Weil sheaves is
invertible, as is the counit of `ī^* ⊣ ī_*`. -/
instance ProEtaleWeilSheaf.isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion
    (i : X ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))] :
    IsIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i).counit :=
  IsoAlgebra.isIso_mapOfNatIsoAdjunction_counit _ _ _ _

end Adjunction

section Localization

variable {Z U X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] [IsClosedImmersion i] [QuasiCompact j] in
include j in
/-- `j^* i_* = 0` on pro-étale Weil sheaves, for complementary `i` and `j`
(`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_obj_adicLowerStar_obj` on the underlying
sheaves). -/
lemma ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (M : ProEtaleWeilSheaf k₀ l Z) :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l j).obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l i).obj M)) :=
  (ProEtaleWeilSheaf.isZero_iff _).2 (isZero_adicUpperStar_obj_adicLowerStar_obj _ _
    (Scheme.Hom.isCompl_range_geometricFiberMap i j _ _ hij).disjoint M.carrier)

omit [Fact (ringChar k₀ ≠ l)] [IsOpenImmersion j] in
/-- Blueprint `lem-exc-open-closed-detection` for pro-étale Weil sheaves: for complementary `i`
and `j`, a pro-étale Weil sheaf `F` with `i^* F = 0` and `j^* F = 0` is zero. -/
lemma ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (F : ProEtaleWeilSheaf k₀ l X)
    (hi : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l i).obj F))
    (hj : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l j).obj F)) : IsZero F :=
  (ProEtaleWeilSheaf.isZero_iff _).2 (AdicSheaf.isZero_of_isZero_adicUpperStar_of_isCompl _ _
    (Scheme.Hom.isCompl_range_geometricFiberMap i j _ _ hij) F.carrier
    ((ProEtaleWeilSheaf.isZero_iff _).1 hi) ((ProEtaleWeilSheaf.isZero_iff _).1 hj))

omit [Fact (ringChar k₀ ≠ l)] in
include j in
/-- Blueprint `lem-exc-proetale-closed-exact` for pro-étale Weil sheaves: for complementary `i`
and `j`, the pushforward `i_*` of pro-étale Weil sheaves is exact, as it is on the underlying
sheaves (`AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_isCompl`). -/
lemma ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    PreservesFiniteColimits (ProEtaleWeilSheaf.lowerStar k₀ l i) :=
  have := preservesFiniteColimits_adicLowerStar_of_isCompl (l := l) _ _
    (Scheme.Hom.isCompl_range_geometricFiberMap i j (comp_over i (Spec (CommRingCat.of k₀)))
      (comp_over j (Spec (CommRingCat.of k₀))) hij)
  IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

end Localization

end AlgebraicGeometry
