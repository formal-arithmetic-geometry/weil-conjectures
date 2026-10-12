/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
public import WeilConjectures.WeilSheaf.FrobeniusMate
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The adjunction `φ^* ⊣ φ_*` of pro-étale Weil sheaves

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pullback `φ^*` and the pushforward `φ_*` of
pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.upperStar`,
`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStar`) are the functors `φ̄^*`, `φ̄_*` on the geometric
fibers with the Weil structures transported along the Frobenius exchange isomorphisms. These
exchange isomorphisms are mates
(`AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`), so the
adjunction `φ̄^* ⊣ φ̄_*` lifts to an adjunction `φ^* ⊣ φ_*` of pro-étale Weil sheaves whose unit
and counit are those of `φ̄^* ⊣ φ̄_*`
(`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`): the adjunction is
Frobenius-equivariant.

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

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

/-- A pro-étale Weil sheaf is zero if and only if its underlying sheaf is. -/
lemma ProEtaleWeilSheaf.isZero_iff {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (K : ProEtaleWeilSheaf k₀ l X) : IsZero K ↔ IsZero K.carrier :=
  ⟨fun h ↦ (IsoAlgebra.forget _).map_isZero h,
    fun h ↦ (IsZero.iff_id_eq_zero K).2 ((IsoAlgebra.forget _).map_injective (h.eq_of_src _ _))⟩

section Adjunction

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- Blueprint `prop-sf-localization-all-stages` (Weil clause): the adjunction `φ^* ⊣ φ_*` of
pro-étale Weil sheaves along a morphism `φ` of `k₀`-schemes. It lifts the adjunction
`φ̄^* ⊣ φ̄_*` on the geometric fibers, whose unit and counit are thus equivariant for the
transported Weil structures: the Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates
(`AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`). -/
noncomputable def ProEtaleWeilSheaf.upperStarLowerStarAdjunction :
    ProEtaleWeilSheaf.upperStar k₀ l φ ⊣ ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  IsoAlgebra.adjunction (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv φ _)

/-- The unit of `φ^* ⊣ φ_*` on pro-étale Weil sheaves is the unit of `φ̄^* ⊣ φ̄_*`. -/
@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_f
    (K : ProEtaleWeilSheaf k₀ l Y) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).unit.app K).hom.f =
      (adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).unit.app K.carrier :=
  rfl

/-- The counit of `φ^* ⊣ φ_*` on pro-étale Weil sheaves is the counit of `φ̄^* ⊣ φ̄_*`. -/
@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f
    (K : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit.app K).hom.f =
      (adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).counit.app K.carrier :=
  rfl

/-- For a closed immersion `φ`, the counit `φ^* φ_* ⟶ 𝟭` of pro-étale Weil sheaves is an
isomorphism. -/
instance [IsClosedImmersion φ] :
    IsIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit :=
  IsoAlgebra.isIso_adjunction_counit _

/-- For an open immersion `φ`, the counit `φ^* φ_* ⟶ 𝟭` of pro-étale Weil sheaves is an
isomorphism. -/
instance [IsOpenImmersion φ] :
    IsIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit :=
  IsoAlgebra.isIso_adjunction_counit _

end Adjunction

section Localization

variable {Z U X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

omit [IsClosedImmersion i] [QuasiCompact j] in
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

omit [IsOpenImmersion j] in
/-- Blueprint `lem-exc-open-closed-detection` for pro-étale Weil sheaves: for complementary `i`
and `j`, a pro-étale Weil sheaf `F` with `i^* F = 0` and `j^* F = 0` is zero. -/
lemma ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (F : ProEtaleWeilSheaf k₀ l X)
    (hi : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l i).obj F))
    (hj : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l j).obj F)) : IsZero F :=
  (ProEtaleWeilSheaf.isZero_iff _).2 (AdicSheaf.isZero_of_isZero_adicUpperStar_of_isCompl _ _
    (Scheme.Hom.isCompl_range_geometricFiberMap i j _ _ hij) F.carrier
    ((ProEtaleWeilSheaf.isZero_iff _).1 hi) ((ProEtaleWeilSheaf.isZero_iff _).1 hj))

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
