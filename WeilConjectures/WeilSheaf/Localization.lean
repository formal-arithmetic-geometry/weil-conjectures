/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization
public import WeilConjectures.WeilSheaf.Operations
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# The closed-support triangle of Weil complexes

Let `k₀` be a finite field, `X` a quasi-compact `k₀`-scheme locally of finite type, `i : Z ⟶ X`
a closed immersion and `j : U ⟶ X` the complementary quasi-compact open immersion, both over
`k₀`. This file proves the Weil clause of blueprint `prop-sf-localization-all-stages`, at the
coefficient stage `Λ = ℚ̄_ℓ`: on Weil complexes (`AlgebraicGeometry.WeilComplex`),

1. `i_*` has a right adjoint `Ri^!`
   (`AlgebraicGeometry.WeilComplex.closedUpperShriekAdjunction`);
2. for a Weil complex `K`, the counit `i_* Ri^! K ⟶ K` and the unit `K ⟶ Rj_* j^* K` extend to a
   distinguished triangle of Weil complexes with a unique third arrow
   (`AlgebraicGeometry.WeilComplex.existsUnique_distTriang_closedSupportTriangle`), functorial
   in `K`; moreover `Ri^! Rj_* = 0` and the unit `Q ⟶ Ri^! i_* Q` is an isomorphism;
3. these structures are Weil-equivariant: forgetting the Weil structures
   (`AlgebraicGeometry.WeilComplex.forgetBoundedConstructibleAdic`) carries the closed-support
   triangle of `K` to the closed-support triangle of the underlying complex on the geometric
   fiber `X̄` (`AlgebraicGeometry.ProEtale.boundedConstructibleAdicClosedSupportTriangle`), by an
   isomorphism of triangles which is the identity on `K`
   (`AlgebraicGeometry.WeilComplex.exists_iso_mapTriangle_closedSupportTriangle`), and
   forgetting the Weil structures commutes with `Ri^!`, compatibly with the counits of
   `i_* ⊣ Ri^!` and `ī_* ⊣ Rī^!`
   (`AlgebraicGeometry.WeilComplex.exists_closedUpperShriek_comp_forget_iso`,
   `AlgebraicGeometry.WeilComplex.nonempty_forget_closedUpperShriek_obj_iso`).

The Weil structures of `i^*`, `j^*`, `i_*` and `Rj_*` are those of the transported functors on
pro-étale Weil sheaves, and the adjunctions `φ^* ⊣ φ_*` lift those on the geometric fibers
(`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`). The right adjoint `Ri^!` is
then constructed by the recollement argument `CategoryTheory.Pretriangulated.Recollement`
applied to Weil complexes, whose inputs are derived by the criterion of
`WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport` from sheaf-level facts transported
from the geometric fibers: the counit `i^* i_* ⟶ 𝟭` is invertible, `j^* i_* = 0`
(`AlgebraicGeometry.ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj`), `i^*` and `j^*`
jointly detect zero objects
(`AlgebraicGeometry.ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl`) and `i_*` is
exact (`AlgebraicGeometry.ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl`).
The equivariance follows from the
uniqueness of the closed-support triangle with given vertices
(`CategoryTheory.Pretriangulated.Recollement.exists_iso_triangle`): forgetting the Weil
structures commutes with `i_*` and `Rj_*`
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerStar_comp_forget_iso`), so it carries the
closed-support triangle of `K` to a distinguished triangle whose outer vertices lie in the
essential images of `ī_*` and `Rj̄_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Along a closed immersion `i`, the counit `i^* i_* F ⟶ F` of pro-étale Weil sheaves is
invertible, as is the counit of `ī^* ⊣ ī_*`. -/
instance ProEtaleWeilSheaf.isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (i : X ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))] :
    IsIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i).counit :=
  IsoAlgebra.isIso_mapOfNatIsoAdjunction_counit _ _ _ _

section SheafLocalization

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

end SheafLocalization

section Forget

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
/-- An object of the derived category of pro-étale Weil sheaves is a Weil complex if and only if
its underlying complex lies in `Dᵇc(X̄, ℚ̄_ℓ)`: the forgetful functor is exact and faithful, so it
preserves and reflects boundedness, and it commutes with cohomology. -/
lemma WeilComplex.objectProperty_iff (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    WeilComplex.objectProperty k₀ l X K ↔
      ProEtale.DerivedCategory.boundedConstructibleAdic l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        ((IsoAlgebra.forget _).mapDerivedCategory.obj K) := by
  refine ⟨fun hK ↦ ⟨(IsoAlgebra.forget _).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩,
    fun hK ↦ ⟨(IsoAlgebra.forget _).bounded_of_bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩⟩
  · exact (adicConstructibleSheaf l _).prop_of_iso
      (((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso n).app K) (hK.2 n)
  · exact (adicConstructibleSheaf l _).prop_of_iso
      (((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso n).app K).symm (hK.2 n)

variable (k₀ l X) in
/-- The forgetful functor from Weil complexes on `X` to `Dᵇc(X̄, ℚ̄_ℓ)`, forgetting the Weil
structure: `AlgebraicGeometry.WeilComplex.forget` with its values in `Dᵇc(X̄, ℚ̄_ℓ)`
(`AlgebraicGeometry.WeilComplex.objectProperty_iff`). -/
noncomputable def WeilComplex.forgetBoundedConstructibleAdic :
    WeilComplex k₀ l X ⥤ (ProEtale.DerivedCategory.boundedConstructibleAdic l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).FullSubcategory :=
  (WeilComplex.objectProperty k₀ l X).liftFullSubcategory _
    (IsoAlgebra.forget _).mapDerivedCategory fun K hK ↦ (WeilComplex.objectProperty_iff K).1 hK

instance : (WeilComplex.forgetBoundedConstructibleAdic k₀ l X).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

noncomputable instance : (WeilComplex.forgetBoundedConstructibleAdic k₀ l X).CommShift ℤ :=
  ObjectProperty.commShiftLiftFullSubcategory _ _ _ _

/-- Forgetting the Weil structure is a triangulated functor. -/
instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.forgetBoundedConstructibleAdic k₀ l X).IsTriangulated :=
  ObjectProperty.isTriangulated_liftFullSubcategory _ _ _ _

end Forget

section Adjunction

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The adjunction `D(φ^*) ⊣ Rφ_*` on the derived categories of pro-étale Weil sheaves, derived
from `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`. -/
noncomputable def ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction :
    (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory ⊣
      (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor :=
  (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).mapDerivedCategoryRightDerivedAdjunction

variable [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `prop-sf-localization-all-stages` (Weil clause): the adjunction `φ^* ⊣ Rφ_*` of
Weil complexes, the restriction of
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction`. -/
noncomputable def WeilComplex.upperStarDerivedLowerStarAdjunction :
    WeilComplex.upperStar (k₀ := k₀) (l := l) φ ⊣ WeilComplex.derivedLowerStar φ :=
  (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l φ).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _) (Iso.refl _)

/-- If the counit of `φ^* ⊣ φ_*` on pro-étale Weil sheaves is an isomorphism (e.g. for a closed
or an open immersion), the derived pushforward `Rφ_*` of Weil complexes is fully faithful. -/
noncomputable def WeilComplex.fullyFaithfulDerivedLowerStar
    [IsIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit] :
    (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).FullyFaithful :=
  have : IsIso (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l φ).counit :=
    Adjunction.isIso_mapDerivedCategoryRightDerivedAdjunction_counit _
  have h :=
    (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l φ).fullyFaithfulROfIsIsoCounit
  have := h.full
  have := h.faithful
  have : (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).Full :=
    ObjectProperty.liftFullSubcategory_full _ _ _ _
  have : (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).Faithful :=
    ObjectProperty.liftFullSubcategory_faithful _ _ _ _
  .ofFullyFaithful _

/-- If the counit of `φ^* ⊣ φ_*` on pro-étale Weil sheaves is an isomorphism, so is the counit
of `φ^* ⊣ Rφ_*` on Weil complexes. -/
instance WeilComplex.isIso_upperStarDerivedLowerStarAdjunction_counit
    [IsIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit] :
    IsIso (WeilComplex.upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) φ).counit :=
  have := (WeilComplex.fullyFaithfulDerivedLowerStar (k₀ := k₀) (l := l) φ).full
  have := (WeilComplex.fullyFaithfulDerivedLowerStar (k₀ := k₀) (l := l) φ).faithful
  Adjunction.counit_isIso_of_R_fully_faithful _

end Adjunction

section Localization

variable {Z U X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))

include hij in
/-- `j^* i_* = 0` on Weil complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj` and
`DerivedCategory.isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj`). -/
lemma WeilComplex.isZero_upperStar_obj_derivedLowerStar_obj (M : WeilComplex k₀ l Z) :
    IsZero ((WeilComplex.upperStar j).obj ((WeilComplex.derivedLowerStar i).obj M)) :=
  have := ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl (k₀ := k₀) (l := l)
    i j hij
  IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
    (DerivedCategory.isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj
      (ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj i j hij) M.obj)

include hij in
/-- A Weil complex `K` on `X` with `j^* K = 0` is `i_*` of the Weil complex `i^* K`: the unit
`K ⟶ Ri_* i^* K` is an isomorphism
(`DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero`). -/
lemma WeilComplex.derivedLowerStar_essImage_of_isZero (K : WeilComplex k₀ l X)
    (hK : IsZero ((WeilComplex.upperStar j).obj K)) :
    (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) i).essImage K := by
  have := ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl (k₀ := k₀) (l := l)
    i j hij
  have hiso := DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i)
    (ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj i j hij)
    (ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij)
    ((ObjectProperty.ι _).map_isZero hK)
  exact ⟨(WeilComplex.upperStar i).obj K, ⟨ObjectProperty.isoMk _ (@asIso _ _ _ _
    ((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l i).unit.app K.obj) hiso).symm⟩⟩

include hij in
/-- Blueprint `prop-sf-localization-all-stages` (Weil clause), the vanishing:
`Hom(i_* Q[m], Rj_* G) = 0` for Weil complexes `Q` on `Z` and `G` on `U`. -/
lemma WeilComplex.subsingleton_hom_shift (Q : WeilComplex k₀ l Z) (G : WeilComplex k₀ l U)
    (m : ℤ) :
    Subsingleton (((WeilComplex.derivedLowerStar i).obj Q)⟦m⟧ ⟶
      (WeilComplex.derivedLowerStar j).obj G) :=
  Recollement.subsingleton_hom_shift _ _ (WeilComplex.upperStarDerivedLowerStarAdjunction j)
    (WeilComplex.isZero_upperStar_obj_derivedLowerStar_obj i j hij) Q G m

include j hij in
/-- The direct image `i_*` of Weil complexes along a closed immersion is a left adjoint
(`CategoryTheory.Pretriangulated.Recollement.isLeftAdjoint`). -/
lemma WeilComplex.isLeftAdjoint_derivedLowerStar :
    (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) i).IsLeftAdjoint := by
  have := locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  exact Recollement.isLeftAdjoint (WeilComplex.upperStarDerivedLowerStarAdjunction j)
    (WeilComplex.fullyFaithfulDerivedLowerStar i)
    (WeilComplex.isZero_upperStar_obj_derivedLowerStar_obj i j hij)
    (WeilComplex.derivedLowerStar_essImage_of_isZero i j hij)

section Equivariance

end Equivariance

end Localization

end AlgebraicGeometry
