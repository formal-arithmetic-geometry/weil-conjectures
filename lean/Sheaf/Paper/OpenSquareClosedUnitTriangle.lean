module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.ModuleDerivedFunctorCompositorShifts
import Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!
# Closed-unit localization after an open direct image

Source: blueprint main-20261015, direct-image stability proof (3), agent-extracted
localization input; Stacks, Tags 09AH, 09BM, 09BN, 0152 and 015F
(blueprint: lem-sfb-open-square-closed-unit-triangle).

The functors below only name the specified composites on internal module derived categories.
The theorem retains the actual derived closed unit and the actual open counit, including
naturality in the degree-zero module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.OpenSquareClosedUnit

open CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem natural_triangle
    {C U Z : Type*} [Category C] [Category U] [Category Z]
    [HasShift U ℤ]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive Z] [HasZeroObject Z] [HasShift Z ℤ]
    [∀ n : ℤ, (shiftFunctor Z n).Additive] [Pretriangulated Z]
    (J : U ⥤ C) (P : C ⥤ U) (Q : C ⥤ Z) (I : Z ⥤ C)
    [J.CommShift ℤ] [Q.CommShift ℤ] [Q.IsTriangulated]
    (a : J ⊣ P) (d : Q ⊣ I) [IsIso d.counit]
    (hJ : J.FullyFaithful) (hz : ∀ M, IsZero (Q.obj (J.obj M)))
    (he : ∀ K, IsZero (Q.obj K) → J.essImage K) :
    ∃ δ : Q ⋙ I ⟶ P ⋙ J ⋙ shiftFunctor C (1 : ℤ),
      ∀ K, Triangle.mk (a.counit.app K) (d.unit.app K) (δ.app K) ∈ distTriang C := by
  classical
  have hex := Recollement.existsUnique_distTriang_counit_unit d a hJ hz he
  let w := fun K ↦ (hex K).choose
  have hw : ∀ K, Recollement.triangle d a K (w K) ∈ distTriang C :=
    fun K ↦ (hex K).choose_spec.1
  refine ⟨{ app := w, naturality := ?_ }, hw⟩
  intro K L f
  obtain ⟨τ, h₁, h₂, h₃⟩ := Recollement.exists_triangleHom d a hz f (hw K) (hw L)
  simpa only [h₁, h₃, Functor.comp_map] using τ.comm₃.symm

private theorem open_essImage
    {C U Z : Type*} [Category C] [Category U] [Category Z]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive U] [HasZeroObject U] [HasShift U ℤ]
    [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
    [Preadditive Z] [HasZeroObject Z] [HasShift Z ℤ]
    [∀ n : ℤ, (shiftFunctor Z n).Additive] [Pretriangulated Z]
    (J : U ⥤ C) (P : C ⥤ U) (Q : C ⥤ Z)
    [P.CommShift ℤ] [Q.CommShift ℤ] [P.IsTriangulated] [Q.IsTriangulated]
    (a : J ⊣ P) [IsIso a.unit]
    (hz : ∀ M, IsZero (Q.obj (J.obj M)))
    (hd : ∀ K, IsZero (P.obj K) → IsZero (Q.obj K) → IsZero K)
    (K : C) (hK : IsZero (Q.obj K)) : J.essImage K := by
  obtain ⟨W, v, w, hT⟩ := distinguished_cocone_triangle (a.counit.app K)
  have hp : IsIso (P.map (a.counit.app K)) := by
    have : IsIso (a.unit.app (P.obj K) ≫ P.map (a.counit.app K)) := by
      rw [a.right_triangle_components K]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (a.unit.app (P.obj K)) _
  have hq : IsIso (Q.map (a.counit.app K)) :=
    isIso_of_source_target_iso_zero _ (hz _).isoZero hK.isoZero
  have hW : IsZero W := hd _
    ((Triangle.isZero₃_iff_isIso₁ _ (P.map_distinguished _ hT)).2 hp)
    ((Triangle.isZero₃_iff_isIso₁ _ (Q.map_distinguished _ hT)).2 hq)
  have : IsIso (a.counit.app K) := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hW
  exact ⟨P.obj K, ⟨asIso (a.counit.app K)⟩⟩

private theorem change_first
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {X : C} (e : X ≅ T.obj₁) :
    Triangle.mk (e.hom ≫ T.mor₁) T.mor₂
      (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e.inv) ∈ distTriang C := by
  apply isomorphic_distinguished _ hT
  refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp
  · simp
  · have hh : (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e.inv) ≫
          (shiftFunctor C (1 : ℤ)).map e.hom = T.mor₃ := by
      rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp, e.inv_hom_id,
        (shiftFunctor C (1 : ℤ)).map_id, Category.comp_id]
    simpa only [Triangle.mk_mor₃, Iso.refl_hom, Category.id_comp] using hh

private theorem isGE_of_iso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y : DerivedCategory C} (e : X ≅ Y) (hY : Y.IsGE (0 : ℤ)) : X.IsGE (0 : ℤ) := by
  let := hY
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm 0

/-- The family `K_M = Rb_* M[0]` of the localization statement.
Source: extracted localization input, definition of K
(blueprint: lem-sfb-open-square-closed-unit-triangle). -/
def directImage {W V : Scheme.{u}} (b : W ⟶ V) :=
  DerivedCategory.singleFunctor
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) 0 ⋙
    moduleObjectDerivedPushforward Λ b

/-- The family `B_M = Rj_* b_! M[0]`, using exact termwise extension by zero.
Source: extracted localization input, definition of B_M
(blueprint: lem-sfb-open-square-closed-unit-triangle). -/
def extensionImage {W V Y : Scheme.{u}} (j : V ⟶ Y) (b : W ⟶ V)
    [IsOpenImmersion b] :=
  DerivedCategory.singleFunctor
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) 0 ⋙
    (CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategory ⋙
      moduleObjectDerivedPushforward Λ j

/-- The exact derived composite `i^* Rj_*` applied to the localization triangle.
Source: extracted localization input, the displayed triangle
(blueprint: lem-sfb-open-square-closed-unit-triangle). -/
def image {V Y Z : Scheme.{u}} (j : V ⟶ Y) (i : Z ⟶ Y) :=
  moduleObjectDerivedPushforward Λ j ⋙ moduleObjectDerivedPullback Λ i

set_option maxHeartbeats 600000 in
-- Comparing the canonical derived composites consumes extra elaboration heartbeats.
/-- The first, middle and last unshifted vertices form a natural distinguished triangle,
with its prescribed first arrow, actual closed unit, and zero/isomorphism criterion.
Source: extracted localization input in direct-image stability proof (3), and Stacks
09AH, 09BM, 09BN, 0152, 015F, 05SE, 05TC, 05RS, 05RT
(blueprint: lem-sfb-open-square-closed-unit-triangle).

Proof:
1. Noetherianity makes b quasi-compact. The existing condensed recollement theorem
supplies exactness and full faithfulness of the underived closed direct image.
2. Exact pullbacks preserve the relevant homology calculations. Disjointness gives
h^*b_! = 0, and complementary restrictions jointly detect zero. Completing the open
counit to a triangle then proves the required open essential-image criterion.
3. The source recollement API gives a triangle with the actual open counit and closed
unit. Its unique connecting maps are natural by the triangle-morphism theorem.
4. The adjunction triple b_! ⊣ b^* ⊣ Rb_* identifies b^*Rb_*M[0] with M[0] by
precisely the transported derived counit. Transport the first vertex along this
isomorphism, then apply the actual triangulated composite i^*Rj_*.
5. Right-derived left t-exactness gives both lower bounds zero. The standard
zero/isomorphism criterion for distinguished triangles gives the final equivalence.
All intermediate categorical lemmas used here are proved as private lemmas in this
module; there are no additional assumed statements.
-/
theorem closed_unit_triangle
    {W V Y H Z : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]
    (j : V ⟶ Y) (b : W ⟶ V) [IsOpenImmersion j] [IsOpenImmersion b]
    (h : H ⟶ V) [IsClosedImmersion h] [IsReduced H]
    (_hcomplement : Set.range h = (Set.range b)ᶜ)
    (i : Z ⟶ Y) [IsClosedImmersion i] :
    ∃ c : directImage Λ b ⋙ (CondensedRing.upperStar Λ b).mapDerivedCategory ≅
        DerivedCategory.singleFunctor
          (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) 0,
      (∀ M, c.hom.app M =
        (leftDerivedUpperStarIsoMapDerivedCategory Λ b).inv.app
            ((directImage Λ b).obj M) ≫
          (derivedUpperStarLowerStarAdjunction Λ b).counit.app
            ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
      ∃ (a : extensionImage Λ j b ⋙ moduleObjectDerivedPullback Λ i ⟶
          directImage Λ b ⋙ image Λ j i)
        (δ : directImage Λ b ⋙ moduleObjectDerivedPullback Λ h ⋙
            moduleObjectDerivedPushforward Λ h ⋙ image Λ j i ⟶
          (extensionImage Λ j b ⋙ moduleObjectDerivedPullback Λ i) ⋙
            shiftFunctor _ (1 : ℤ)),
        (∀ M, a.app M = (image Λ j i).map
          ((CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategory.map (c.inv.app M) ≫
            (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ b).counit.app
              ((directImage Λ b).obj M))) ∧
        (∀ M, Triangle.mk (a.app M)
          ((image Λ j i).map
            ((derivedUpperStarLowerStarAdjunction Λ h).unit.app
              ((directImage Λ b).obj M))) (δ.app M) ∈ distTriang _) ∧
        (∀ M, (∃ n : ℤ, ((directImage Λ b).obj M).IsGE n) ∧
          (∃ n : ℤ, ((extensionImage Λ j b).obj M).IsGE n)) ∧
        (∀ M, IsZero ((moduleObjectDerivedPullback Λ i).obj
            ((extensionImage Λ j b).obj M)) ↔
          IsIso ((image Λ j i).map
            ((derivedUpperStarLowerStarAdjunction Λ h).unit.app
              ((directImage Λ b).obj M)))) := by
  classical
  have : IsNoetherian Y := ⟨⟩
  have : TopologicalSpace.NoetherianSpace V :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion j
  have : QuasiCompact b := inferInstance
  have hcomp : Set.range b = (Set.range h)ᶜ := by
    rw [_hcomplement, compl_compl]
  obtain ⟨hex, hr⟩ := condensed_open_closed_recollement Λ h b hcomp
  let := hex
  have hfull : (CondensedRing.lowerStar Λ h).Full := hr.2.2.2.2.2.2.2.2.2.1
  have hfaith : (CondensedRing.lowerStar Λ h).Faithful := hr.2.2.2.2.2.2.2.2.2.2.1
  clear hr
  have hkinj : (CondensedRing.lowerStar Λ h).PreservesKInjectiveComplexes :=
    (CondensedRing.upperStarLowerStarAdjunction Λ h).preservesKInjectiveComplexes
  have htQ := (module_derived_functors_exact_and_comparison_shifts Λ h).1
  let J := (CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategory
  let P := (CondensedRing.upperStar Λ b).mapDerivedCategory
  let Q := moduleObjectDerivedPullback Λ h
  let I := moduleObjectDerivedPushforward Λ h
  let a₀ := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ b
  let d := derivedUpperStarLowerStarAdjunction Λ h
  have hu : IsIso (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ b).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have hau : IsIso a₀.unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have hdc : IsIso d.counit := Adjunction.counit_isIso_of_R_fully_faithful _
  let e := leftDerivedUpperStarIsoMapDerivedCategory Λ b
  let ob := (derivedUpperStarLowerStarAdjunction Λ b).ofNatIsoLeft e
  have hoc : IsIso ob.counit :=
    (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨a₀, ob⟩).1 hau
  let c : directImage Λ b ⋙ P ≅ DerivedCategory.singleFunctor _ 0 :=
    asIso (Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0) ob.counit)
  have hz : ∀ M, IsZero (Q.obj (J.obj M)) := by
    intro M
    apply IsZero.of_iso _ ((leftDerivedUpperStarIsoMapDerivedCategory Λ h).app (J.obj M))
    apply (CondensedRing.upperStar Λ h).isZero_mapDerivedCategory_obj
    intro n
    exact (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ b h
      (by rw [_hcomplement]; exact disjoint_compl_right) _).of_iso
        ((CondensedRing.upperStar Λ h).mapIso
          (((CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategoryHomologyFunctorIso
            n).symm.app M))
  have hd : ∀ K, IsZero (P.obj K) → IsZero (Q.obj K) → IsZero K := by
    intro K hp hq
    apply (DerivedCategory.isZero_iff K).2
    intro n
    apply CondensedRing.isZero_of_isZero_upperStar_of_isCompl Λ h b
      (by rw [_hcomplement]; exact isCompl_compl.symm)
    · have hz := (DerivedCategory.homologyFunctor _ n).map_isZero
        (hq.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ h).app K).symm)
      exact hz.of_iso
        (((CondensedRing.upperStar Λ h).mapDerivedCategoryHomologyFunctorIso n).app K)
    · exact (((DerivedCategory.homologyFunctor _ n).map_isZero hp).of_iso
        (((CondensedRing.upperStar Λ b).mapDerivedCategoryHomologyFunctorIso n).app K))
  obtain ⟨δ₀, hδ₀⟩ := natural_triangle J P Q I a₀ d
    a₀.fullyFaithfulLOfIsIsoUnit hz (open_essImage J P Q a₀ hz hd)
  refine ⟨c, ?_, ?_⟩
  · intro M
    rfl
  · let S := DerivedCategory.singleFunctor
        (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) 0
    let F := moduleObjectDerivedPushforward Λ j ⋙ moduleObjectDerivedPullback Λ i
    have htj := (module_derived_functors_exact_and_comparison_shifts Λ j).2.1
    have hti := (module_derived_functors_exact_and_comparison_shifts Λ i).1
    have hF : F.IsTriangulated := inferInstance
    let av : S ⋙ J ⟶ directImage Λ b :=
      Functor.whiskerRight c.inv J ≫ Functor.whiskerLeft (directImage Λ b) a₀.counit
    let dv : directImage Λ b ⋙ Q ⋙ I ⟶ (S ⋙ J) ⋙ shiftFunctor _ (1 : ℤ) :=
      Functor.whiskerLeft (directImage Λ b) δ₀ ≫
        Functor.whiskerRight (Functor.whiskerRight c.hom J) (shiftFunctor _ (1 : ℤ))
    let a : (S ⋙ J) ⋙ F ⟶ directImage Λ b ⋙ F := Functor.whiskerRight av F
    let δ : directImage Λ b ⋙ Q ⋙ I ⋙ F ⟶
        ((S ⋙ J) ⋙ F) ⋙ shiftFunctor _ (1 : ℤ) :=
      Functor.whiskerRight dv F ≫ Functor.whiskerLeft (S ⋙ J) (F.commShiftIso (1 : ℤ)).hom
    have hv (M) : Triangle.mk (av.app M) (d.unit.app ((directImage Λ b).obj M))
        (dv.app M) ∈ distTriang _ := by
      exact change_first _ (hδ₀ ((directImage Λ b).obj M)) (J.mapIso (c.app M)).symm
    have htriangle (M) : Triangle.mk (a.app M)
        (F.map (d.unit.app ((directImage Λ b).obj M))) (δ.app M) ∈ distTriang _ := by
      change F.mapTriangle.obj
        (Triangle.mk (av.app M) (d.unit.app ((directImage Λ b).obj M)) (dv.app M))
          ∈ distTriang _
      exact F.map_distinguished _ (hv M)
    refine ⟨a, δ, ?_, ?_, ?_, ?_⟩
    · intro M
      rfl
    · exact htriangle
    · intro M
      constructor
      · exact ⟨0, (CondensedRing.lowerStar Λ b).isGE_rightDerivedFunctor_obj_singleFunctor M⟩
      · let N := (CondensedRing.openImmersionLowerShriek Λ b).obj M
        let eb := ((CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategorySingleFunctor
          0).app M
        let ej := (moduleObjectDerivedPushforward Λ j).mapIso eb
        refine ⟨0, ?_⟩
        have hn := (CondensedRing.lowerStar Λ j).isGE_rightDerivedFunctor_obj_singleFunctor N
        exact isGE_of_iso ej hn
    · intro M
      exact Triangle.isZero₁_iff_isIso₂ _ (htriangle M)

end AlgebraicGeometry.ProEtale.OpenSquareClosedUnit
