/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NL and R4
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData
import Sheaf.Paper.RingedCoefficientPullbackCoherence
import Sheaf.Paper.RingedCoefficientPullbackComparison
import Sheaf.Paper.RingedCoefficientPullbackShifts
import Sheaf.Paper.RingedCoefficientAssociatorShifts
import Sheaf.Paper.RingedCoefficientScalarUnits
import Sheaf.Paper.RingedCoefficientScalarShifts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift

/-! # Coefficient projection cocycles, obtained by taking mates

Source: Stacks Project, Cohomology on Sites, Tags 07A7 and 0E47
(blueprint: lem-pur-ringed-coefficient-projection-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have heq : Functor.whiskerLeft inj F.rightDerivedFunctorUnit =
      (Functor.leftUnitor G).inv ≫ Functor.whiskerRight E.unitIso.hom G ≫
        (Functor.associator E.functor E.inverse G).hom ≫
        Functor.whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (Functor.associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    have hn := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.leftUnitor_inv_app, hinv]
    dsimp only [G, E, inj] at hn ⊢
    simp only [Category.id_comp, Category.assoc]
    rw [← Category.assoc]
    erw [hn]
    erw [Category.comp_id]
    simp only [Functor.comp_map, Category.assoc]
    change _ = _ ≫ F.rightDerivedFunctor.map (E.functor.map (E.unit.app X)) ≫
      F.rightDerivedFunctor.map (E.counit.app (E.functor.obj X))
    rw [← Functor.map_comp]
    erw [E.functor_unit_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    dsimp only [G, E, inj]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  let J := E.inverse.obj (DerivedCategory.Qh.obj K)
  obtain ⟨f, hf⟩ := (J.property.map_bijective_of_isTriangulated DerivedCategory.Qh
    K).surjective
      (E.counitIso.inv.app (DerivedCategory.Qh.obj K))
  refine ⟨J, f, ?_⟩
  rw [Functor.comp_map, hf]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_adjunction_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R) :
    NatTrans.CommShift adj.mapDerivedCategoryRightDerivedAdjunction.unit ℤ := by
  have : NatTrans.CommShift R.rightDerivedFunctorUnit ℤ := canonical_unit_commShift R
  have hunit : NatTrans.CommShift (adj.mapHomologicalComplex (.up ℤ)).unit ℤ := by
    constructor
    intro n
    ext K i
    dsimp [Adjunction.mapHomologicalComplex]
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    simp only [HomologicalComplex.id_f, CochainComplex.shiftFunctor_obj_X', Category.id_comp,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
    erw [Category.comp_id]
  have : NatTrans.CommShift (adj.mapHomotopyCategory (.up ℤ)).unit ℤ := by
    have heq : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
        (adj.mapHomotopyCategory (.up ℤ)).unit =
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
          Functor.whiskerRight (adj.mapHomologicalComplex (.up ℤ)).unit
            (HomotopyCategory.quotient C (.up ℤ)) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ))
            (R.mapHomotopyCategoryFactors (.up ℤ)).inv ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (L.mapHomotopyCategoryFactors (.up ℤ)).inv
            (R.mapHomotopyCategory (.up ℤ)) ≫
          (Functor.associator _ _ _).hom := by
      ext K
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
        Adjunction.mapHomotopyCategory_unit_app_quotient, Category.id_comp]
      simp [Functor.mapHomotopyCategoryFactors]
    have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
        (adj.mapHomotopyCategory (.up ℤ)).unit) ℤ := by
      rw [heq]
      infer_instance
    exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
      (fun X ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective X).choose_spec ▸
        inferInstance⟩)
  let η := adj.mapDerivedCategoryRightDerivedAdjunction.unit
  have heq : Functor.whiskerLeft DerivedCategory.Qh η =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (adj.mapHomotopyCategory (.up ℤ)).unit DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (L.mapHomotopyCategory (.up ℤ)) R.rightDerivedFunctorUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryFactorsh.inv R.rightDerivedFunctor ≫
        (Functor.associator _ _ _).hom := by
    ext K
    apply (cancel_mono (R.rightDerivedFunctor.map
      (L.mapDerivedCategoryFactorsh.hom.app K))).1
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp,
      Category.assoc, ← R.rightDerivedFunctor.map_comp,
      L.mapDerivedCategoryFactorsh.inv_hom_id_app, R.rightDerivedFunctor.map_id,
      Category.comp_id]
    erw [Category.id_comp, Category.comp_id]
    exact (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit K
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Qh η) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)


variable {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := K) pX)
  (e : Comparisons g nY nX)

private theorem counit_natural (R : Sheaf J CommRingCat.{r})
    {M N : D K (g.rings.obj R)} (f : M ⟶ N) :
    (g.left R).map ((g.right R).map f) ≫ (g.adjunction R).counit.app N =
      (g.adjunction R).counit.app M ≫ f :=
  (g.adjunction R).counit.naturality f

private theorem comparison_transpose {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : D K (g.rings.obj R)) :
    (g.left S).map ((comparison g nY nX e a).app M) ≫
        (g.adjunction S).counit.app ((pX (g.rings.map a)).derived.obj M) =
      (e.derived a).hom.app ((g.right R).obj M) ≫
        (pX (g.rings.map a)).derived.map ((g.adjunction R).counit.app M) :=
  mateEquiv_counit (g.adjunction R) (g.adjunction S)
    (TwoSquare.mk _ _ _ _ (e.derived a).hom) M

private theorem laws_of_pullbackCoherence
    (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX))
    (h : PullbackCoherence g nY nX e uY uX) : Laws g nY nX e uY uX := by
  have hc {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
      (M : D K (g.rings.obj R)) :
      (nY.derived a b).hom.app ((g.right R).obj M) ≫
          (comparison g nY nX e (a ≫ b)).app M =
        (pY b).derived.map ((comparison g nY nX e a).app M) ≫
          (comparison g nY nX e b).app ((pX (g.rings.map a)).derived.obj M) ≫
          (g.right T).map ((targetAssociator g nX a b).hom.app M) := by
    apply ((g.adjunction T).homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [comparison_transpose]
    rw [counit_natural g T]
    rw [reassoc_of% (comparison_transpose g nY nX e b _)]
    have hn := (e.derived b).hom.naturality ((comparison g nY nX e a).app M)
    change (g.left T).map ((pY b).derived.map ((comparison g nY nX e a).app M)) ≫ _ =
      (e.derived b).hom.app _ ≫
        (pX (g.rings.map b)).derived.map
          ((g.left S).map ((comparison g nY nX e a).app M)) at hn
    rw [reassoc_of% hn]
    rw [← (pX (g.rings.map b)).derived.map_comp_assoc, comparison_transpose,
      (pX (g.rings.map b)).derived.map_comp]
    have ht := (targetAssociator g nX a b).hom.naturality
      ((g.adjunction R).counit.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ht
    simp only [Category.assoc]
    rw [ht]
    rw [← reassoc_of% (h.composition a b ((g.right R).obj M))]
  refine ⟨hc, ?_, ?_⟩
  · intro R M
    apply ((g.adjunction R).homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [counit_natural g R]
    rw [reassoc_of% (comparison_transpose g nY nX e (𝟙 R) M)]
    have ht := (eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_id R)) ≪≫
      uX.derived (g.rings.obj R)).hom.naturality ((g.adjunction R).counit.app M)
    dsimp only [Functor.id_map, Functor.comp_obj, Functor.id_obj] at ht
    rw [ht]
    rw [reassoc_of% (h.unit R ((g.right R).obj M))]
    rfl
  · intro R S T V a b a' b' hab M
    have hs {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
        (M : D K (g.rings.obj R)) :
        successive g nY nX e a b M = (comparison g nY nX e (a ≫ b)).app M := by
      dsimp only [successive]
      rw [← hc, Iso.inv_hom_id_app_assoc]
    rw [hs, hs]
    simpa only [eqToHom_map] using
      eqToHom_naturality
        (fun (a : R ⟶ V) ↦ (comparison g nY nX e a).app M) hab

private theorem shiftLaws_of_pullbackShifts
    (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX))
    (s : PullbackShifts g nY nX e uY uX) : Nonempty (ShiftLaws g nY nX e uY uX) := by
  let scalarY {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
      (pY a).derived.CommShift ℤ := s.scalarY a
  let scalarX {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S) :
      (pX a).derived.CommShift ℤ := s.scalarX a
  have hmate {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
      NatTrans.CommShift (comparison g nY nX e a) ℤ := by
    have hR : (g.adjunction R).CommShift ℤ :=
      .mk' _ _ (canonical_adjunction_unit_commShift (g.ordinaryAdjunction R))
    have hS : (g.adjunction S).CommShift ℤ :=
      .mk' _ _ (canonical_adjunction_unit_commShift (g.ordinaryAdjunction S))
    have := s.inverseScalar a
    dsimp only [comparison, mateEquiv, Equiv.coe_fn_mk]
    infer_instance
  exact ⟨{
    scalarY := s.scalarY
    scalarX := s.scalarX
    canonicalY := s.canonicalY
    canonicalX := s.canonicalX
    inverseScalar := s.inverseScalar
    mate := hmate
    associatorY := s.associatorY
    associatorX := s.associatorX
    unitY := s.unitY
    unitX := s.unitX }⟩

private theorem assertion_of_pullbacks [PreservesFiniteLimits uInv]
    (g : Geometry uInv uPush adj) :
    ∀ (pY : Scalars.{c, v, r} J) (pX : Scalars.{c, v, r} K)
      (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
        max c v (r + 1)} (J := J) pY)
      (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
        max c v (r + 1)} (J := K) pX),
      ∃ (e : Comparisons g nY nX) (uY : ScalarUnits (p := pY))
        (uX : ScalarUnits (p := pX)),
        Laws g nY nX e uY uX ∧ Nonempty (ShiftLaws g nY nX e uY uX) := by
  intro pY pX nY nX
  obtain ⟨e⟩ := coefficientPullbackComparisons g nY nX
  obtain ⟨sY⟩ := coefficientScalarShifts pY
  obtain ⟨sX⟩ := coefficientScalarShifts pX
  let scalarY {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
      (pY a).derived.CommShift ℤ := sY.scalar a
  let scalarX {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S) :
      (pX a).derived.CommShift ℤ := sX.scalar a
  obtain ⟨uY, huY⟩ := coefficientScalarUnits nY sY.canonical
  obtain ⟨uX, huX⟩ := coefficientScalarUnits nX sX.canonical
  have hc := coefficientPullbackCoherence g nY nX e uY uX
  let hs : PullbackShifts g nY nX e uY uX := {
    scalarY := scalarY
    scalarX := scalarX
    canonicalY := sY.canonical
    canonicalX := sX.canonical
    inverseScalar := coefficientPullbackShifts g nY nX e sY.canonical sX.canonical
    associatorY := coefficientAssociatorShifts nY sY.canonical
    associatorX := coefficientAssociatorShifts nX sX.canonical
    unitY := huY
    unitX := huX }
  exact ⟨e, uY, uX, laws_of_pullbackCoherence g nY nX e uY uX hc,
    shiftLaws_of_pullbackShifts g nY nX e uY uX hs⟩

/-- The ordinary unbounded coefficient projection cocycle, its identity and square
specializations, coefficient naturality, canonical shifts, and the same assertions
on strict inverse systems. The second conjunct is on the actual ringed sequence
sites: its ring objects include systemRing and their compatible maps systemMap.
Its morphisms are compared before evaluation or total inverse limit. Neither
flatness of ring maps nor invertibility of projection comparisons is required.

Source: Stacks Project, Cohomology on Sites, Tags 07A7, 0E47, 0D6D, 0D6E and 07A6
(blueprint: lem-pur-ringed-coefficient-projection-cocycle).

Proof:
1. Use coefficientPullbackComparisons for the insertion-normalized ordinary
inverse-image/scalar comparison and its derived K-flat representative equation.
2. Construct scalar multiplication units from the scalar extension/restriction
adjunction, then descend their ordinary isomorphisms by the universal left-derived
property. Choose coherent scalar shifts by the right-Kan-extension construction.
3. Prove scalar associator shifts by the universal lift of the termwise comparison
and its computation counit equation on K-flat resolutions. Use
coefficientPullbackCoherence for the balanced double-tensor composition square,
and multiplication-unit equation. Prove inverse-image comparison shifts directly
from the counit-normalized computation square and K-flat resolutions.
These are statements about inverse-image tensor maps, before taking mates.
4. The defining mate formula transposes comparison under the target-coefficient
geometric adjunction to the inverse-image/scalar comparison followed by scalar
extension of the source-coefficient counit.
5. Transpose both sides of the cocycle through that adjunction bijection. Expand
by the mate/counit equation, counit naturality, naturality of the inverse-image
comparison and of the balanced target associator, and scalar functoriality.
The left comparison square of step 3 identifies the resulting words.
6. For identity coefficients, the same transposition and the left unit equation
give the multiplication-unit law. Cancel balanced source associators to identify
each successive word with the single comparison for its composite. For a commuting
square, eqToHom_naturality for that single comparison gives the desired equality.
7. The canonical right-derived unit commutes with shifts, as can be checked on
the K-injective localization equivalence. The termwise ordinary adjunction unit
also commutes with shifts. Their normalized factorization gives this property for
the canonical derived adjunction unit, hence for its adjunction and for mates.
Combine this with the left comparison shifts from step 3 to obtain ShiftLaws.
8. Apply this uniform argument on J,K and on the actual coefficient sequence
sites. This proves the system equations in their derived category before any
evaluation or inverse limit; equality detection by evaluation is not used. -/
theorem ringedCoefficientProjectionCocycle
    (J : GrothendieckTopology C) (K : GrothendieckTopology X) :
    Assertion.{c, v, r} J K ∧
      Assertion.{c, v, r} (WeilConjectures.coefficientSequenceTopology J)
        (WeilConjectures.coefficientSequenceTopology K) := by
  have h {C X : Type c} [Category.{v} C] [Category.{v} X]
      [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
      (J : GrothendieckTopology C) (K : GrothendieckTopology X) :
      Assertion.{c, v, r} J K := by
    intro uInv uPush adj hu g pY pX nY nX
    let := hu
    exact assertion_of_pullbacks g pY pX nY nX
  exact ⟨h J K, h _ _⟩

end SheafOfModules.RingedCoefficientProjection
