module

public import Sheaf.CategoryTheory.DerivedExtEvaluation
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleGrothendieckAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
import WeilConjectures.Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # The canonical Ext and derived-sections presentations of etale cohomology

Source: Stacks Project, Cohomology on Sites, Tags 03FD and 01FT.
(blueprint: def-weil-pbc-etale-cohomology-presentation).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
noncomputable section
set_option autoImplicit false
attribute [local instance 2000] CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal
  HasSmallSiteSheafify.hasSheafify IsGrothendieckAbelian.hasExt
  HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat
  Scheme.enoughInjectives_sheaf_smallEtaleTopology_addCommGrpCat
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_unit_single {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives D] [HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (M : C) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      R.rightDerivedFunctor.map ((L.mapDerivedCategorySingleFunctor 0).hom.app M) =
    (DerivedCategory.singleFunctor C 0).map (adj.unit.app M) ≫
      R.rightDerivedSingleUnit (L.obj M) := by
  let K := (CochainComplex.singleFunctor C 0).obj M
  let j := (L.mapCochainComplexSingleFunctor 0).hom.app M
  have hu := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient C (.up ℤ)).obj K)
  have hf : L.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      L.mapDerivedCategoryFactors.hom.app K := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
    repeat erw [CategoryTheory.Functor.map_id]
    repeat erw [Category.comp_id]
    repeat erw [Category.id_comp]
  have hs : (L.mapDerivedCategorySingleFunctor 0).hom.app M =
      L.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map j := by
    rw [← cancel_epi (L.mapDerivedCategoryFactors.inv.app K)]
    simpa only [K, j, CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app_assoc] using
      L.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M
  rw [hf] at hu
  rw [hs, Functor.map_comp, ← Category.assoc]
  erw [hu]
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  have hn := R.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient D (.up ℤ)).map j)
  dsimp only [Functor.comp_map] at hn
  erw [Category.assoc, ← hn]
  change DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map j) ≫ _ = _
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hc : (adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
      (R.mapHomologicalComplex (.up ℤ)).map j =
    (CochainComplex.singleFunctor C 0).map (adj.unit.app M) ≫
      (R.mapCochainComplexSingleFunctor 0).inv.app (L.obj M) := by
    apply HomologicalComplex.from_single_hom_ext
    dsimp [K, j, Functor.mapCochainComplexSingleFunctor]
    simp only [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    suffices h : adj.unit.app M ≫ R.map (𝟙 (L.obj M)) = adj.unit.app M by
      convert h using 1 <;>
        simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
          CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single,
          Functor.mapHomologicalComplex_map_f,
          HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
          Functor.id_obj, Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id,
          eqToIso_refl, eqToHom_refl, Iso.refl_hom, Iso.refl_inv,
          Category.id_comp, if_true, Functor.mapHomologicalComplex_obj_X]
      all_goals exact h
    erw [R.map_id, Category.comp_id]
  rw [hc, DerivedCategory.Q.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_unit_single_homology {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives D] [HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R]
    (adj : L ⊣ R) (M : C) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app M ≫
      (DerivedCategory.homologyFunctor C 0).map
        (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
            ((DerivedCategory.singleFunctor C 0).obj M) ≫
          R.rightDerivedFunctor.map ((L.mapDerivedCategorySingleFunctor 0).hom.app M)) =
    adj.unit.app M ≫
      (R.homologyRightDerivedFunctorObjSingleFunctorIso (L.obj M) 0 ≪≫
        R.rightDerivedZeroIsoSelf.app (L.obj M)).inv := by
  rw [← cancel_mono
    (R.homologyRightDerivedFunctorObjSingleFunctorIso (L.obj M) 0 ≪≫
      R.rightDerivedZeroIsoSelf.app (L.obj M)).hom]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [derived_unit_single, Functor.map_comp, Category.assoc,
    R.rightDerivedSingleUnit_zero]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.naturality
    (adj.unit.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  erw [hn]
  erw [Iso.inv_hom_id_app_assoc]

/-- Evaluation from the lifted integer object is bijective under an exact adjunction. -/
private theorem derived_ext_evaluation_bijective {D : Type*} [Category* D]
    [Abelian D] [HasDerivedCategory D] [HasExt.{u + 1} D]
    [EnoughInjectives D] [HasKInjectiveResolutions D]
    {L : AddCommGrpCat.{u + 1} ⥤ D} {R : D ⥤ AddCommGrpCat.{u + 1}}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] (adj : L ⊣ R) (F : D) (q : ℕ) :
    Function.Bijective (derivedExtEvaluation R
      (L.obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q
      (adj.unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (ULift.up 1))) := by
  let P := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let B := (DerivedCategory.singleFunctor _ 0).obj F
  let eL := (L.mapDerivedCategorySingleFunctor 0).app P
  let eS := (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).mapIso
      ((R.rightDerivedFunctor.commShiftIso (q : ℤ)).app B) ≪≫
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).shiftIso
      (q : ℤ) 0 (q : ℤ) (add_zero (q : ℤ))).app (R.rightDerivedFunctor.obj B)
  let eQ := (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).mapIso
    (R.rightDerivedFunctor.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F))
  have hx (x : Ext (L.obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q) :
      (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{u + 1} 0).inv.app P ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
            (eL.hom ≫ Ext.homEquiv x)) =
      adj.unit.app P ≫
        (R.homologyRightDerivedFunctorObjSingleFunctorIso (L.obj P) 0 ≪≫
          R.rightDerivedZeroIsoSelf.app (L.obj P)).inv ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (R.rightDerivedFunctor.map (Ext.homEquiv x)) := by
    calc
      _ = ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          AddCommGrpCat.{u + 1} 0).inv.app P ≫
            (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
              (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
                  ((DerivedCategory.singleFunctor _ 0).obj P) ≫
                R.rightDerivedFunctor.map eL.hom)) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
            (R.rightDerivedFunctor.map (Ext.homEquiv x)) := by
        simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
      _ = _ := by
        erw [derived_unit_single_homology adj P]
        rw [Category.assoc]
  let H := (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).obj
    (R.rightDerivedFunctor.obj (B⟦(q : ℤ)⟧))
  have hEval : Function.Bijective (fun f : P ⟶ H ↦ f (ULift.up 1)) := by
    have h : (fun f : P ⟶ H ↦ f (ULift.up 1)) =
        (AddCommGrpCat.uliftZMultiplesAddEquiv H : (P ⟶ H) → H) := by
      funext f
      symm
      change (uliftZMultiplesHom H).symm f.hom = f (ULift.up 1)
      simp only [uliftZMultiplesHom_symm_apply]
      rfl
    rw [h]
    exact (AddCommGrpCat.uliftZMultiplesAddEquiv H).bijective
  have hExt : Function.Bijective
      (Ext.homEquiv : Ext (L.obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q →
        ((DerivedCategory.singleFunctor _ 0).obj (L.obj P) ⟶ B⟦(q : ℤ)⟧)) :=
    Ext.homEquiv.bijective
  have hPre : Function.Bijective (fun t :
      (DerivedCategory.singleFunctor _ 0).obj (L.obj P) ⟶ B⟦(q : ℤ)⟧ ↦ eL.hom ≫ t) := by
    constructor
    · intro a b h
      exact (cancel_epi eL.hom).mp h
    · intro a
      exact ⟨eL.inv ≫ a, by simp only [Iso.hom_inv_id_assoc]⟩
  have hAdj := (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv
    ((DerivedCategory.singleFunctor _ 0).obj P) (B⟦(q : ℤ)⟧)).bijective
  have hHom := DerivedCategory.bijective_singleFunctorCompHomologyFunctorIso_inv_app_comp
    P (R.rightDerivedFunctor.obj (B⟦(q : ℤ)⟧))
  let f := fun x : Ext (L.obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q ↦ eQ.hom (eS.hom
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso
        AddCommGrpCat.{u + 1} 0).inv.app P ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
          (eL.hom ≫ Ext.homEquiv x))) (ULift.up 1)))
  have hf : Function.Bijective f := by
    exact (ConcreteCategory.bijective_of_isIso eQ.hom).comp
      ((ConcreteCategory.bijective_of_isIso eS.hom).comp
        (hEval.comp (hHom.comp (hAdj.comp (hPre.comp hExt)))))
  have he (x : Ext (L.obj P) F q) :
      f x = derivedExtEvaluation R (L.obj P) F q (adj.unit.app P (ULift.up 1)) x := by
    dsimp only [f]
    rw [hx x]
    simp only [derivedExtEvaluation, eQ, eS,
      Functor.mapIso_hom, Functor.map_comp]
    rfl
  have h : f = derivedExtEvaluation R (L.obj P) F q (adj.unit.app P (ULift.up 1)) := funext he
  rw [← h]
  exact hf


attribute [local irreducible] derivedExtEvaluation

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate the derived morphism representing an Ext class at the integer generator.
All functors, units and shift comparisons are the recorded derived constructions.
Source: Stacks Project, Tags 03FD and 01FT
(blueprint: def-weil-pbc-etale-cohomology-presentation). -/
def sheafHToDerived {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H F q) :
    (cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)) :=
  derivedExtEvaluation.{u, u + 2, u + 1, u + 1}
    (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q
    ((constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (ULift.up 1)) x
attribute [local irreducible] sheafHToDerived

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Additivity of evaluation of the represented cohomology class.
Source: Stacks Project, Tags 03FD and 01FT
(blueprint: def-weil-pbc-etale-cohomology-presentation).

Proof: Ext.homAddEquiv preserves sums. The right derived functor, its homology
functors, the degree-zero and shift comparisons, and evaluation at the fixed generator
are additive. Their displayed composite therefore preserves sums. -/
theorem sheafHToDerived_add {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x y : Sheaf.H F q) :
    sheafHToDerived F q (x + y) = sheafHToDerived F q x + sheafHToDerived F q y := by
  simp only [sheafHToDerived, derivedExtEvaluation]
  simp only [← Ext.homAddEquiv_apply, map_add, Functor.map_add,
    Preadditive.add_comp, AddCommGrpCat.hom_add_apply]

/-- The Ext-to-derived evaluation comparison is bijective in every degree.
Source: Stacks Project, Tags 03FD and 01FT
(blueprint: def-weil-pbc-etale-cohomology-presentation).

Proof: resolve F by injective abelian sheaves. The constant-integer adjunction
identifies Hom from the integer sheaf with global sections naturally. Apply this
identification in each degree of the resolution: its cohomology is Ext on the
source and derived global sections on the target. The identity generator evaluates
this very identification, including in degree zero. Thus the displayed map is
bijective. This argument applies also to the empty scheme. -/
theorem sheafHToDerived_bijective {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (sheafHToDerived F q) := by
  unfold sheafHToDerived
  exact derived_ext_evaluation_bijective
    (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}) F q

/-- The canonical additive comparison of the two cohomology presentations.
Its inverse is determined by the proved bijectivity of the explicit evaluation.
Source: Stacks Project, Tags 03FD and 01FT
(blueprint: def-weil-pbc-etale-cohomology-presentation). -/
def sheafHDerivedEquiv {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H F q ≃+
      (cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)) :=
  { Equiv.ofBijective (sheafHToDerived F q) (sheafHToDerived_bijective F q) with
    map_add' := sheafHToDerived_add F q }

end
end AlgebraicGeometry.Etale
