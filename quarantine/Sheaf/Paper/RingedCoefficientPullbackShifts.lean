/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Shift compatibility of normalized inverse-image coefficient comparisons
Source: Stacks Project, Tags 0D6D and 07A6
(blueprint: lem-pur-coefficient-pullback-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

private theorem shift_of_dense_computation
    {A B E : Type*} [Category A] [Category B] [Category E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] (G L : B ⥤ E)
    [G.CommShift ℤ] [L.CommShift ℤ] (F : A ⥤ E) [F.CommShift ℤ]
    (α : Q ⋙ L ⟶ F) [NatTrans.CommShift α ℤ] (t : G ⟶ L)
    [NatTrans.CommShift (whiskerLeft Q t ≫ α) ℤ]
    (dense : ∀ Y : B, ∃ (X : A) (_e : Q.obj X ≅ Y), IsIso (α.app X)) :
    NatTrans.CommShift t ℤ := by
  constructor
  intro n
  let s : shiftFunctor B n ⋙ G ⟶ L ⋙ shiftFunctor E n :=
    (G.commShiftIso n).hom ≫ whiskerRight t (shiftFunctor E n)
  let u : shiftFunctor B n ⋙ G ⟶ L ⋙ shiftFunctor E n :=
    whiskerLeft (shiftFunctor B n) t ≫ (L.commShiftIso n).hom
  have good (X : A) [IsIso (α.app X)] : s.app (Q.obj X) = u.app (Q.obj X) := by
    apply (cancel_mono ((shiftFunctor E n).mapIso (asIso (α.app X))).hom).1
    change s.app (Q.obj X) ≫ (α.app X)⟦n⟧' =
      u.app (Q.obj X) ≫ (α.app X)⟦n⟧'
    apply (cancel_epi (G.mapIso ((Q.commShiftIso n).app X)).hom).1
    change G.map ((Q.commShiftIso n).hom.app X) ≫ s.app (Q.obj X) ≫
      (α.app X)⟦n⟧' = G.map ((Q.commShiftIso n).hom.app X) ≫ u.app (Q.obj X) ≫
      (α.app X)⟦n⟧'
    have ht := NatTrans.shift_app_comm (whiskerLeft Q t ≫ α) n X
    have ha := NatTrans.shift_app_comm α n X
    simp only [NatTrans.comp_app, whiskerLeft_app, Functor.map_comp,
      Functor.commShiftIso_comp_hom_app, Category.assoc] at ht ha
    rw [← ha, ← t.naturality_assoc] at ht
    simpa only [s, u, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using ht
  ext Y
  obtain ⟨X, e, hX⟩ := dense Y
  let := hX
  have h := congrArg (fun f ↦ f ≫ (L ⋙ shiftFunctor E n).map e.hom) (good X)
  rw [← s.naturality, ← u.naturality] at h
  exact (cancel_epi (((shiftFunctor B n) ⋙ G).mapIso e).hom).1 h

private theorem complexComp_commShift
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom ℤ := by
  constructor
  intro n
  ext K i
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.commShiftIso_comp_hom_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

private def complexCounit
    {A : Type c} [Category.{v} A] [EssentiallySmall.{r} A]
    {J0 : GrothendieckTopology A} {R S : Sheaf J0 CommRingCat.{r}} {a : R ⟶ S}
    (p : SuccessiveDerivedQuotient.Presentation.{c, v, r, max c v (r + 1)} a) :
    DerivedCategory.Q ⋙ p.derived ⟶
      p.ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso (Mod J0 R)).inv p.derived ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft (HomotopyCategory.quotient (Mod J0 R) (.up ℤ)) p.counit ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (p.ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft (p.ordinary.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso (Mod J0 S)).hom

private theorem complexCounit_app
    {A : Type c} [Category.{v} A] [EssentiallySmall.{r} A]
    {J0 : GrothendieckTopology A} {R S : Sheaf J0 CommRingCat.{r}} {a : R ⟶ S}
    (p : SuccessiveDerivedQuotient.Presentation.{c, v, r, max c v (r + 1)} a)
    (P : CochainComplex (Mod J0 R) ℤ) :
    (complexCounit p).app P = computation p P := by
  simp only [complexCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  rfl

private theorem complexCounit_shift
    {A : Type c} [Category.{v} A] [EssentiallySmall.{r} A]
    {J0 : GrothendieckTopology A} {R S : Sheaf J0 CommRingCat.{r}} {a : R ⟶ S}
    (p : SuccessiveDerivedQuotient.Presentation.{c, v, r, max c v (r + 1)} a)
    [p.derived.CommShift ℤ] [NatTrans.CommShift p.counit ℤ] :
    NatTrans.CommShift (complexCounit p) ℤ := by
  dsimp only [complexCounit]
  infer_instance

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := K) pX)
  (e : Comparisons g nY nX)
  [scalarY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (pY a).derived.CommShift ℤ]
  [scalarX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S),
    (pX a).derived.CommShift ℤ]
  (canonicalY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pY a).counit ℤ)
  (canonicalX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pX a).counit ℤ)

private def ordinarySquare {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    (pY a).ordinary.mapHomologicalComplex (.up ℤ) ⋙
        (g.inverse S).modules.mapHomologicalComplex (.up ℤ) ≅
      (g.inverse R).modules.mapHomologicalComplex (.up ℤ) ⋙
        (pX (g.rings.map a)).ordinary.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (e.ordinary a) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

private def targetCounit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    DerivedCategory.Q ⋙ (g.left R ⋙ (pX (g.rings.map a)).derived) ⟶
      ((g.inverse R).modules.mapHomologicalComplex (.up ℤ) ⋙
        (pX (g.rings.map a)).ordinary.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    whiskerRight (g.inverse R).modules.mapDerivedCategoryFactors.hom _ ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft ((g.inverse R).modules.mapHomologicalComplex (.up ℤ))
      (complexCounit (pX (g.rings.map a))) ≫
    (Functor.associator _ _ _).inv

private def sourceCounit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    DerivedCategory.Q ⋙ ((pY a).derived ⋙ g.left S) ⟶
      ((g.inverse R).modules.mapHomologicalComplex (.up ℤ) ⋙
        (pX (g.rings.map a)).ordinary.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    whiskerRight (complexCounit (pY a)) (g.left S) ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft ((pY a).ordinary.mapHomologicalComplex (.up ℤ))
      (g.inverse S).modules.mapDerivedCategoryFactors.hom ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (ordinarySquare g nY nX e a).hom _

include canonicalY canonicalX in
private theorem normalizedCounits_shift {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    NatTrans.CommShift (targetCounit g (pX := pX) a) ℤ ∧
      NatTrans.CommShift (sourceCounit g nY nX e a) ℤ := by
  have := canonicalY a
  have := canonicalX (g.rings.map a)
  have := complexCounit_shift (pY a)
  have := complexCounit_shift (pX (g.rings.map a))
  have := complexComp_commShift (e.ordinary a)
  have := complexComp_commShift
    (Iso.refl ((g.inverse R).modules ⋙ (pX (g.rings.map a)).ordinary))
  have : NatTrans.CommShift (ordinarySquare g nY nX e a).hom ℤ := by
    dsimp only [ordinarySquare, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  constructor
  · dsimp only [targetCounit]
    infer_instance
  · dsimp only [sourceCounit]
    infer_instance

omit scalarY scalarX in
private theorem ordinarySquare_app {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Mod J R) ℤ) :
    (ordinarySquare g nY nX e a).hom.app P =
      (NatTrans.mapHomologicalComplex (e.ordinary a).hom (.up ℤ)).app P := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

omit scalarY scalarX in
private theorem normalizedCounits_equation
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    whiskerLeft DerivedCategory.Q (e.derived a).hom ≫ targetCounit g (pX := pX) a =
      sourceCounit g nY nX e a := by
  let t := whiskerLeft DerivedCategory.Q (e.derived a).hom ≫
    targetCounit g (pX := pX) a
  let u := sourceCounit g nY nX e a
  have flat (P : CochainComplex (Mod J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients)
      (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
      t.app P = u.app P := by
    simpa only [t, u, sourceCounit, targetCounit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp, Category.comp_id, complexCounit_app, ordinarySquare_app,
      Category.assoc]
      using e.representative a P hP hf
  ext P₀
  obtain ⟨P, f, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
  have hf' (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P.X i) :=
    ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso R _).symm (hf i)
  let : IsIso (DerivedCategory.Q.map f) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
  apply (cancel_epi (((pY a).derived ⋙ g.left S).mapIso
    (asIso (DerivedCategory.Q.map f))).hom).1
  change (DerivedCategory.Q ⋙ ((pY a).derived ⋙ g.left S)).map f ≫ t.app P₀ =
    (DerivedCategory.Q ⋙ ((pY a).derived ⋙ g.left S)).map f ≫ u.app P₀
  rw [t.naturality, u.naturality, flat P hP hf']

include canonicalY canonicalX

/-- The normalized inverse-image scalar comparison respects counit-normalized shifts.
Source: Stacks Project, Cohomology on Sites, Tags 0D6D and 07A6
(blueprint: lem-pur-coefficient-pullback-shifts).

Proof: the ordinary comparison maps termwise to a shift-compatible comparison.
Compose it with the scalar computation counit and the exact inverse-image factors.
Both this source computation and the corresponding target computation commute with
shifts. Their equality after the derived comparison holds on K-flat representatives
by normalization, and on all complexes by naturality along a K-flat resolution.
On a flat-term K-flat representative the source computation is invertible; since
the derived comparison is an isomorphism, the target computation is invertible too.
The two computation shift equations can therefore be cancelled to prove the shift
square on these representatives. Every derived object has such a representative,
so naturality transports that square to all derived objects. -/
theorem coefficientPullbackShifts
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    NatTrans.CommShift (e.derived a).hom ℤ := by
  let α := targetCounit g (pX := pX) a
  let β := sourceCounit g nY nX e a
  obtain ⟨hα, hβ⟩ := normalizedCounits_shift g nY nX e canonicalY canonicalX a
  let := hα
  let := hβ
  have heq : whiskerLeft DerivedCategory.Q (e.derived a).hom ≫ α = β :=
    normalizedCounits_equation g nY nX e a
  have : NatTrans.CommShift
      (whiskerLeft DerivedCategory.Q (e.derived a).hom ≫ α) ℤ := by
    rw [heq]
    exact hβ
  apply shift_of_dense_computation DerivedCategory.Q _ _ _ α (e.derived a).hom
  intro M
  let P₀ := DerivedCategory.Q.objPreimage M
  obtain ⟨P, f, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
  have hf' (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P.X i) :=
    ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso R _).symm (hf i)
  let : IsIso (DerivedCategory.Q.map f) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
  refine ⟨P, asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso M, ?_⟩
  let := nY.computed a P hP hf'
  have : IsIso (computation (pY a) P) := by
    dsimp only [computation, derivedPullbackComplexComparison]
    infer_instance
  have hβP : IsIso (β.app P) := by
    dsimp only [β, sourceCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, complexCounit_app]
    infer_instance
  have hk : α.app P = (e.derived a).inv.app (DerivedCategory.Q.obj P) ≫ β.app P := by
    have h := NatTrans.congr_app heq P
    change (e.derived a).hom.app (DerivedCategory.Q.obj P) ≫ α.app P = β.app P at h
    rw [← h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [hk]
  infer_instance

end SheafOfModules.RingedCoefficientProjection
