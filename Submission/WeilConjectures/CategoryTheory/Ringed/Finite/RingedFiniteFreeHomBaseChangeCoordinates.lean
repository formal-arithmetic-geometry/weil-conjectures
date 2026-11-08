/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
public import Submission.WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Submission.WeilConjectures.Algebra.Homology.IndFiniteFree.IndFiniteFreeScalarModel
import all Submission.WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-! # Finite-free coordinates for the scalar-Hom comparison

Source: Stacks Project, Tags 08J9 and 08JA.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace CategoryTheory

namespace FiniteFreeLocalizationProof

private def adjunction {A B D E : Type*} [Category A] [Category B]
    [Category D] [Category E] {G : A ⥤ B} {F : B ⥤ A}
    (adj : G ⊣ F) (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (Q' : B ⥤ E) (W' : MorphismProperty B) [Q'.IsLocalization W']
    (G' : D ⥤ E) (F' : E ⥤ D)
    (α : Q ⋙ G' ≅ G ⋙ Q') (χ : Q' ⋙ F' ≅ F ⋙ Q) : G' ⊣ F' := by
  let : CatCommSq G Q Q' G' := ⟨α.symm⟩
  let : CatCommSq F Q' Q F' := ⟨χ.symm⟩
  exact adj.localization Q W Q' W' G' F'

private theorem transpose {A B D E : Type*} [Category A] [Category B]
    [Category D] [Category E] {G : A ⥤ B} {F : B ⥤ A}
    (adj : G ⊣ F) (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (Q' : B ⥤ E) (W' : MorphismProperty B) [Q'.IsLocalization W']
    (G' : D ⥤ E) (F' : E ⥤ D)
    (α : Q ⋙ G' ≅ G ⋙ Q') (χ : Q' ⋙ F' ≅ F ⋙ Q)
    (X : A) (Y : B) (g : X ⟶ F.obj Y) :
    ((adjunction adj Q W Q' W' G' F' α χ).homEquiv (Q.obj X) (Q'.obj Y)).symm
      (Q.map g ≫ χ.inv.app Y) =
        α.hom.app X ≫ Q'.map ((adj.homEquiv X Y).symm g) := by
  dsimp only [adjunction]
  rw [Adjunction.homEquiv_counit, Adjunction.localization_counit_app]
  change G'.map (Q.map g ≫ χ.inv.app Y) ≫
    G'.map (χ.hom.app Y) ≫ α.hom.app (F.obj Y) ≫ Q'.map (adj.counit.app Y) = _
  rw [G'.map_comp]
  simp only [Category.assoc]
  rw [← G'.map_comp_assoc (χ.inv.app Y) (χ.hom.app Y),
    Iso.inv_hom_id_app, G'.map_id, Category.id_comp]
  have hn := α.hom.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← Q'.map_comp, Adjunction.homEquiv_counit]

private theorem unit {A B D E : Type*} [Category A] [Category B]
    [Category D] [Category E] {G : A ⥤ B} {F : B ⥤ A}
    (adj : G ⊣ F) (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (Q' : B ⥤ E) (W' : MorphismProperty B) [Q'.IsLocalization W']
    (G' : D ⥤ E) (F' : E ⥤ D)
    (α : Q ⋙ G' ≅ G ⋙ Q') (χ : Q' ⋙ F' ≅ F ⋙ Q) (X : A) :
    (adjunction adj Q W Q' W' G' F' α χ).unit.app (Q.obj X) =
      Q.map (adj.unit.app X) ≫ χ.inv.app (G.obj X) ≫ F'.map (α.inv.app X) := by
  let : CatCommSq G Q Q' G' := ⟨α.symm⟩
  let : CatCommSq F Q' Q F' := ⟨χ.symm⟩
  dsimp only [adjunction]
  exact adj.localization_unit_app Q W Q' W' G' F' X

end FiniteFreeLocalizationProof

namespace FiniteFreeClosedProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open WeilConjectures
variable {A B : Type*} [Category A] [Category B]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
  (AR : CoefficientClosedStructure H) (AS : CoefficientClosedStructure I)
  {T : A ⥤ B} {U : B ⥤ A} (δ : T ⊣ U)
  (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)
  [Preadditive B] (K : Type*) [Ring K] [Linear K B]

end FiniteFreeClosedProof

namespace RingedFiniteFreeCoordinatesProof
open SheafOfModules MonoidalCategory
universe u₀ v₀ r₀
variable {C : Type u₀} [Category.{v₀} C] [EssentiallySmall.{r₀} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r₀} RingCat.{r₀})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r₀}]
  [HasSheafify J AddCommGrpCat.{r₀}]
  {R S : Sheaf J CommRingCat.{r₀}}

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
  Abelian.hasFiniteBiproducts
attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private def regularTensorIso
    (M : SheafOfModules.{r₀} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (monoidalCategory R).tensorObj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M ≅ M :=
  tensorObjIsoSheafification _ M ≪≫
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit).app M

set_option maxHeartbeats 100000 in
-- Tensor sheafification comparisons require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem regularTensorIso_inv_apply
    (M : SheafOfModules.{r₀} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (regularTensorIso M).inv.val.app V x =
      (SheafOfModules.IndFiniteFree.tensorPresheafUnit
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M).app V
        ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have : IsIso adj.counit := by dsimp [adj]; infer_instance
  let e := (asIso adj.counit).app M
  have hc : e.inv.val = adj.unit.app M.val := by
    have he : e.inv = inv (adj.counit.app M) := NatIso.isIso_inv_app adj.counit M
    rw [he]
    change (SheafOfModules.forget _).map (inv (adj.counit.app M)) = _
    rw [Functor.map_inv]
    exact adj.inv_counit_map
  let a := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have hb : e.inv.val ≫ (a.map (λ_ M.val).inv).val =
      (λ_ M.val).inv ≫ adj.unit.app (_ ⊗ M.val) := by
    rw [hc]
    exact (adj.unit.naturality (λ_ M.val).inv).symm
  have hb' := congrArg (fun k ↦ k.app V x) hb
  change (tensorObjIsoSheafification
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M).inv.val.app V
      (((e.inv.val ≫ (a.map (λ_ M.val).inv).val).app V) x) = _
  rw [hb']
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def ordinaryBasisIso (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (M : scalarModules J R) :
    (⨁ fun _ : Fin d ↦ M) ≅ (scalarRestriction φ).obj (changeOfRings φ M) := by
  let U := unit (derivedChangeRingIndependentCoefficients J R)
  let G : scalarModules J R ⥤ scalarModules J R := tensorRight M
  have : PreservesColimitsOfSize.{r₀, r₀} (tensorLeft M) :=
    tensorLeft_preservesColimits_independentCoefficients R M
  let b : tensorLeft M ≅ G := NatIso.ofComponents (fun N ↦ β_ M N)
    (fun f ↦ BraidedCategory.braiding_naturality_right M f)
  have : PreservesColimitsOfSize.{r₀, r₀} G := preservesColimits_of_natIso b
  let i₁ : (⨁ fun _ : Fin d ↦ M) ≅ ∐ fun _ : Fin d ↦ M :=
    biproduct.isoCoproduct _
  let i₂ : (∐ fun _ : Fin d ↦ M) ≅ ∐ fun _ : ULift.{r₀} (Fin d) ↦ G.obj U :=
    Sigma.whiskerEquiv (Equiv.ulift : ULift.{r₀} (Fin d) ≃ Fin d).symm
      (fun _ ↦ regularTensorIso M)
  let i₃ : (∐ fun _ : ULift.{r₀} (Fin d) ↦ G.obj U) ≅
      G.obj (free (R := derivedChangeRingIndependentCoefficients J R)
        (ULift.{r₀} (Fin d))) :=
    (PreservesCoproduct.iso G (fun _ : ULift.{r₀} (Fin d) ↦ U)).symm
  let i₄ : G.obj (free (R := derivedChangeRingIndependentCoefficients J R)
      (ULift.{r₀} (Fin d))) ≅
      G.obj ((scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S))) :=
    G.mapIso e.symm
  let i₅ : G.obj ((scalarRestriction φ).obj
      (unit (derivedChangeRingIndependentCoefficients J S))) ≅
        (scalarRestriction φ).obj (changeOfRings φ M) :=
    (IndFiniteFree.exists_extensionTensorComparison φ M).choose
  exact i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅

set_option maxHeartbeats 100000 in
-- Tensor sheafification comparisons require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryBasisIso_ι (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (M : scalarModules J R) (i : Fin d) :
    biproduct.ι _ i ≫ (ordinaryBasisIso φ d e M).hom =
      (regularTensorIso M).inv ≫ ((ιFree (ULift.up i) ≫ e.inv) ▷ M) ≫
        (SheafOfModules.IndFiniteFree.exists_extensionTensorComparison φ M).choose.hom := by
  dsimp only [ordinaryBasisIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    PreservesCoproduct.inv_hom]
  simp only [biproduct.isoCoproduct_hom, biproduct.ι_desc_assoc]
  rw [Sigma.whiskerEquiv_hom, Sigma.ι_comp_map'_assoc,
    ι_comp_sigmaComparison_assoc]
  change (regularTensorIso M).inv ≫ ((ιFree (ULift.up i)) ▷ M) ≫ (e.inv ▷ M) ≫ _ = _
  rw [comp_whiskerRight, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryBasisIso_ι_apply (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (M : scalarModules J R) (i : Fin d) (V : Cᵒᵖ) (x : M.val.obj V) :
    (biproduct.ι _ i ≫ (ordinaryBasisIso φ d e M).hom).val.app V x =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
        (((ιFree (ULift.up i) ≫ e.inv).val.app V (1 : R.obj.obj V))
          ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) := by
  rw [ordinaryBasisIso_ι]
  change (IndFiniteFree.exists_extensionTensorComparison φ M).choose.hom.val.app V
    ((((ιFree (ULift.up i) ≫ e.inv) ▷ M).val.app V
      ((regularTensorIso M).inv.val.app V x))) = _
  rw [regularTensorIso_inv_apply]
  change (IndFiniteFree.exists_extensionTensorComparison φ M).choose.hom.val.app V
    ((((ιFree (ULift.up i) ≫ e.inv) ▷ M).val.app V
      (IndFiniteFree.pureTensor _ M V (show R.obj.obj V from 1) x))) = _
  rw [IndFiniteFree.pureTensor_whiskerRight]
  exact (IndFiniteFree.exists_extensionTensorComparison φ M).choose_spec V _ x

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev copies {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
    (d : ℕ) : D ⥤ D where
  obj X := ⨁ fun _ : Fin d ↦ X
  map f := biproduct.map (fun _ ↦ f)
  map_id X := by ext i j; simp
  map_comp f g := by ext i j; simp

private instance copies_additive {D : Type*} [Category D] [Preadditive D]
    [HasFiniteBiproducts D] (d : ℕ) : (copies (D := D) d).Additive where
  map_add := by
    intro X Y f g
    change biproduct.map (fun _ : Fin d ↦ f + g) =
      biproduct.map (fun _ : Fin d ↦ f) + biproduct.map (fun _ : Fin d ↦ g)
    apply biproduct.hom_ext'
    intro i
    rw [Preadditive.comp_add, biproduct.ι_map, biproduct.ι_map, biproduct.ι_map]
    simp only [Preadditive.add_comp]

private def complexCopiesIso {D : Type*} [Category D] [Abelian D]
    (d : ℕ) (F : CochainComplex D ℤ) :
    (⨁ fun _ : Fin d ↦ F) ≅ ((copies d).mapHomologicalComplex (.up ℤ)).obj F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (HomologicalComplex.eval D (.up ℤ) n).mapBiproduct (fun _ : Fin d ↦ F)) (by
      intro n m hnm
      change ((HomologicalComplex.eval D (.up ℤ) n).mapBiproduct _).hom ≫
        biproduct.map (fun _ : Fin d ↦ F.d n m) = _
      apply biproduct.hom_ext
      intro i
      simp only [Category.assoc, biproduct.map_π, Functor.mapBiproduct_hom]
      erw [biproduct.lift_π_assoc, biproduct.lift_π]
      exact (biproduct.π (fun _ : Fin d ↦ F) i).comm n m)

private theorem complexCopiesIso_ι_f {D : Type*} [Category D] [Abelian D]
    (d : ℕ) (F : CochainComplex D ℤ) (i : Fin d) (n : ℤ) :
    (biproduct.ι (fun _ : Fin d ↦ F) i ≫ (complexCopiesIso d F).hom).f n =
      biproduct.ι (fun _ : Fin d ↦ F.X n) i := by
  dsimp only [complexCopiesIso, HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  change (HomologicalComplex.eval D (.up ℤ) n).map (biproduct.ι _ i) ≫
    ((HomologicalComplex.eval D (.up ℤ) n).mapBiproduct _).hom = _
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, Functor.mapBiproduct_hom]
  erw [biproduct.lift_π]
  rw [← Functor.map_comp]
  change (HomologicalComplex.eval D (.up ℤ) n).map
    (biproduct.ι (fun _ : Fin d ↦ F) i ≫ biproduct.π _ j) =
      biproduct.ι (fun _ : Fin d ↦ F.X n) i ≫
        biproduct.π (fun _ : Fin d ↦ F.X n) j
  by_cases h : i = j
  · subst j
    simp only [biproduct.ι_π_self, Functor.map_id]
    rfl
  · simp only [biproduct.ι_π_ne _ h, Functor.map_zero]

private def complexCopies {D : Type*} [Category D] [Abelian D] (d : ℕ) :
    copies (D := CochainComplex D ℤ) d ≅ (copies d).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (complexCopiesIso d) (by
    intro F G f
    apply biproduct.hom_ext'
    intro i
    dsimp only [copies]
    rw [biproduct.ι_map_assoc]
    apply HomologicalComplex.hom_ext
    intro n
    simp only [HomologicalComplex.comp_f]
    change f.f n ≫ ((biproduct.ι (fun _ : Fin d ↦ G) i).f n ≫
        (complexCopiesIso d G).hom.f n) =
      (biproduct.ι (fun _ : Fin d ↦ F) i).f n ≫
        ((complexCopiesIso d F).hom.f n ≫ biproduct.map (fun _ ↦ f.f n))
    rw [← Category.assoc ((biproduct.ι (fun _ : Fin d ↦ F) i).f n)]
    have hF := complexCopiesIso_ι_f d F i n
    have hG := complexCopiesIso_ι_f d G i n
    dsimp only [HomologicalComplex.comp_f] at hF hG
    rw [hF, hG, biproduct.ι_map])

private def copiesComparison {D D' : Type*} [Category D] [Category D']
    [Preadditive D] [Preadditive D'] [HasFiniteBiproducts D] [HasFiniteBiproducts D']
    (F : D ⥤ D') [F.Additive] (d : ℕ) : copies d ⋙ F ≅ F ⋙ copies d :=
  NatIso.ofComponents (fun X ↦ F.mapBiproduct (fun _ : Fin d ↦ X)) (by
    intro X Y f
    dsimp only [Functor.comp_map, copies]
    apply (cancel_epi (F.mapBiproduct (fun _ : Fin d ↦ X)).inv).1
    apply biproduct.hom_ext'
    intro i
    simp only [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc]
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc]
    change F.map (biproduct.ι (fun _ : Fin d ↦ X) i) ≫
        F.map (biproduct.map (fun _ ↦ f)) ≫
        (F.mapBiproduct (fun _ : Fin d ↦ Y)).hom ≫ biproduct.π _ j =
      F.map (biproduct.ι (fun _ : Fin d ↦ X) i) ≫
        (F.mapBiproduct (fun _ : Fin d ↦ X)).hom ≫
        biproduct.map (fun _ ↦ F.map f) ≫ biproduct.π _ j
    simp only [Functor.mapBiproduct_hom, biproduct.map_π]
    erw [biproduct.lift_π, biproduct.lift_π_assoc]
    rw [← F.map_comp_assoc, ← F.map_comp]
    simp only [Category.assoc, biproduct.map_π, F.map_comp])

private def localizedBasis {D D' : Type*} [Category D] [Category D']
    [Preadditive D] [Preadditive D'] [HasFiniteBiproducts D] [HasFiniteBiproducts D']
    (Q : D ⥤ D') [Q.Additive] (W : MorphismProperty D) [Q.IsLocalization W]
    (d : ℕ) (F : D ⥤ D) (G : D' ⥤ D')
    (b : copies d ≅ F) (χ : Q ⋙ G ≅ F ⋙ Q) : copies d ≅ G :=
  Localization.liftNatIso Q W (Q ⋙ copies d) (Q ⋙ G) (copies d) G
    ((copiesComparison Q d).symm ≪≫ Functor.isoWhiskerRight b Q ≪≫ χ.symm)

universe w₁
variable [HasDerivedCategory.{w₁} (scalarModules J R)]
  [HasDerivedCategory.{w₁} (scalarModules J S)]

private def scalarModel (φ : R ⟶ S) :
    DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ :=
  (nonempty_derivedChangeOfRingsCochainModel φ).some

attribute [local irreducible] scalarModel

private def moduleBasisIso (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (M : scalarModules J R) :
    (copies d).obj M ≅ (scalarRestriction φ).obj (m.E.obj M) :=
  ordinaryBasisIso φ d e M ≪≫ (scalarRestriction φ).mapIso (eqToIso (m.obj_eq M).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleBasisIso_ι_apply (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (M : scalarModules J R) (i : Fin d) (V : Cᵒᵖ) (x : M.val.obj V) :
    (biproduct.ι _ i ≫ (moduleBasisIso φ d e m M).hom).val.app V x =
      IndFiniteFree.extensionPure m M V
        ((ιFree (ULift.up i) ≫ e.inv).val.app V (1 : R.obj.obj V)) x := by
  change (eqToHom (m.obj_eq M).symm).val.app V
    ((biproduct.ι _ i ≫ (ordinaryBasisIso φ d e M).hom).val.app V x) = _
  rw [ordinaryBasisIso_ι_apply]
  rfl

attribute [local irreducible] ordinaryBasisIso regularTensorIso moduleBasisIso

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def moduleBasis (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ) :
    copies d ≅ m.E ⋙ scalarRestriction φ :=
  NatIso.ofComponents (moduleBasisIso φ d e m) (by
    intro M N f
    dsimp only [copies, Functor.comp_map]
    apply biproduct.hom_ext'
    intro i
    change biproduct.ι _ i ≫ biproduct.map (fun _ ↦ f) ≫ _ = _
    rw [biproduct.ι_map_assoc]
    apply SheafOfModules.hom_ext
    ext V x
    change (biproduct.ι _ i ≫ (moduleBasisIso φ d e m N).hom).val.app V
      (f.val.app V x) =
      (m.E.map f).val.app V
        ((biproduct.ι _ i ≫ (moduleBasisIso φ d e m M).hom).val.app V x)
    rw [moduleBasisIso_ι_apply, moduleBasisIso_ι_apply]
    exact (IndFiniteFree.extensionPure_naturality m f V _ x).symm)

private def modelIso (φ : R ⟶ S)
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (E : scalarModules J R ⥤ scalarModules J S)
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm) : E ≅ m.E :=
  NatIso.ofComponents (fun M ↦ eqToIso ((h M).trans (m.obj_eq M).symm)) (by
    intro M N f
    rw [hm, m.map_eq]
    simp)

attribute [local irreducible] modelIso

private def chainBasis (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ) :
    copies d ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
      (scalarRestriction φ).mapHomologicalComplex (.up ℤ) :=
  complexCopies d ≪≫ NatIso.mapHomologicalComplex (moduleBasis φ d e m) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

attribute [local irreducible] chainBasis moduleBasis

private def chainBasisE (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive] (eE : E ≅ m.E) :
    copies d ≅ E.mapHomologicalComplex (.up ℤ) ⋙
      (scalarRestriction φ).mapHomologicalComplex (.up ℤ) :=
  chainBasis φ d e m ≪≫ Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex eE.symm (.up ℤ)) _

private def restrictionFactors (φ : R ⟶ S)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (T : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ (T ⋙ scalarDerivedRestriction.{u₀, v₀, r₀, w₁} φ) ≅
      (E.mapHomologicalComplex (.up ℤ) ⋙
        (scalarRestriction φ).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ε _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarRestrictionComparison φ) ≪≫
    (Functor.associator _ _ _).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] scalarDerivedRestriction scalarRestrictionComparison
  FiniteFreeLocalizationProof.adjunction

private def derivedAdjunction (φ : R ⟶ S)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (T : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (adj : E ⊣ scalarRestriction φ) : T ⊣ scalarDerivedRestriction φ :=
  FiniteFreeLocalizationProof.adjunction (adj.mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) T
    (scalarDerivedRestriction φ) ε (scalarRestrictionComparison φ)

attribute [local irreducible] derivedAdjunction

attribute [local irreducible] chainBasisE localizedBasis

end RingedFiniteFreeCoordinatesProof

private instance sectionLinearIndependent {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (S : Sheaf J CommRingCat.{r}) :
    Linear (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
      (SheafOfModules.scalarModules J S) :=
  SheafOfModules.homLinear S.obj
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).property

private instance derivedSectionLinear {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (S : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)] :
    Linear (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
      (DerivedCategory (SheafOfModules.scalarModules J S)) :=
  DerivedCategory.instLinear _ _

private instance sectionQLinear {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (S : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)] :
    Functor.Linear (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
      (DerivedCategory.Q : CochainComplex (SheafOfModules.scalarModules J S) ℤ ⥤ _) := by
  unfold derivedSectionLinear
  infer_instance

attribute [local irreducible] derivedSectionLinear

section Site
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

namespace FiniteFreeScalarProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SheafOfModules MonoidalCategory WeilConjectures
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
  derivedInternalHomOfUniverses SheafOfModules.homLinear SheafOfModules.homModule

private abbrev sections (S : Sheaf J CommRingCat.{max c v r}) :=
  RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat)

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem smul_apply (M N : scalarModules J S) (f : M ⟶ N)
    (s : sections.{c, v, r} J S) (V : Cᵒᵖ) (x : M.val.obj V) :
    (s • f).val.app V x = (show S.obj.obj V from s.val V) • f.val.app V x := by
  unfold sectionLinearIndependent SheafOfModules.homLinear SheafOfModules.homModule
  rfl

attribute [local irreducible] coefficientTotalTensor DerivedCategory.instLinear
  CoefficientClosedStructure.tensor

end FiniteFreeScalarProof

/-- The basis components of a finite-free scalar-extension isomorphism, specified
on every K-flat representative. The degreewise map is multiplication by the actual
basis section, followed by sheafification; the localization square fixes its derived class.
Source: Stacks Project, Tags 08J9 and 08JA.
(blueprint: lem-sf-ringed-finite-free-hom-coordinates). -/
def RingedFiniteFreeBasisCoordinates
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J R)]
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)]
    (d : ℕ) (e : (SheafOfModules.scalarRestriction φ).obj
      (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
      SheafOfModules.free
        (R := SheafOfModules.derivedChangeRingIndependentCoefficients J R)
        (ULift.{max c v r} (Fin d)))
    (E : SheafOfModules.scalarModules J R ⥤ SheafOfModules.scalarModules J S)
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    [E.Additive]
    (T : DerivedCategory (SheafOfModules.scalarModules J R) ⥤
      DerivedCategory (SheafOfModules.scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (X : DerivedCategory (SheafOfModules.scalarModules J R))
    (a : (⨁ fun _ : Fin d ↦ X) ≅ (SheafOfModules.scalarDerivedRestriction φ).obj
      (T.obj X)) : Prop :=
  ∀ (F : CochainComplex (SheafOfModules.scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F →
    ∀ (q : DerivedCategory.Q.obj F ≅ X) (j : Fin d),
    ∃ b : F ⟶ ((SheafOfModules.scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj F),
      (∀ (n : ℤ) (V : Cᵒᵖ) (x : (F.X n).val.obj V),
        (b.f n).val.app V x = ringedFiniteFreeScalarSection.{c, v, r} J φ E h (F.X n) V
          (((SheafOfModules.ιFree (ULift.up j) ≫ e.inv).val.app V)
            (show R.obj.obj V from 1)) x) ∧
      q.inv ≫ DerivedCategory.Q.map b ≫
          (SheafOfModules.scalarRestrictionComparison φ).inv.app
            ((E.mapHomologicalComplex (.up ℤ)).obj F) =
        biproduct.ι _ j ≫ a.hom ≫
          (SheafOfModules.scalarDerivedRestriction φ).map (T.map q.inv ≫ ε.app F)

namespace FiniteFreeScalarProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SheafOfModules

end FiniteFreeScalarProof

attribute [-instance] sectionLinearIndependent derivedSectionLinear sectionQLinear

attribute [local irreducible] FiniteFreeLocalizationProof.adjunction
  derivedInternalHomOfUniverses WeilConjectures.CoefficientClosedStructure.tensor
  WeilConjectures.coefficientTotalTensor
  SheafOfModules.scalarDerivedRestriction SheafOfModules.scalarRestrictionComparison
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
  SheafOfModules.monoidalCategory SheafOfModules.tensorObjIsoSheafification
  WeilConjectures.CoefficientTensorModels.iso
  RingedFiniteFreeCoordinatesProof.derivedAdjunction
  RingedFiniteFreeCoordinatesProof.scalarModel RingedFiniteFreeCoordinatesProof.modelIso
  RingedFiniteFreeCoordinatesProof.chainBasisE
  RingedFiniteFreeCoordinatesProof.moduleBasisIso
  RingedFiniteFreeCoordinatesProof.localizedBasis
  RingedFiniteFreeCoordinatesProof.restrictionFactors
  ringedFiniteFreeScalarSection WeilConjectures.coefficientTensorGenerator
  RingedFiniteFreeBasisCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end Site
end CategoryTheory
