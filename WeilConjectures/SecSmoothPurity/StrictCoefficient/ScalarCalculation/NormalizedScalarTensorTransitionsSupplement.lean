/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.StrictCoefficient.NormalizedCoefficientDiagramSupplement
public import WeilConjectures.SecSmoothPurity.StrictCoefficient.KappaCalculation.NormalizedKappaTransitionsSupplement
import all WeilConjectures.SecSmoothPurity.StrictCoefficient.KappaCalculation.NormalizedKappaTransitionsSupplement
import all WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
import all WeilConjectures.SecSmoothPurity.CoefficientComparisonsBalancedConstruction
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.SecSmoothPurity.CochainCompositeHom
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import all WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SecSmoothPurity.NormalizedScalarTensorTransitions

/-! # Normalized scalar tensor transitions

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL, and
Cohomology on Sites, Tag 07A4.
(blueprint: lem-pur-normalized-scalar-tensor-transitions).

Scalar tensor comparisons commute with arbitrary semilinear squares. Their
forward maps insert one and their inverse maps multiply the scalar coefficients.
-/

set_option Elab.async false
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules
open scoped TensorProduct ChangeOfRings
namespace CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation

attribute [local irreducible] scalarComp scalarUnit extensionAdjunction
attribute [local irreducible] generator
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]


open KappaCalculation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Auxiliary formula for scalar tensor transitions. Source: Stacks 03EK, 03EL, 07A4
(blueprint: lem-pur-normalized-scalar-tensor-transitions). -/
def tensorTransitionForward (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a)))
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q') :=
  (extend (B.map s)).map (tensorComparison (extensionPullback (B.map a)) (z a) P Q).hom ≫
    (tensorComparison (extensionPullback (B.map s)) (z s)
      ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q)).hom ≫
    tensorTotalMap (squareArrow B a b r s h P P' f) (squareArrow B a b r s h Q Q' g)

/-- Auxiliary formula for scalar tensor transitions. Source: Stacks 03EK, 03EL, 07A4
(blueprint: lem-pur-normalized-scalar-tensor-transitions). -/
def tensorTransitionInverse (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a)))
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q') :=
  (extend (B.map s)).map (tensorComparison (extensionPullback (B.map a)) (z a) P Q).inv ≫
    squareArrow B a b r s h (total P Q) (total P' Q')
      (tensorArrowFor B z r P Q P' Q' f g)

/-- Auxiliary formula for scalar tensor transitions. Source: Stacks 03EK, 03EL, 07A4
(blueprint: lem-pur-normalized-scalar-tensor-transitions). -/
def TensorTransitionValues (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a))) : Prop :=
  ∀ {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q')
    (p q n : ℤ) (hpq : p + q = n) (U : Cᵒᵖ) (v v' : (B.obj j).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((((tensorTransitionForward B z a b r s h P Q P' Q' f g).f n).val.app U
      (extensionTmul (B.map s) (((extend (B.map a)).obj (total P Q)).X n) U 1
        (extensionTmul (B.map a) ((total P Q).X n) U v (totalPure P Q p q n hpq U x y)))) =
      totalPure ((extend (B.map b)).obj P') ((extend (B.map b)).obj Q') p q n hpq U
        (extensionTmul (B.map b) (P'.X p) U ((B.map s).hom.app U v)
          ((semilinearSectionMap (B.map r) f p).hom.app U x))
        (extensionTmul (B.map b) (Q'.X q) U 1
          ((semilinearSectionMap (B.map r) g q).hom.app U y))) ∧
    ((((tensorTransitionInverse B z a b r s h P Q P' Q' f g).f n).val.app U
      (extensionTmul (B.map s)
        ((total ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q)).X n) U 1
        (totalPure ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q) p q n hpq U
          (extensionTmul (B.map a) (P.X p) U v x)
          (extensionTmul (B.map a) (Q.X q) U v' y)))) =
      extensionTmul (B.map b) ((total P' Q').X n) U
        ((B.map s).hom.app U v * (B.map s).hom.app U v')
        (totalPure P' Q' p q n hpq U
          ((semilinearSectionMap (B.map r) f p).hom.app U x)
          ((semilinearSectionMap (B.map r) g q).hom.app U y)))

@[no_expose] private noncomputable instance tensorCoproducts (R : Sheaf J CommRingCat.{w}) :
    HasCoproducts.{0} (Modules R) := inferInstance

@[no_expose] private noncomputable instance hasTensorTotal (R : Sheaf J CommRingCat.{w})
    (P Q : Complex R) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules R)) (.up ℤ) :=
  inferInstance

attribute [local irreducible] tensorComparison tensorTotalMap comparison

private theorem tensorComparison_eq {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) : tensorComparison f c P Q = comparison f c P Q := by
  unfold tensorComparison
  rfl

private theorem tensorTotalMap_eq {A : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex A} (f : P ⟶ P') (g : Q ⟶ Q') :
    tensorTotalMap f g = totalMap f g := by
  unfold tensorTotalMap
  rfl


@[no_expose] private def identityCoefficientSquare {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    CoefficientComparisonsBalanced.Square (𝟭 (Sheaf J (Type w))) :=
  { R0 := A, R1 := B, B0 := A, B1 := B, A0 := A, A1 := B
    iY := a, iX := a, j := a, phi0 := 𝟙 A, phi1 := 𝟙 B
    I0 := identityAlgebraicInverseImage A
    I1 := identityAlgebraicInverseImage B
    graph := by simp [identityAlgebraicInverseImage]
    commutes := by simp }

private theorem scalarConstruction {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    CoefficientComparisonsBalanced.ScalarTensorConstruction a :=
  (CoefficientComparisonsBalanced.coefficientComparisons_balanced_construction
    (identityCoefficientSquare a) (𝟭 _) Adjunction.id).2.1

private theorem scalarTensorFormulas {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (c : Comparison (extensionPullback a)) :
    CoefficientComparisonsBalanced.ScalarTensorFormulas a c.mu := by
  obtain ⟨m, hm, _⟩ := scalarConstruction a
  let c' : CanonicalRingedTensorComparisonOnSmallSites A B A (𝟭 _)
      (identityAlgebraicInverseImage A) a (extensionFunctor a) (fun _ ↦ rfl) :=
    { q := c.q, q_one := c.q_one, mu := c.mu,
      naturality := c.naturality, pure := c.pure }
  have h : c.mu = m := hm.2.2 c'
  exact h.symm ▸ hm.1


@[reassoc]
private theorem tensorComparison_ι {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) (p q n : ℤ) (h : p + q = n) :
    f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n h) ≫
        (tensorComparison f c P Q).hom.f n =
      (c.mu (P.X p) (Q.X q)).hom ≫
        CochainComplex.ιMapBifunctor ((pull f).obj P) ((pull f).obj Q)
          (curriedTensor (Modules S)) p q n h := by
  unfold tensorComparison
  exact CategoryTheory.CochainPullback.comparison_ι f c P Q p q n h

@[reassoc]
private theorem tensorComparison_inv_ι {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) (p q n : ℤ) (h : p + q = n) :
    CochainComplex.ιMapBifunctor ((pull f).obj P) ((pull f).obj Q)
        (curriedTensor (Modules S)) p q n h ≫ (tensorComparison f c P Q).inv.f n =
      (c.mu (P.X p) (Q.X q)).inv ≫
        f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n h) := by
  unfold tensorComparison comparison
  change _ ≫ (tensorPullbackTotal f.L c.mu c.naturality P Q).f n = _
  simp only [tensorPullbackTotal, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc]

@[reassoc]
private theorem totalMap_ι {R : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex R} (a : P ⟶ P') (b : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) :
    CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n h ≫
        (tensorTotalMap a b).f n =
      (a.f p ⊗ₘ b.f q) ≫
        CochainComplex.ιMapBifunctor P' Q' (curriedTensor (Modules R)) p q n h := by
  unfold tensorTotalMap
  change _ ≫ (HomologicalComplex.mapBifunctorMap a b _ _).f n = _
  simp only [HomologicalComplex.ι_mapBifunctorMap, curriedTensor_map_app,
    curriedTensor_obj_map, tensorHom_def, Category.assoc]



private theorem totalPure_smul {A : Sheaf J CommRingCat.{w}}
    (P Q : Complex A) (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (b : A.obj.obj U) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    totalPure P Q p q n h U (b • x) y = b • totalPure P Q p q n h U x y := by
  let t := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)).unit.app
      ((P.X p).val ⊗ (Q.X q).val)).app U
  have ht := t.hom.map_smul b (x ⊗ₜ[A.obj.obj U] y)
  change t ((b • x) ⊗ₜ[A.obj.obj U] y) = b • t (x ⊗ₜ[A.obj.obj U] y) at ht
  dsimp only [totalPure, ringedComparisonPure]
  erw [ht, map_smul, map_smul]

private theorem totalMap_pure {A : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex A} (a : P ⟶ P') (b : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((tensorTotalMap a b).f n).val.app U (totalPure P Q p q n h U x y) =
      totalPure P' Q' p q n h U ((a.f p).val.app U x) ((b.f q).val.app U y) := by
  have ht := congrArg (fun z ↦ z.val.app U (moduleTmul (P.X p) (Q.X q) U x y))
    (totalMap_ι a b p q n h)
  change ((tensorTotalMap a b).f n).val.app U
    ((tensorι P Q p q n h).val.app U
      (moduleTmul (P.X p) (Q.X q) U x y)) =
    (CochainComplex.ιMapBifunctor P' Q' (curriedTensor (Modules A)) p q n h).val.app U
      ((a.f p ⊗ₘ b.f q).val.app U (moduleTmul (P.X p) (Q.X q) U x y)) at ht
  erw [moduleTmul_map] at ht
  exact ht

private theorem scalarTotal_hom {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (c : Comparison (extensionPullback a)) (P Q : Complex A)
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ) (b : B.obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((tensorComparison (extensionPullback a) c P Q).hom.f n).val.app U
      (extensionTmul a ((total P Q).X n) U b (totalPure P Q p q n h U x y)) =
    totalPure ((extend a).obj P) ((extend a).obj Q) p q n h U
      (extensionTmul a (P.X p) U b x) (extensionTmul a (Q.X q) U 1 y) := by
  have ht := congrArg (fun z ↦ z.val.app U
    (extensionTmul a (P.X p ⊗ Q.X q) U b
      (ringedComparisonPure A (P.X p) (Q.X q) U x y)))
    (tensorComparison_ι (extensionPullback a) c P Q p q n h)
  change ((tensorComparison (extensionPullback a) c P Q).hom.f n).val.app U
    (((extensionFunctor a).map
      (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules A)) p q n h)).val.app U
      _) = _ at ht
  change _ = (CochainComplex.ιMapBifunctor ((extend a).obj P) ((extend a).obj Q)
    (curriedTensor (Modules B)) p q n h).val.app U
      (((c.mu (P.X p) (Q.X q)).hom).val.app U _) at ht
  erw [extension_map, (scalarTensorFormulas a c).1] at ht
  exact ht

private theorem scalarTotal_inv {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (c : Comparison (extensionPullback a)) (P Q : Complex A)
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ) (b b' : B.obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((tensorComparison (extensionPullback a) c P Q).inv.f n).val.app U
      (totalPure ((extend a).obj P) ((extend a).obj Q) p q n h U
        (extensionTmul a (P.X p) U b x) (extensionTmul a (Q.X q) U b' y)) =
      extensionTmul a ((total P Q).X n) U (b * b') (totalPure P Q p q n h U x y) := by
  have ht := congrArg (fun z ↦ z.val.app U
    (ringedComparisonPure B ((extensionFunctor a).obj (P.X p))
      ((extensionFunctor a).obj (Q.X q)) U
      (extensionTmul a (P.X p) U b x) (extensionTmul a (Q.X q) U b' y)))
    (tensorComparison_inv_ι (extensionPullback a) c P Q p q n h)
  change ((tensorComparison (extensionPullback a) c P Q).inv.f n).val.app U _ =
    (((extensionFunctor a).map
      (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules A)) p q n h)).val.app U
      (((c.mu (P.X p) (Q.X q)).inv).val.app U _)) at ht
  erw [(scalarTensorFormulas a c).2, extension_map] at ht
  exact ht


private theorem tensorArrowFor_value (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a)))
    {i k : Index} (r : i ⟶ k) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q')
    (p q n : ℤ) (hpq : p + q = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (semilinearSectionMap (B.map r) (tensorArrowFor B z r P Q P' Q' f g) n).hom.app U
      (totalPure P Q p q n hpq U x y) =
    totalPure P' Q' p q n hpq U
      ((semilinearSectionMap (B.map r) f p).hom.app U x)
      ((semilinearSectionMap (B.map r) g q).hom.app U y) := by
  dsimp only [semilinearSectionMap, tensorArrowFor]
  have he : totalMap f g = tensorTotalMap f g := (tensorTotalMap_eq f g).symm
  have hc : comparison (extensionPullback (B.map r)) (z r) P Q =
      tensorComparison (extensionPullback (B.map r)) (z r) P Q :=
    (tensorComparison_eq _ _ _ _).symm
  rw [he, hc]
  change ((tensorTotalMap f g).f n).val.app U
    (((tensorComparison (extensionPullback (B.map r)) (z r) P Q).hom.f n).val.app U
      (((extensionAdjunction (B.map r)).unit.app ((total P Q).X n)).val.app U
        (totalPure P Q p q n hpq U x y))) = _
  rw [extension_unit, scalarTotal_hom, totalMap_pure]
  change totalPure P' Q' p q n hpq U
    ((f.f p).val.app U (extensionTmul (B.map r) (P.X p) U 1 x))
    ((g.f q).val.app U (extensionTmul (B.map r) (Q.X q) U 1 y)) = _
  congr 1
  · change (f.f p).val.app U _ = (f.f p).val.app U
      (((extensionAdjunction (B.map r)).unit.app (P.X p)).val.app U x)
    rw [extension_unit]
  · change (g.f q).val.app U _ = (g.f q).val.app U
      (((extensionAdjunction (B.map r)).unit.app (Q.X q)).val.app U y)
    rw [extension_unit]

attribute [local irreducible] extensionFunctor squareArrow
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem tensor_hom_ext {A : Sheaf J CommRingCat.{w}}
    (M N H : Modules A) {f g : M ⊗ N ⟶ H}
    (h : ∀ U x y, f.val.app U (moduleTmul M N U x y) =
      g.val.app U (moduleTmul M N U x y)) : f = g := by
  exact CochainScalarConstruction.pure_hom_ext A M N H h



private theorem nestedTotal_hom_ext {A B H : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (b : B ⟶ H) (P Q : Complex A) (n : ℤ) (M : Modules H)
    {f g : (extensionFunctor b).obj ((extensionFunctor a).obj ((total P Q).X n)) ⟶ M}
    (h : ∀ p q (hpq : p + q = n) U x y,
      f.val.app U (extensionTmul b ((extensionFunctor a).obj ((total P Q).X n)) U 1
        (extensionTmul a ((total P Q).X n) U 1 (totalPure P Q p q n hpq U x y))) =
      g.val.app U (extensionTmul b ((extensionFunctor a).obj ((total P Q).X n)) U 1
        (extensionTmul a ((total P Q).X n) U 1 (totalPure P Q p q n hpq U x y)))) :
    f = g := by
  apply ((extensionAdjunction b).homEquiv _ M).injective
  apply ((extensionAdjunction a).homEquiv _ _).injective
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply tensor_hom_ext
  intro U x y
  change f.val.app U
    (((extensionAdjunction b).unit.app ((extensionFunctor a).obj ((total P Q).X n))).val.app U
      (((extensionAdjunction a).unit.app ((total P Q).X n)).val.app U
        (totalPure P Q p q n hpq U x y))) =
    g.val.app U
      (((extensionAdjunction b).unit.app ((extensionFunctor a).obj ((total P Q).X n))).val.app U
        (((extensionAdjunction a).unit.app ((total P Q).X n)).val.app U
          (totalPure P Q p q n hpq U x y)))
  simpa only [extension_unit] using h p q hpq U x y


attribute [local irreducible] totalPure ringedComparisonPure extensionTmul

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem tensorTransitionValues (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a))) :
    TensorTransitionValues B z := by
  intro i j k l a b r s h P Q P' Q' f g p q n hpq U v v' x y
  constructor
  · dsimp only [tensorTransitionForward, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f]
    change ((tensorTotalMap (squareArrow B a b r s h P P' f)
      (squareArrow B a b r s h Q Q' g)).f n).val.app U
      (((tensorComparison (extensionPullback (B.map s)) (z s)
        ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q)).hom.f n).val.app U
        (((extensionFunctor (B.map s)).map
          ((tensorComparison (extensionPullback (B.map a)) (z a) P Q).hom.f n)).val.app U _)) = _
    erw [extension_map (B.map s)
      ((tensorComparison (extensionPullback (B.map a)) (z a) P Q).hom.f n) U 1]
    rw [scalarTotal_hom (B.map a) (z a) P Q p q n hpq U v x y]
    rw [scalarTotal_hom (B.map s) (z s)
      ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q) p q n hpq U 1
      (extensionTmul (B.map a) (P.X p) U v x)
      (extensionTmul (B.map a) (Q.X q) U 1 y)]
    erw [totalMap_pure]
    have h₁ := squareArrow_value B a b r s h P P' f p U 1 v x
    have h₂ := squareArrow_value B a b r s h Q Q' g q U 1 1 y
    exact congrArg₂ (totalPure ((extend (B.map b)).obj P')
      ((extend (B.map b)).obj Q') p q n hpq U)
      (by
        set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
        simpa only [extend, pull, extensionPullback,
          Functor.mapHomologicalComplex, one_mul] using h₁)
      (by
        set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
        simpa only [extend, pull, extensionPullback,
          Functor.mapHomologicalComplex, map_one, one_mul] using h₂)
  · dsimp only [tensorTransitionInverse, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f]
    change ((squareArrow B a b r s h (total P Q) (total P' Q')
      (tensorArrowFor B z r P Q P' Q' f g)).f n).val.app U
      (((extensionFunctor (B.map s)).map
        ((tensorComparison (extensionPullback (B.map a)) (z a) P Q).inv.f n)).val.app U _) = _
    erw [extension_map (B.map s)
      ((tensorComparison (extensionPullback (B.map a)) (z a) P Q).inv.f n) U 1]
    erw [scalarTotal_inv]
    erw [squareArrow_value, tensorArrowFor_value]
    simp only [one_mul]
    exact congrArg (fun t ↦ extensionTmul (B.map b) ((total P' Q').X n) U t
      (totalPure P' Q' p q n hpq U
        ((semilinearSectionMap (B.map r) f p).hom.app U x)
        ((semilinearSectionMap (B.map r) g q).hom.app U y)))
      (map_mul ((B.map s).hom.app U).hom v v')

private theorem tensorTransitionLaws (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a))) :
    TensorTransitionLaws B z := by
  intro i j k l a b r s h P Q P' Q' f g
  ext n : 1
  apply nestedTotal_hom_ext (B.map a) (B.map s) P Q n
  intro p q hpq U x y
  have ht := (tensorTransitionValues B z a b r s h P Q P' Q' f g
    p q n hpq U 1 1 x y).1
  simp only [map_one] at ht
  unfold tensorTransitionForward at ht
  simp only [tensorComparison_eq, tensorTotalMap_eq] at ht
  erw [ht]
  change _ = ((comparison (extensionPullback (B.map b)) (z b) P' Q').hom.f n).val.app U
    (((squareArrow B a b r s h (total P Q) (total P' Q')
      (tensorArrowFor B z r P Q P' Q' f g)).f n).val.app U _)
  have hv := scalarTotal_hom (B.map b) (z b) P' Q' p q n hpq U 1
    ((semilinearSectionMap (B.map r) f p).hom.app U x)
    ((semilinearSectionMap (B.map r) g q).hom.app U y)
  rw [tensorComparison_eq] at hv
  erw [squareArrow_value, map_one, mul_one]
  have hu := tensorArrowFor_value B z r P Q P' Q' f g p q n hpq U x y
  change ((tensorArrowFor B z r P Q P' Q' f g).f n).val.app U
    (((extensionAdjunction (B.map r)).unit.app ((total P Q).X n)).val.app U
      (totalPure P Q p q n hpq U x y)) = _ at hu
  change _ = ((comparison (extensionPullback (B.map b)) (z b) P' Q').hom.f n).val.app U
    (extensionTmul (B.map b) ((total P' Q').X n) U 1
      (((tensorArrowFor B z r P Q P' Q' f g).f n).val.app U
        (((extensionAdjunction (B.map r)).unit.app ((total P Q).X n)).val.app U
          (totalPure P Q p q n hpq U x y))))
  exact hv.symm.trans (congrArg
    (fun t : ((total P' Q').X n).val.obj U ↦
      ((comparison (extensionPullback (B.map b)) (z b) P' Q').hom.f n).val.app U
        (extensionTmul (B.map b) ((total P' Q').X n) U 1 t)) hu.symm)

/-- Scalar tensor comparisons commute with arbitrary semilinear squares and have
its forward/inverse coefficient formulas on each homogeneous tensor summand.
Source: Stacks 03EK, 03EL and 07A4, original strict-totalization step 6
(blueprint: lem-pur-normalized-scalar-tensor-transitions).
Proof: the normalized scalar tensor map inserts one; its inverse multiplies
coefficients. Scalar associators multiply coefficients by adjoint uniqueness.
Compose these formulas with the two arbitrary transition adjoints. Ring maps
preserve products and one. Finally use both scalar adjunctions, the tensor
universal property and coproduct extensionality to obtain equality of whole maps. -/
theorem normalizedScalarTensorTransitions (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a))) :
    TensorTransitionLaws B z ∧ TensorTransitionValues B z := by
  exact ⟨tensorTransitionLaws B z, tensorTransitionValues B z⟩

end CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation
