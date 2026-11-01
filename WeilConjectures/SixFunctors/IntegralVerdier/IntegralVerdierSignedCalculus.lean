/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomModelsExist
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Normalized signed biduality calculus

Source: Stacks Project, Tags 06YL and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralVerdier

private theorem transport_natural {C : Type*} [Category* C]
    (T A : C × C ⥤ C) (e : T ≅ A)
    (b : ∀ K L : C, T.obj (K, L) ≅ T.obj (L, K))
    (hb : ∀ (K L K' L' : C) (f : K ⟶ K') (g : L ⟶ L'),
      T.map (Prod.mkHom f g) ≫ (b K' L').hom =
        (b K L).hom ≫ T.map (Prod.mkHom g f))
    (K L K' L' : C) (f : K ⟶ K') (g : L ⟶ L') :
    A.map (Prod.mkHom f g) ≫ e.inv.app (K', L') ≫ (b K' L').hom ≫
        e.hom.app (L', K') =
      e.inv.app (K, L) ≫ (b K L).hom ≫ e.hom.app (L, K) ≫ A.map (Prod.mkHom g f) := by
  rw [e.inv.naturality_assoc]
  rw [← Category.assoc (T.map (Prod.mkHom f g)), hb]
  simp only [Category.assoc]
  rw [e.hom.naturality]

private theorem generator_transport (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (i j k : ℤ) (h : i + j = k) (U : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R P Q i j k h U x y =
      (eqToHom (congrArg
        (fun n : ℤ ↦ (((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q).X n)
          h)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) := by
  subst k
  rfl

private theorem presentation_symmetry (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R) :
    ∃ s : SignedSymmetry X R a,
      ∀ (K L K' L' : IntegralHom.Derived.{u, u} X R) (f : K ⟶ K') (g : L ⟶ L'),
        a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
          (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f) := by
  let : HasDerivedCategory.{u + 2}
      (RingedTensorModules.{u + 1, u, u} (ProEt.topology X) R) :=
    HasDerivedCategory.standard _
  obtain ⟨S, T, β, ⟨hc⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2} (ProEt.topology X) R
  let : MonoidalCategory (IntegralHom.Derived.{u, u} X R) := S.monoidal
  let : SymmetricCategory (IntegralHom.Derived.{u, u} X R) := β
  let q : (IntegralHom.flat.{u, u} X R).FullSubcategory ⥤
      IntegralHom.Derived.{u, u} X R :=
    coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology X) R ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (IntegralHom.Modules.{u, u} X R) (.up ℤ)).inverseImage
    (coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology X) R)
  have : q.IsLocalization W :=
    RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2} (ProEt.topology X) R
  let FF := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (W.prod W)
    (IntegralHom.Derived.{u, u} X R)
  let e : S.tensor ≅ a.tensor := FF.preimageIso (T.comparison.symm ≪≫ a.representative)
  have he : Functor.isoWhiskerLeft (q.prod q) e =
      T.comparison.symm ≪≫ a.representative := by
    apply Iso.ext
    exact FF.map_preimage _
  have he_app (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
      (hP : IntegralHom.flat.{u, u} X R P) (hQ : IntegralHom.flat.{u, u} X R Q) :
      (T.iso (ProEt.topology X) R S P Q hP hQ).hom ≫
        e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
          a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) := by
    have h := congrArg (fun z ↦ z.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) he
    change e.hom.app _ = (T.iso _ _ _ P Q hP hQ).inv ≫ _ at h
    erw [h, Iso.hom_inv_id_assoc]
  let swap (K L : IntegralHom.Derived.{u, u} X R) :
      a.tensor.obj (K, L) ≅ a.tensor.obj (L, K) :=
    (e.app (K, L)).symm ≪≫ β.toBraidedCategory.braiding K L ≪≫ e.app (L, K)
  have hswap : ∀ (K L K' L' : IntegralHom.Derived.{u, u} X R)
      (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (swap K' L').hom =
        (swap K L).hom ≫ a.tensor.map (Prod.mkHom g f) := by
    intro K L K' L' f g
    have hb (A B A' B' : IntegralHom.Derived.{u, u} X R)
        (f' : A ⟶ A') (g' : B ⟶ B') :
        S.tensor.map (Prod.mkHom f' g') ≫ (β.toBraidedCategory.braiding A' B').hom =
          (β.toBraidedCategory.braiding A B).hom ≫ S.tensor.map (Prod.mkHom g' f') := by
      exact BraidedCategory.braiding_naturality f' g'
    have h := transport_natural S.tensor a.tensor e β.toBraidedCategory.braiding hb
      K L K' L' f g
    with_unfolding_all
      change a.tensor.map (Prod.mkHom f g) ≫
          (e.inv.app (K', L') ≫ (β.toBraidedCategory.braiding K' L').hom ≫
            e.hom.app (L', K')) =
          (e.inv.app (K, L) ≫ (β.toBraidedCategory.braiding K L).hom ≫
            e.hom.app (L, K)) ≫ a.tensor.map (Prod.mkHom g f)
    erw [Category.assoc, Category.assoc]
    exact h
  refine ⟨⟨swap, hswap, ?_⟩, hswap⟩
  intro P Q hP hQ
  obtain ⟨s, hs, hsquare⟩ := hc.symmetry_model P Q hP hQ
  refine ⟨s.hom, ?_, ?_⟩
  · intro i j U x y
    have h := hs i j (i + j) rfl (add_comm j i) U x y
    simp only [generator_transport, eqToHom_refl, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] at h
    with_unfolding_all exact h
  · apply (cancel_epi (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩))).1
    simp only [Iso.hom_inv_id_app_assoc]
    simp only [swap, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
    erw [← he_app P Q hP hQ, Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Category.assoc, hsquare, Category.assoc, he_app Q P hQ hP]
    rfl

/-- Coherent normalized tensor-Hom presentations over the completed coefficient
sheaf and all finite quotients. This asserts only the structural calculus, with
no geometric dualizing object, constructibility, bounds, or biduality premise.

Source: Stacks Project, Tags 06YL, 06YU, 08J9, 08JA and 07A4;
thm-coef-integral-verdier proof step 5
(blueprint: lem-sf-integral-verdier-signed-calculus).

Proof: take the source tensor presentation and every normalized finite reduction
presentation from IntegralHom.models_exist. For an arbitrary supplied presentation,
compare its K-flat tensor comparison with the native symmetric monoidal comparison.
Full faithfulness of restriction along the product K-flat localization lifts their
ratio to a natural isomorphism between the native tensor and the supplied tensor.
Conjugate the native braiding by this isomorphism. Its naturality gives the two-input
swap equation. The native chain swap sends x tensor y in bidegree (i,j) to
(-1)^(ij) y tensor x. The representative comparison square identifies this with the
supplied tensor's swap, including transport from degree j+i to degree i+j.
Apply this construction to the source presentation and every finite presentation.
IntegralHom.evaluation_naturality supplies the first-variable counit equation for
each supplied presentation, using its representative evaluation normalization.
Choose the finite presentations and symmetries simultaneously and assemble the four
universal equations. No geometric dualizing input or boundedness is used. -/
theorem signedCalculus
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    ∃ (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
      (s : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) a)
      (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
      (t : ∀ n : ℕ, SignedSymmetry X (integralCoefficientCommRingSheaf l E X n)
        (m n).target),
      (∀ (K L K' L' : Ambient l E X) (f : K ⟶ K') (g : L ⟶ L'),
        a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
          (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f)) ∧
      (∀ (K K' W : Ambient l E X) (f : K' ⟶ K),
        a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheaf l E X D hl)).map
            (Prod.mkHom f.op (𝟙 W)))) ≫ (a.adjunction K').counit.app W =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W) ∧
      (∀ (n : ℕ) (K L K' L' : DerivedCategory (scalarReductionTarget l E X n))
        (f : K ⟶ K') (g : L ⟶ L'),
        (m n).target.tensor.map (Prod.mkHom f g) ≫ ((t n).swap K' L').hom =
          ((t n).swap K L).hom ≫ (m n).target.tensor.map (Prod.mkHom g f)) ∧
      (∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l E X n))
        (f : K' ⟶ K),
        (m n).target.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
            (Prod.mkHom f.op (𝟙 W)))) ≫ ((m n).target.adjunction K').counit.app W =
        (m n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
          ((m n).target.adjunction K).counit.app W) := by
  classical
  obtain ⟨a, ha⟩ := IntegralHom.models_exist l E X D hl
  obtain ⟨s, hs⟩ := presentation_symmetry X _ a
  let m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n :=
    fun n ↦ (ha n).some
  have ht (n : ℕ) := presentation_symmetry X _ (m n).target
  choose t ht using ht
  exact ⟨a, s, m, t, hs, IntegralHom.evaluation_naturality X _ a, ht,
    fun n ↦ IntegralHom.evaluation_naturality X _ (m n).target⟩

end WeilConjectures.IntegralVerdier
