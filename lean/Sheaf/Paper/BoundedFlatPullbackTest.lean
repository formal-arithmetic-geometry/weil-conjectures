/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Bounded flat pullback and arbitrary target tensor tests

Source: Stacks Project, Tags 05VD, 015F, 06YQ and Section 06YL; blueprint
thm-exc-explicit-preservation, proof paragraph 2
(blueprint: lem-exc-bounded-flat-pullback-test).

ModuleCat-valued sheaves present modules over the constant ring sheaf. The tensor
comparison below is natural simultaneously in the bounded flat complex and in every
module sheaf on the target, without requiring that the latter descend to the source.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Limits MonoidalCategory

/-- Tensor tests built from a pair of functors into a monoidal category.
Source: signed tensor tests, blueprint lem-exc-bounded-flat-pullback-test.
(blueprint: lem-exc-bounded-flat-pullback-test). -/
@[irreducible]
def tensorTestFunctor {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] (B : D ⥤ C) (S : E ⥤ C) : D × E ⥤ C :=
  B.prod S ⋙ Functor.uncurry.obj (curriedTensor C)

private def tensorComparison {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] :
    F.prod F ⋙ Functor.uncurry.obj (curriedTensor D) ⟶
      Functor.uncurry.obj (curriedTensor C) ⋙ F where
  app X := Functor.LaxMonoidal.μ F X.1 X.2
  naturality X Y f := by
    simpa only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
      curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def] using
      Functor.LaxMonoidal.μ_natural F f.1 f.2

private lemma isIsoQTensor {C : Type*} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [HasDerivedCategory.{v} C]
    [Abelian.HasFunctorialFlatResolution C] (P L : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P L) := by
  let H := HomotopyCategory.quotient C (.up ℤ)
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh (H.obj P) (H.obj L)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left _ _ _ _ hP'
  change IsIso (((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
    (DerivedCategory.quotientCompQhIso C).inv.app L) ≫
    Functor.LaxMonoidal.μ (H ⋙ DerivedCategory.Qh) P L ≫
    (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ L))
  rw [Functor.LaxMonoidal.comp_μ]
  infer_instance

private theorem tensorTestsIso {C D E K : Type*} [Category C] [Category D]
    [Category E] [Category K] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (B : E ⥤ C) (S : K ⥤ C)
    (h : ∀ P M, IsIso (Functor.LaxMonoidal.μ F (B.obj P) (S.obj M))) :
    Nonempty (((B ⋙ F).prod (S ⋙ F)) ⋙ Functor.uncurry.obj (curriedTensor D) ≅
      (B.prod S ⋙ Functor.uncurry.obj (curriedTensor C)) ⋙ F) := by
  let τ := Functor.whiskerLeft (B.prod S) (tensorComparison F)
  have : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro PM
    exact h PM.1 PM.2
  exact ⟨asIso τ⟩

private theorem tensorTestFunctorComparison {C D E K : Type*}
    [Category C] [Category D] [Category E] [Category K]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    (B : E ⥤ C) (S : K ⥤ C) (R : E ⥤ D) (e : R ≅ B ⋙ F)
    (h : ∀ P M, IsIso (Functor.LaxMonoidal.μ F (B.obj P) (S.obj M))) :
    Nonempty (tensorTestFunctor R (S ⋙ F) ≅ tensorTestFunctor B S ⋙ F) := by
  rw [tensorTestFunctor, tensorTestFunctor]
  obtain ⟨t⟩ := tensorTestsIso F B S h
  exact ⟨Functor.isoWhiskerRight (NatIso.prod e (Iso.refl _)) _ ≪≫ t⟩

private lemma tensorSingleTermIsZero {C : Type*} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] (P : CochainComplex C ℤ) (M : C) (n : ℤ)
    (hn : IsZero (P.X n)) :
    IsZero ((P ⊗ (CochainComplex.singleFunctor C 0).obj M).X n) := by
  have e : P ⊗ (CochainComplex.singleFunctor C 0).obj M ≅
      ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P :=
    CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P
  exact IsZero.of_iso ((tensorRight M).map_isZero hn)
    ((HomologicalComplex.eval C (.up ℤ) n).mapIso e)

private lemma derivedHomologyIsZero {C : Type*} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{v} C] (K : DerivedCategory C) (P : CochainComplex C ℤ)
    (e : K ≅ DerivedCategory.Q.obj P) (n : ℤ) (hn : IsZero (P.X n)) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj K) := by
  have hh : IsZero (P.homology n) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ hn
  exact IsZero.of_iso hh
    ((DerivedCategory.homologyFunctor C n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors C n).app P)

namespace AlgebraicGeometry.ProEtale.BoundedFlatPullbackTest

/-- The full domain of flat complexes supported in the specified interval.
Source: blueprint thm-exc-explicit-preservation, paragraph 2; Stacks Tag 06YQ
(blueprint: lem-exc-bounded-flat-pullback-test). -/
def flatInterval (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] (c d : ℤ) :
    ObjectProperty (CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :=
  fun P ↦ (∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q))) ∧
    ∀ q : ℤ, q < c ∨ d < q → IsZero (P.X q)

/-- The actual termwise inverse image on constant-coefficient module sheaves.
Source: Stacks Tags 00WX and 015F; blueprint thm-exc-explicit-preservation, paragraph 2
(blueprint: lem-exc-bounded-flat-pullback-test). -/
def termwisePullback {V X : Scheme.{u}} (f : V ⟶ X) (A : Type (u + 1)) [CommRing A] :
    CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)) ℤ :=
  (upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)

/-- The signed total tensor of the pulled-back complex with an arbitrary target sheaf
in degree zero; maps are the actual tensor maps of the two factors.
Source: Stacks Section 06YL; blueprint thm-exc-explicit-preservation, paragraph 2
(blueprint: lem-exc-bounded-flat-pullback-test). -/
def strictTests {V X : Scheme.{u}} (f : V ⟶ X) (A : Type (u + 1)) [CommRing A]
    (c d : ℤ) :
    (flatInterval X A c d).FullSubcategory ×
        Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A) ⥤
      CochainComplex (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)) ℤ :=
  tensorTestFunctor ((flatInterval X A c d).ι ⋙ termwisePullback f A)
    (CochainComplex.singleFunctor _ 0)

/-- Derived tensor tests against every target module sheaf, with its degree-zero
localization and the existing derived tensor functor.
Source: Stacks Section 06YL; blueprint thm-exc-explicit-preservation, paragraph 2
(blueprint: lem-exc-bounded-flat-pullback-test). -/
def derivedTests {V X : Scheme.{u}} (f : V ⟶ X) (A : Type (u + 1)) [CommRing A]
    (c d : ℤ) :
    (flatInterval X A c d).FullSubcategory ×
        Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A) ⥤
      ModuleDerivedCategory V A :=
  tensorTestFunctor ((flatInterval X A c d).ι ⋙ DerivedCategory.Q ⋙
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory)
    (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q)

private theorem sheafQTensorIsIso (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] (V : Scheme.{u})
    (P L : CochainComplex (Sheaf (Scheme.ProEt.topology V) A) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P L) := by
  exact isIsoQTensor P L hP



private theorem tensorTestsComparison {V X : Scheme.{u}} (f : V ⟶ X)
    (A : Type (u + 1)) [CommRing A] [Finite A] (c d : ℤ)
    (hk : ∀ P : (flatInterval X A c d).FullSubcategory,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        ((termwisePullback f A).obj P.obj)) :
    Nonempty (derivedTests f A c d ≅ strictTests f A c d ⋙ DerivedCategory.Q) := by
  exact tensorTestFunctorComparison DerivedCategory.Q
    ((flatInterval X A c d).ι ⋙ termwisePullback f A)
    (CochainComplex.singleFunctor _ 0) _
    (Functor.isoWhiskerLeft (flatInterval X A c d).ι
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors)
    (fun P M ↦ sheafQTensorIsIso (ModuleCat.{u + 1} A) V _ _ (hk P))

/-- Flat bounded inverse image computes all target-side tensor tests, naturally in
both the complex and the arbitrary target module sheaf.
Source: Stacks Tags 05VD, 015F, 06YQ and Section 06YL; blueprint
thm-exc-explicit-preservation, proof paragraph 2
(blueprint: lem-exc-bounded-flat-pullback-test).

Proof:
1. Apply lem-weil-pbc-ringed-topos-flat-module-pullback to the pro-etale geometric
   morphism and the canonical constant coefficient map. Thus every inverse-image
   term is flat, without flatness of the scheme morphism or of the ring map.
2. prop-weil-pbc-proetale-constant-exact gives exactness. Hence zero terms stay
   zero. lem-weil-pbc-exact-functor-derived-factorization supplies the natural
   comparison between termwise localization and the induced derived functor.
3. The upper bound d and the flat terms give K-flatness by
   lem-pc-bounded-above-flat-kflat-site, transported to fixed-ring module sheaves.
4. Use the identity K-flat resolution of the pulled-back complex in
   def-weil-derived-tensor. lem-weil-derived-tensor-resolution-independent
   identifies this with the fixed derived tensor. The comparisons commute with
   every chain map and every map of target module sheaves, yielding the stated
   natural isomorphism on the product category.
5. In degree n, tensoring with M[0] has only F^n tensor M and differential
   d_F tensor 1. Thus it vanishes outside [c,d], and so does its cohomology.
   Apply def-weil-derived-cohomology-sheaves to the comparison to deduce the
   cohomology vanishing of the derived test. No condition is placed on M.
-/
theorem bounded_flat_pullback_test {V X : Scheme.{u}} (f : V ⟶ X)
    (A : Type (u + 1)) [CommRing A] [Finite A] (c d : ℤ) (_hcd : c ≤ d) :
    (∀ P : (flatInterval X A c d).FullSubcategory,
      (∀ q : ℤ, exactFunctor _ _
        (tensorRight (((termwisePullback f A).obj P.obj).X q))) ∧
      (∀ q : ℤ, q < c ∨ d < q →
        IsZero (((termwisePullback f A).obj P.obj).X q)) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        ((termwisePullback f A).obj P.obj)) ∧
    Nonempty ((flatInterval X A c d).ι ⋙ termwisePullback f A ⋙ DerivedCategory.Q ≅
      (flatInterval X A c d).ι ⋙ DerivedCategory.Q ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory) ∧
    Nonempty (derivedTests f A c d ≅ strictTests f A c d ⋙ DerivedCategory.Q) ∧
    ∀ (P : (flatInterval X A c d).FullSubcategory)
      (M : Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)) (n : ℤ),
      n < c ∨ d < n →
        IsZero (((strictTests f A c d).obj (P, M)).X n) ∧
        IsZero ((DerivedCategory.homologyFunctor _ n).obj
          ((derivedTests f A c d).obj (P, M))) := by
  have hflat (P : (flatInterval X A c d).FullSubcategory) (q : ℤ) :
      ObjectProperty.flat (((termwisePullback f A).obj P.obj).X q) := by
    have h := (P.property.1 q).preservesFiniteLimits
    have hleft : PreservesFiniteLimits (tensorLeft (P.obj.X q)) :=
      preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (P.obj.X q)).symm
    exact Functor.PreservesFlat.flat_obj (F := upperStar (ModuleCat.{u + 1} A) f)
      ((ObjectProperty.flat_iff_preservesFiniteLimits _).2 hleft)
  have hzero (P : (flatInterval X A c d).FullSubcategory) (q : ℤ)
      (hq : q < c ∨ d < q) :
      IsZero (((termwisePullback f A).obj P.obj).X q) :=
    (upperStar (ModuleCat.{u + 1} A) f).map_isZero (P.property.2 q hq)
  have hk (P : (flatInterval X A c d).FullSubcategory) :
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        ((termwisePullback f A).obj P.obj) := by
    have hb : ((termwisePullback f A).obj P.obj).IsStrictlyLE d :=
      (CochainComplex.isStrictlyLE_iff _ _).2 (fun q hq ↦ hzero P q (.inr hq))
    exact CochainComplex.kFlat_of_isStrictlyLE_of_flat _ d (hflat P)
  let C := Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)
  let B := (flatInterval X A c d).ι ⋙ termwisePullback f A
  have e := Functor.isoWhiskerLeft (flatInterval X A c d).ι
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.symm
  obtain ⟨eTest⟩ := tensorTestsComparison f A c d hk
  refine ⟨fun P ↦ ⟨fun q ↦ (hflat P q).2, hzero P, hk P⟩, ⟨e⟩, ⟨eTest⟩, ?_⟩
  intro P M n hn
  have hz : IsZero (((strictTests f A c d).obj (P, M)).X n) :=
    by
      rw [strictTests, tensorTestFunctor]
      exact tensorSingleTermIsZero (C := C) (B.obj P) M n (hzero P n hn)
  refine ⟨hz, ?_⟩
  exact derivedHomologyIsZero (C := C) _ _ (eTest.app (P, M)) n hz

end AlgebraicGeometry.ProEtale.BoundedFlatPullbackTest
