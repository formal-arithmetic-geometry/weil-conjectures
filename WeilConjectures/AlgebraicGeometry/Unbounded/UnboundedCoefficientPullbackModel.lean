/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarMateIdentifications
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarBalancingChain
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.AlgebraicGeometry.PulledNormalization.PulledReductionNormalizationComparison
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

/-! # Unbounded coefficient comparison on flat-term K-flat pullback models

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 06YT, 06YY, 0G7D;
sites-modules.tex, Tag 03EL; blueprint thm-exc-explicit-preservation, proof paragraph 2.
(blueprint: lem-exc-unbounded-coefficient-pullback-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem conjugate_linear
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (a : R ⟶ S)
    {N N' P P' : SheafOfModules.{u + 1} S} (k : N ≅ P) (l : N' ≅ P')
    (h : (SheafOfModules.restrictScalars a).obj P ⟶
      (SheafOfModules.restrictScalars a).obj P')
    (h' : (SheafOfModules.restrictScalars a).obj N ⟶
      (SheafOfModules.restrictScalars a).obj N')
    (hh : h' = (SheafOfModules.restrictScalars a).map k.hom ≫ h ≫
      (SheafOfModules.restrictScalars a).map l.inv)
    (hb : ∀ W (b : S.obj.obj W) (x : P.val.obj W),
      h.val.app W (b • x) = b • (show P'.val.obj W from h.val.app W x)) :
    ∀ W (b : S.obj.obj W) (x : N.val.obj W),
      h'.val.app W (b • x) = b • (show N'.val.obj W from h'.val.app W x) := by
  intro W b x
  rw [hh]
  change l.inv.val.app W (h.val.app W (k.hom.val.app W (b • x))) = _
  rw [map_smul, hb]
  exact (l.inv.val.app W).hom.map_smul b _

/-- Compute coefficient extension after exact pullback using a supplied representative.
This is the pullback factorization followed by the existing universal scalar counit.
Source: Stacks 06YT, 06YY (blueprint: lem-exc-unbounded-coefficient-pullback-model). -/
def excPullbackThenCoefficientComputation
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K) :=
  (directImageScalarExtension φ V).map
    ((proEtaleConstantRingDerivedPullback A f).map i.inv ≫
      (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
    reductionScalarComplexCounit V (proEtaleConstantRingMap (T := V) φ)
      (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)

/-- Compute pullback after coefficient extension using the same representative.
This applies exact B-pullback to the existing scalar counit, then its factorization.
Source: Stacks 06YT, 06YY (blueprint: lem-exc-unbounded-coefficient-pullback-model). -/
def excCoefficientThenPullbackComputation
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K) :=
  (proEtaleConstantRingDerivedPullback B f).map
    ((directImageScalarExtension φ X).map i.inv ≫
      reductionScalarComplexCounit X (proEtaleConstantRingMap (T := X) φ) P) ≫
    (proEtaleConstantRingPullback B f).mapDerivedCategoryFactors.hom.app
      (((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex
        (.up ℤ)).obj P)

/-- The canonical B-linear coefficient comparison, computed on every flat-term K-flat
model, for arbitrary unbounded derived objects and arbitrary finite-ring homomorphisms.
The A-linear normalization uses the published pure-tensor predicate; the equality
with excScalarBalancingMap retains the B-action before passing to complexes.
Source: Stacks 0G7E, 06YT, 06YY, 0G7D, 03EL
(blueprint: lem-exc-unbounded-coefficient-pullback-model).

Proof:
Lift the B-linear map supplied by the scalar balancing chain to a natural isomorphism s.
Its inverse gives T degreewise. The two adjunction bijections and the unit tensor formula
identify this inverse with the ordinary coefficient/pullback mate. The general derived
mate comparison computes the canonical derived mate on every cochain representative,
using the published scalar counits and exact-pullback factorization. Naturality along
the supplied isomorphism [P] ≅ K gives the displayed computation equation.
The ringed-topos K-flat pullback theorem supplies flatness and K-flatness of the pulled
model; exactness preserves quasi-isomorphisms. The scalar counits on these K-flat models
are invertible, so both named computation morphisms are isomorphisms. This proof uses
the supplied model and the existing derived comparison, without a new localization. -/
theorem unboundedCoefficientPullbackModel
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X) :
    ∃ t : scalarMateOrdinaryTensor φ X ⋙ proEtaleConstantRingPullback A f ≅
        proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ V,
      IsScalarBalancing φ f t ∧
      ∃ s : proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
          proEtaleConstantRingPullback B f ≅
        proEtaleConstantRingPullback A f ⋙
          proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ),
        (∀ M : proEtaleRingModules X (proEtaleConstantRing X A),
          (scalarMateRestriction φ V).map (s.hom.app M) = excScalarBalancingMap φ f t M) ∧
        ∃ T : (proEtaleConstantRingPullback A f ⋙
              proEtaleRingExtension (proEtaleConstantRingMap (T := V) φ)).mapHomologicalComplex
                (.up ℤ) ≅
            (proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙
              proEtaleConstantRingPullback B f).mapHomologicalComplex (.up ℤ),
          (∀ (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
            (n : ℤ), (T.hom.app P).f n = s.inv.app (P.X n) ∧
              (T.inv.app P).f n = s.hom.app (P.X n)) ∧
          (∀ P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ,
            CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing X A) P →
            (∀ n : ℤ, SheafOfModules.IsFlatOnSite
              (J := ProEt.topology X) (R := proEtaleConstantRing X A) (P.X n)) →
            CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing V A)
                (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P) ∧
            (∀ n : ℤ, SheafOfModules.IsFlatOnSite
              (J := ProEt.topology V) (R := proEtaleConstantRing V A)
              ((((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P).X n)) ∧
            (∀ (G : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
              (q : P ⟶ G), QuasiIso q →
                QuasiIso (((proEtaleConstantRingPullback A f).mapHomologicalComplex
                  (.up ℤ)).map q)) ∧
            ∀ (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K),
              IsIso (excPullbackThenCoefficientComputation φ f P K i) ∧
              IsIso (excCoefficientThenPullbackComputation φ f P K i) ∧
              (directImageScalarPullbackIso φ f).inv.app K ≫
                  excCoefficientThenPullbackComputation φ f P K i =
                excPullbackThenCoefficientComputation φ f P K i ≫
                  DerivedCategory.Q.map (T.hom.app P)) := by
  obtain ⟨_, hβ, t, ht, _, hb, _⟩ := proEtaleScalarBalancingChain φ f
  obtain ⟨s, hs⟩ := balancingLift φ f t hb
  let T := NatIso.mapHomologicalComplex s.symm (.up ℤ)
  refine ⟨t, ht, s, hs, T, ?_, ?_⟩
  · intro P n
    exact ⟨rfl, rfl⟩
  · intro P hp hf
    obtain ⟨hpf, hff⟩ := PulledNormalization.pullback_good f
      (proEtaleConstantRing X A) (proEtaleConstantRing V A)
      (proEtaleConstantRingComparison f A) P hp hf
    refine ⟨hpf, hff, ?_, ?_⟩
    · intro G q hq
      have : QuasiIso q := hq
      infer_instance
    · intro K i
      have hcX := scalarCounit_isIso X
        (proEtaleConstantRingMap (T := X) φ) P hp
      have hcV := scalarCounit_isIso V
        (proEtaleConstantRingMap (T := V) φ)
        (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P) hpf
      refine ⟨?_, ?_, ?_⟩
      · unfold excPullbackThenCoefficientComputation
        infer_instance
      · unfold excCoefficientThenPullbackComputation
        infer_instance
      · have he := balancingLift_eq_mate φ f t ht hβ s hs
        have hm := PulledNormalization.derivedMate_rep f
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRing V A) (proEtaleConstantRing V B)
          (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := V) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm P
        have hT : T.hom.app P = (NatIso.mapHomologicalComplex
            (PulledNormalization.ordinaryMate f
              (proEtaleConstantRing X A) (proEtaleConstantRing X B)
              (proEtaleConstantRing V A) (proEtaleConstantRing V B)
              (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := V) φ)
              (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
              (proEtaleConstantInverseImageMap_naturality f
                (CommRingCat.ofHom (RingHom.ulift φ))).symm) (.up ℤ)).hom.app P := by
          simp only [T, he]
          rfl
        rw [hT]
        simp only [excCoefficientThenPullbackComputation,
          excPullbackThenCoefficientComputation, Functor.map_comp, Category.assoc]
        have hn := ((directImageScalarPullbackIso φ f).inv.naturality i.inv).symm
        change (directImageScalarPullbackIso φ f).inv.app K ≫
            (proEtaleConstantRingDerivedPullback B f).map
              ((directImageScalarExtension φ X).map i.inv) =
          (directImageScalarExtension φ V).map
            ((proEtaleConstantRingDerivedPullback A f).map i.inv) ≫
              (directImageScalarPullbackIso φ f).inv.app (DerivedCategory.Q.obj P) at hn
        rw [reassoc_of% hn]
        exact congrArg (fun z ↦ (directImageScalarExtension φ V).map
          ((proEtaleConstantRingDerivedPullback A f).map i.inv) ≫ z) hm

end AlgebraicGeometry.ProEtale
