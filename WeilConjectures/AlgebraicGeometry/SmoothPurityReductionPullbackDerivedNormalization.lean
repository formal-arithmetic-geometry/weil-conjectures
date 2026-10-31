/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionPullbackOrdinaryNormalization
import all WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskeringSupplement
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependentSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlyingSupplement

/-! # Derived normalization for a smooth-purity reduction pullback

Source: Stacks 07A4, 0G7E; blueprint integral direct-image proof (3).
(blueprint: lem-sp-reduction-pullback-derived-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The derived counit equation and canonical comparison for the
ordinary-normalized pullback core.

Source: Stacks Project, Tags 06YS, 0G7E and 07A4; Categories, Tag 04VK; blueprint
integral direct-image proof (3).
Proof: let P be the integral cochain complexes that are K-flat with flat terms. Every
complex has a quasi-isomorphism from one in P (Tag 06YS), so the derived category is a
localization of P and restriction of functors out of it along P is fully faithful
(Tag 04VK). For K in P, inverse image keeps K K-flat (Tag 0G7E), so the recorded
`computes` fields of both reduction towers make the two representative comparisons
e1 (integral pullback, then target counit) and e2 (source counit, then system pullback)
invertible. On P compose e1, the core's ordinary isomorphism and the inverse of e2, and
lift this natural isomorphism to nu. Its value on each K in P is that composite, which
is the displayed counit equation after cancelling e2. The argument applies also to zero
complexes and to identity and empty schemes.
(blueprint: lem-sp-reduction-pullback-derived-normalization). -/
theorem sp_reduction_pullback_derived_normalization
    (hl : ∀ x : T, IsUnit (l : T.residueField x))
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    {T' : Scheme.{u}} (hl' : ∀ x : T', IsUnit (l : T'.residueField x)) (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (p : SpReductionPullbackOrdinaryData l E T D r g D' r') :
    Nonempty { ν : p.core.integral.modules.mapDerivedCategory ⋙
      spMonoidalReduction l E T' D' r' ≅
      spMonoidalReduction l E T D r ⋙ p.core.system.modules.mapDerivedCategory //
      SpPullbackDerived l E T D r g D' r'
        (SpReductionPullbackCore.toData l E T D r g D' r' p.core ν) } := by
  classical
  have _ := hl
  have _ := hl'
  let C := spIntegralSectionModules l E T
  let I := p.core.integral.modules
  let J := p.core.system.modules
  let A := spMonoidalOrdinary l E T D r
  let A' := spMonoidalOrdinary l E T' D' r'
  let R := spMonoidalReduction l E T D r
  let R' := spMonoidalReduction l E T' D' r'
  let e₁ : DerivedCategory.Q ⋙ I.mapDerivedCategory ⋙ R' ⟶
      (I ⋙ A').mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight I.mapDerivedCategoryFactors.hom R' ≫
      Functor.whiskerLeft (I.mapHomologicalComplex (.up ℤ))
        (spMonoidalCounit l E T' D' r')
  let e₂ : DerivedCategory.Q ⋙ R ⋙ J.mapDerivedCategory ⟶
      (A ⋙ J).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (spMonoidalCounit l E T D r) J.mapDerivedCategory ≫
      Functor.whiskerLeft (A.mapHomologicalComplex (.up ℤ))
        J.mapDerivedCategoryFactors.hom
  let τ : ((I ⋙ A').mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ≅
      ((A ⋙ J).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex p.core.ordinary (.up ℤ)) DerivedCategory.Q
  let P : ObjectProperty (CochainComplex C ℤ) := fun K ↦
    K.IsKFlatIndependentCoefficients ∧
      flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (spIntegralSectionRing l E T) K
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun K ↦ P K.as
  let q := HomotopyCategory.quotient C (.up ℤ)
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  have hp (K : CochainComplex C ℤ) : P K ↔ H (q.obj K) := Iff.rfl
  have hres : ∀ X : HomotopyCategory C (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), W f := by
    intro X
    obtain ⟨K, f, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    have hf' : flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (spIntegralSectionRing l E T) K := by
      intro n
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (spIntegralSectionRing l E T) (K.X n)).symm
        (hf n)
    refine ⟨⟨q.obj K, hk, hf'⟩, q.map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  let f := H.lift (P.ι ⋙ q) (fun K ↦ (hp K.obj).1 K.property)
  have : f.Full := ⟨by
    intro X Y g
    obtain ⟨a, ha⟩ := q.map_surjective g.hom
    refine ⟨ObjectProperty.homMk a, ?_⟩
    apply ObjectProperty.hom_ext
    exact ha⟩
  have : f.EssSurj := ⟨by
    intro X
    obtain ⟨Y, hy⟩ := HomotopyCategory.quotient_obj_surjective X.obj
    exact ⟨⟨Y, (hp Y).2 (hy.symm ▸ X.property)⟩,
      ⟨ObjectProperty.isoMk H (eqToIso hy)⟩⟩⟩
  have : (H.ι ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage H.ι) :=
    CategoryTheory.restriction_localization W DerivedCategory.Qh H hres
  let ff := (Localization.fullyFaithfulWhiskeringLeft
    (H.ι ⋙ DerivedCategory.Qh) (W.inverseImage H.ι)
    (DerivedCategory (spMonoidalSystems l E T'))).comp
      (CategoryTheory.fullyFaithfulWhiskeringOfFullEssSurj f _)
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _
    (DerivedCategory (spMonoidalSystems l E T'))).mapIso
      (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso C)))
  have he₁ (K : P.FullSubcategory) : IsIso (e₁.app K.obj) := by
    have : PreservesFiniteLimits
        (Scheme.proEtaleSheafInverseImage g (Type (u + 1))) :=
      (toposFunctorialityInverseImage g (𝟙 T)).2.2.2.1
    have hk := SheafOfModules.kFlat_inverseImage_independent
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1)))
      p.core.integral K.obj K.property.1 K.property.2
    let := D'.hasDerived
    let := r'.computes ((I.mapHomologicalComplex (.up ℤ)).obj K.obj) hk
    dsimp only [e₁, spMonoidalCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  have he₂ (K : P.FullSubcategory) : IsIso (e₂.app K.obj) := by
    let := D.hasDerived
    let := r.computes K.obj K.property.1
    dsimp only [e₂, spMonoidalCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  let a : P.ι ⋙ DerivedCategory.Q ⋙ I.mapDerivedCategory ⋙ R' ≅
      P.ι ⋙ (I ⋙ A').mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (e₁.app K.obj) (he₁ K))
      (fun g ↦ e₁.naturality g.hom)
  let b : P.ι ⋙ DerivedCategory.Q ⋙ R ⋙ J.mapDerivedCategory ≅
      P.ι ⋙ (A ⋙ J).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (e₂.app K.obj) (he₂ K))
      (fun g ↦ e₂.naturality g.hom)
  let c := a ≪≫ Functor.isoWhiskerLeft P.ι τ ≪≫ b.symm
  let ν : I.mapDerivedCategory ⋙ R' ≅ R ⋙ J.mapDerivedCategory := ff'.preimageIso c
  refine ⟨ν, ?_⟩
  intro K hk hf
  have hν : ν.hom.app (DerivedCategory.Q.obj K) = c.hom.app ⟨K, hk, hf⟩ :=
    congrArg (fun z ↦ z.app ⟨K, hk, hf⟩) (ff'.map_preimage (X := I.mapDerivedCategory ⋙ R')
      (Y := R ⋙ J.mapDerivedCategory) c.hom)
  change _ = ν.hom.app (DerivedCategory.Q.obj K) ≫ _
  rw [hν]
  have := he₂ ⟨K, hk, hf⟩
  change _ = (e₁.app K ≫ τ.hom.app K ≫ inv (e₂.app K)) ≫ e₂.app K
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.ProEtale
