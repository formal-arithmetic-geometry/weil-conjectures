/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.AlgebraicGeometry.OpenScalarTensor.OpenScalarTensorData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarRestrictionUnit
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Open extension preserves the normalized scalar counit

Source: Stacks Project, sites-modules.tex, Tag 0E8I; sites-cohomology.tex, Tag 07A6;
blueprint, det-sp-tower-gluing, Levels paragraph
(blueprint: lem-sp-open-scalar-counit-square).

All categories are ordinary uncompleted unbounded constant-ring module derived categories.
The open extension, scalar restriction square and tensor square are the published ones.
Unit equations express identity comparisons on the open without identifying distinct
functors by definitional equality. Naturality is retained at the natural-transformation level.
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

/-- The exact open adjunction in the recorded sheafified extension coordinates.
The coordinate change is the unit-preserving uniqueness map `reductionOpenModel`.
Consequently this unit is the sectionwise open unit, descended termwise.
Source: Stacks Tags 03DI, 03DJ and 07A6
(blueprint: lem-sp-open-scalar-counit-square). -/
def openScalarCounitAdjunction (R : Type u) [CommRing R] [Finite R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicExtensionByZero j R).mapDerivedCategory ⊣ constantPullback (A := R) j :=
  (OpenScalarTensor.openAdj R j).ofNatIsoLeft (reductionOpenModel R j).symm

/-- Scalar multiplication identifies extension along the identity coefficient map with
identity. This is the unique left-adjoint comparison whose right-adjoint comparison is
the published sectionwise identity scalar unitor, so it retains counit normalization.
Source: Stacks Tag 07A6 (blueprint: lem-sp-open-scalar-counit-square). -/
def openScalarCounitScalarUnitor (R : Type u) [CommRing R] [Finite R]
    (W : Scheme.{u}) : scalarExtensionFunctor (RingHom.id R) W ≅ 𝟭 _ :=
  (proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := W) (RingHom.id R))).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight (sfOpenDerivedCoefficientRestrictionId W R).symm)

private theorem exactUnitOnComplexes
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (K : CochainComplex C ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  unfold Adjunction.mapExactDerivedCategory
  rw [Adjunction.localization_unit_app]
  simp only [Iso.symm_hom, CatCommSq.iso, Category.assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  simp

private theorem exactTranspose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (K : CochainComplex C ℤ) (N : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
    a.mapExactDerivedCategory.homEquiv _ _
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app N := by
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app N)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := G.mapDerivedCategoryFactors.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc, Functor.comp_obj, Category.comp_id] using congrArg
    (fun k ↦ k ≫ DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f))
    (exactUnitOnComplexes a K)

private theorem exactUniq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F H : C ⥤ D} {G U : D ⥤ C}
    [F.Additive] [H.Additive] [G.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : F ⊣ G) (b : H ⊣ U) (q : G ≅ U) :
    ((a.mapExactDerivedCategory.ofNatIsoRight
        (Functor.mapDerivedCategoryNatIso q)).leftAdjointUniq b.mapExactDerivedCategory) =
      Functor.mapDerivedCategoryNatIso ((a.ofNatIsoRight q).leftAdjointUniq b) := by
  let e := (a.ofNatIsoRight q).leftAdjointUniq b
  let qh : G.mapHomologicalComplex (.up ℤ) ≅ U.mapHomologicalComplex (.up ℤ) :=
    { hom := NatTrans.mapHomologicalComplex q.hom (.up ℤ)
      inv := NatTrans.mapHomologicalComplex q.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomologicalComplex_comp, q.hom_inv_id,
          NatTrans.mapHomologicalComplex_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomologicalComplex_comp, q.inv_hom_id,
          NatTrans.mapHomologicalComplex_id] }
  let eh := NatIso.mapHomologicalComplex e (.up ℤ)
  have hv (P : CochainComplex C ℤ) :
      (a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ (eh.hom.app P) ≫
        qh.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      (b.mapHomologicalComplex (.up ℤ)).unit.app P := by
    apply HomologicalComplex.Hom.ext
    funext n
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (a.ofNatIsoRight q) b (P.X n)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
    exact h
  have hr (K : CochainComplex D ℤ) :
      G.mapDerivedCategoryFactors.inv.app K ≫
          (Functor.mapDerivedCategoryNatIso q).hom.app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map (qh.hom.app K) ≫ U.mapDerivedCategoryFactors.inv.app K := by
    apply (cancel_epi (G.mapDerivedCategoryFactors.hom.app K)).1
    apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app K)).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    simpa only [qh, Functor.comp_obj, Category.comp_id] using
      Functor.mapDerivedCategoryNatIso_fac q K
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro P
  apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app P)).1
  rw [Functor.mapDerivedCategoryNatIso_fac]
  exact normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q)
    (a.mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ))
    a.mapExactDerivedCategory b.mapExactDerivedCategory
    (fun P ↦ F.mapDerivedCategoryFactors.hom.app P)
    (fun P ↦ H.mapDerivedCategoryFactors.hom.app P)
    (fun K ↦ G.mapDerivedCategoryFactors.inv.app K)
    (fun K ↦ U.mapDerivedCategoryFactors.inv.app K)
    (exactTranspose a) (exactTranspose b) qh (Functor.mapDerivedCategoryNatIso q)
    (fun P ↦ eh.hom.app P) hv hr P

private theorem derivedIdentityFactor
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app K := by
  have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj C
    ((HomotopyCategory.quotient C (.up ℤ)).obj K)
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  have h₁ : (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso C).inv.app
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  have h₃ : ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  rw [h₁, h₂, h₃, (𝟭 C).mapDerivedCategory.map_id, Category.id_comp] at h
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id] at h
  exact h

private theorem exactUnitWord
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) [IsIso a.unit] :
    (Functor.mapDerivedCategoryIdIso C).inv ≫
        (Functor.mapDerivedCategoryNatIso (asIso a.unit)).hom ≫
        (Functor.mapDerivedCategoryCompIso F G).hom = a.mapExactDerivedCategory.unit := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K))).1
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac, ← derivedIdentityFactor,
    Iso.inv_hom_id_app_assoc]
  exact (exactUnitOnComplexes a K).symm

/-- The open unit is invertible, and restriction determines any arrow whose source is
an open extension. The unit is the section-normalized one of `openScalarCounitAdjunction`;
its inverse is the sectionwise identification of restriction of extension with the input.
Source: Stacks Tags 03DI, 03DJ and 07A6
(blueprint: lem-sp-open-scalar-counit-square).

Proof: the intrinsic sheaf extension is fully faithful, hence its open unit is invertible.
Compute the localized exact unit on cochain representatives. The localization factors
identify it with sfIntrinsicDerivedOpenUnit, including the identity and composition
comparisons. Localization preserves the unit equation characterizing left-adjoint
uniqueness, by exactUniq; therefore reductionOpenModel preserves this same unit. Its
invertibility descends and is preserved by the right-adjoint coordinate isomorphism.
For an arrow with source j! M, equality of restrictions gives equality of adjuncts by
the unit formula. Injectivity of the Hom bijection proves equality of the arrows. -/
theorem openScalarCounitUnit (R : Type u) [CommRing R] [Finite R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (∀ M : proEtaleDerivedCategory X R,
      (openScalarCounitAdjunction R j).unit.app M ≫
          (openSquareDerivedPullbackModel R j).hom.app
            ((sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj M) =
        (sfIntrinsicDerivedOpenUnit R j).app M) ∧
    IsIso (openScalarCounitAdjunction R j).unit ∧
      ∀ (M : proEtaleDerivedCategory X R) (N : proEtaleDerivedCategory Z R),
        Function.Injective (fun h :
          (sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj M ⟶ N ↦
            (constantPullback (A := R) j).map h) := by
  let a := sfIntrinsicOpenAdjunction R j
  let b : proEtaleRingOpenExtension j (proEtaleConstantRing Z R)
      (proEtaleConstantRing X R) (proEtaleConstantRingComparison j R) ⊣
        proEtaleConstantRingPullback R j :=
    Adjunction.ofIsRightAdjoint (proEtaleConstantRingPullback R j)
  let q := openSquarePullbackModel R j
  have : (sfIntrinsicExtensionByZero j R).Full := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : (sfIntrinsicExtensionByZero j R).Faithful := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  have hw : a.mapExactDerivedCategory.unit = sfIntrinsicDerivedOpenUnit R j := by
    rw [← exactUnitWord a]
    rfl
  have hu : (openScalarCounitAdjunction R j).unit ≫
      Functor.whiskerLeft (sfIntrinsicExtensionByZero j R).mapDerivedCategory
        (openSquareDerivedPullbackModel R j).hom = a.mapExactDerivedCategory.unit := by
    ext M
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    unfold openScalarCounitAdjunction reductionOpenModel
    rw [← exactUniq (sfIntrinsicOpenAdjunction R j) b q.symm]
    simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
      Functor.whiskerRight_app, Iso.symm_hom]
    rw [Adjunction.leftAdjointUniq_inv_app]
    change (b.mapExactDerivedCategory.unit.app M ≫
      (proEtaleConstantRingPullback R j).mapDerivedCategory.map
        ((b.mapExactDerivedCategory.leftAdjointUniq
          (a.mapExactDerivedCategory.ofNatIsoRight
            (Functor.mapDerivedCategoryNatIso q.symm))).hom.app M)) ≫ _ = _
    rw [Adjunction.unit_leftAdjointUniq_hom_app]
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.mapDerivedCategoryNatIso_symm]
    simp only [Category.assoc, openSquareDerivedPullbackModel, q, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hi : IsIso a.mapExactDerivedCategory.unit := by
    rw [← exactUnitWord a]
    infer_instance
  have hi' : IsIso (openScalarCounitAdjunction R j).unit := by
    have : IsIso ((openScalarCounitAdjunction R j).unit ≫
        Functor.whiskerLeft (sfIntrinsicExtensionByZero j R).mapDerivedCategory
          (openSquareDerivedPullbackModel R j).hom) := by
      rw [hu]
      exact hi
    exact IsIso.of_isIso_comp_right _
      (Functor.whiskerLeft (sfIntrinsicExtensionByZero j R).mapDerivedCategory
        (openSquareDerivedPullbackModel R j).hom)
  refine ⟨?_, hi', ?_⟩
  · intro M
    exact NatTrans.congr_app (hu.trans hw) M
  · intro M N f g h
    apply ((openScalarCounitAdjunction R j).homEquiv M N).injective
    simp only [Adjunction.homEquiv_unit, h]


set_option backward.defeqAttrib.useBackward true in
private theorem scalarOpenTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) (K : C) :
    b.unit.app (SU.obj K) ≫ JB.map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      SU.map (a.unit.app K) ≫
        ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app (LA.obj K) := by
  apply (u.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((u.comp b).ofNatIsoRight q) (a.comp x) K
  change ((u.comp b).ofNatIsoRight q).unit.app K ≫
      (RX ⋙ JA).map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      (a.comp x).unit.app K at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc] at h
  have hn := q.hom.naturality
    (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [Functor.comp_obj] at h
  rw [← hn] at h
  have hm := unit_mateEquiv_symm x u (TwoSquare.mk _ _ _ _ q.inv) (LA.obj K)
  change JA.map (x.unit.app (LA.obj K)) ≫ q.inv.app (SX.obj (LA.obj K)) =
    u.unit.app (JA.obj (LA.obj K)) ≫ RU.map
      (((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app (LA.obj K)) at hm
  have hu := u.unit.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
  rw [← reassoc_of% hu, ← hm]
  apply (cancel_mono (q.hom.app (SX.obj (LA.obj K)))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj,
    Adjunction.comp_unit_app] using h

private theorem transportTensorUnit
    {UA ZA UB ZB : Type*} [Category UA] [Category ZA] [Category UB] [Category ZB]
    {LA IA : UA ⥤ ZA} {LB IB : UB ⥤ ZB} {vA : ZA ⥤ UA} {vB : ZB ⥤ UB}
    {TZ : ZA ⥤ ZB} {TX : UA ⥤ UB}
    (a : LA ⊣ vA) (b : LB ⊣ vB) (eA : IA ≅ LA) (eB : IB ≅ LB)
    (beta : LA ⋙ TZ ≅ TX ⋙ LB) (lam : TZ ⋙ vB ≅ vA ⋙ TX)
    (h : ∀ K, b.unit.app (TX.obj K) ≫ vB.map (beta.inv.app K) =
      TX.map (a.unit.app K) ≫ lam.inv.app (LA.obj K)) (K : UA) :
    (b.ofNatIsoLeft eB.symm).unit.app (TX.obj K) ≫ vB.map
        ((Functor.isoWhiskerRight eA TZ ≪≫ beta ≪≫
          Functor.isoWhiskerLeft TX eB.symm).inv.app K) =
      TX.map ((a.ofNatIsoLeft eA.symm).unit.app K) ≫ lam.inv.app (IA.obj K) := by
  simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Iso.symm_hom, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Iso.symm_inv,
    Functor.map_comp, Category.assoc]
  rw [← vB.map_comp_assoc, Iso.inv_hom_id_app, vB.map_id, Category.id_comp, reassoc_of% (h K)]
  have hn := lam.inv.naturality (eA.inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]

/-- The specified scalar restriction and tensor comparisons restrict to identity
comparisons, written with their canonical open units and scalar/pullback identifications.
Source: Stacks Tags 03DI, 0E8I and 07A6
(blueprint: lem-sp-open-scalar-counit-square).

Proof: openScalarRestrictionUnit supplies the first equation in the prescribed constant
pullback coordinates. For the tensor equation, apply scalarOpenTranspose to the two open
and two scalar adjunctions: the unit equation of left-adjoint uniqueness, the scalar mate
unit equation and naturality identify the inverse open comparison's transpose. Transport
both left adjoints through reductionOpenModel; naturality of inverse lambda and cancellation
of the two B-coordinate changes give precisely the second displayed equation. -/
theorem openScalarCounitRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (∀ L : proEtaleDerivedCategory X B,
      (openScalarCounitAdjunction A j).unit.app ((scalarRestriction φ X).obj L) ≫
          (constantPullback (A := A) j).map ((sfOpenRestrictionDerived j φ).hom.app L) ≫
          (OpenScalarTensor.rightSquare φ j).inv.app
            ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj L) =
        (scalarRestriction φ X).map ((openScalarCounitAdjunction B j).unit.app L)) ∧
    (∀ M : proEtaleDerivedCategory X A,
      (openScalarCounitAdjunction B j).unit.app ((scalarExtensionFunctor φ X).obj M) ≫
          (constantPullback (A := B) j).map ((reductionOpenScalarIso φ j).inv.app M) =
        (scalarExtensionFunctor φ X).map ((openScalarCounitAdjunction A j).unit.app M) ≫
          (tensorPullbackIso φ j).inv.app
            ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M)) := by
  refine ⟨?_, ?_⟩
  · exact openScalarRestrictionUnit φ j
  · intro M
    apply transportTensorUnit (OpenScalarTensor.openAdj A j)
      (OpenScalarTensor.openAdj B j) (reductionOpenModel A j) (reductionOpenModel B j)
      (openScalarIso φ j) (tensorPullbackIso φ j)
    intro K
    exact scalarOpenTranspose (OpenScalarTensor.openAdj A j)
      (OpenScalarTensor.openAdj B j)
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
      (OpenScalarTensor.rightSquare φ j) K

private theorem counitSquareOfUnits
    {UA ZA UB ZB : Type*} [Category UA] [Category ZA] [Category UB] [Category ZB]
    {JA : UA ⥤ ZA} {vA : ZA ⥤ UA} {JB : UB ⥤ ZB} {vB : ZB ⥤ UB}
    {TZ : ZA ⥤ ZB} {rZ : ZB ⥤ ZA} {TX : UA ⥤ UB} {rX : UB ⥤ UA}
    (a : JA ⊣ vA) (b : JB ⊣ vB) (z : TZ ⊣ rZ) (x : TX ⊣ rX)
    (q : vB ⋙ rX ≅ rZ ⋙ vA) (lam : TZ ⋙ vB ≅ vA ⋙ TX)
    (alpha : rX ⋙ JA ≅ JB ⋙ rZ) (beta : JA ⋙ TZ ≅ TX ⋙ JB)
    (ha : ∀ L, a.unit.app (rX.obj L) ≫ vA.map (alpha.hom.app L) ≫
      q.inv.app (JB.obj L) = rX.map (b.unit.app L))
    (hb : ∀ M, b.unit.app (TX.obj M) ≫ vB.map (beta.inv.app M) =
      TX.map (a.unit.app M) ≫ lam.inv.app (JA.obj M))
    (hc : ∀ N, lam.inv.app (rZ.obj N) ≫ vB.map (z.counit.app N) =
      TX.map (q.inv.app N) ≫ x.counit.app (vB.obj N)) (L : UB) :
    TZ.map (alpha.hom.app L) ≫ z.counit.app (JB.obj L) =
      beta.hom.app (rX.obj L) ≫ JB.map (x.counit.app L) := by
  apply (cancel_epi (beta.inv.app (rX.obj L))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [reassoc_of% (hb (rX.obj L))]
  have hn := lam.inv.naturality (alpha.hom.app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, hc]
  rw [← TX.map_comp_assoc, ← TX.map_comp_assoc, Category.assoc, ha]
  have he := x.counit.naturality (b.unit.app L)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at he
  rw [he]
  exact b.unit.naturality (x.counit.app L)

/-- Open extension and scalar restriction preserve the specified derived scalar counit.
This equality of natural transformations includes the equation at every ambient L and
its naturality, with no boundedness, flatness, constructibility or Tor condition.
Source: Stacks Tags 0E8I and 07A6; det-sp-tower-gluing, Levels paragraph
(blueprint: lem-sp-open-scalar-counit-square).

Proof: put f = epsilon_Z(j!_B L) after T_Z(a_L), and g = j!_B(epsilon_X L) after E.
Inverse lambda is definitionally the inverse scalar-adjunction mate of rightSquare.inv.
The Mathlib mate-counit equation therefore gives its scalar counit formula directly.
Precompose f and g with E inverse, and apply the B-open Hom equivalence. The second
equation of openScalarCounitRestriction rewrites the source unit. Naturality of inverse
lambda, its mate-counit formula, the first restriction equation and scalar-counit
naturality make the adjuncts equal. Injectivity and cancellation give f = g. Componentwise
extensionality gives equality of natural transformations for all unbounded derived objects. -/
theorem openScalarCounitSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Functor.whiskerRight (sfOpenRestrictionDerived j φ).hom (scalarExtensionFunctor φ Z) ≫
        Functor.whiskerLeft (sfIntrinsicExtensionByZero j B).mapDerivedCategory
          (proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := Z) φ)).counit =
      Functor.whiskerLeft (scalarRestriction φ X) (reductionOpenScalarIso φ j).hom ≫
        Functor.whiskerRight (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := X) φ)).counit
            (sfIntrinsicExtensionByZero j B).mapDerivedCategory := by
  ext L
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply counitSquareOfUnits (openScalarCounitAdjunction A j)
    (openScalarCounitAdjunction B j)
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
    (OpenScalarTensor.rightSquare φ j) (tensorPullbackIso φ j)
    (sfOpenRestrictionDerived j φ) (reductionOpenScalarIso φ j)
    (openScalarCounitRestriction φ j).1 (openScalarCounitRestriction φ j).2
  intro N
  exact (mateEquiv_counit_symm
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
    (TwoSquare.mk _ _ _ _ (OpenScalarTensor.rightSquare φ j).inv) N).symm


private theorem identityOfCounitSquare
    {U Z : Type*} [Category U] [Category Z] (J : U ⥤ Z)
    {TX rX : U ⥤ U} {TZ rZ : Z ⥤ Z} (x : TX ⊣ rX) (z : TZ ⊣ rZ)
    (iX : rX ≅ 𝟭 U) (iZ : rZ ≅ 𝟭 Z) (eX : TX ≅ 𝟭 U) (eZ : TZ ≅ 𝟭 Z)
    (alpha : rX ⋙ J ≅ J ⋙ rZ) (beta : J ⋙ TZ ≅ TX ⋙ J)
    (ha : ∀ L, alpha.hom.app L ≫ iZ.hom.app (J.obj L) = J.map (iX.hom.app L))
    (hx : ∀ L, x.counit.app L = eX.hom.app (rX.obj L) ≫ iX.hom.app L)
    (hz : ∀ L, z.counit.app L = eZ.hom.app (rZ.obj L) ≫ iZ.hom.app L)
    (hs : ∀ L, TZ.map (alpha.hom.app L) ≫ z.counit.app (J.obj L) =
      beta.hom.app (rX.obj L) ≫ J.map (x.counit.app L)) (K : U) :
    beta.hom.app K ≫ J.map (eX.hom.app K) = eZ.hom.app (J.obj K) := by
  have he (L : U) : beta.hom.app (rX.obj L) ≫ J.map (eX.hom.app (rX.obj L)) =
      eZ.hom.app (J.obj (rX.obj L)) := by
    apply (cancel_mono (J.map (iX.hom.app L))).1
    rw [Category.assoc, ← J.map_comp, ← hx, ← hs, hz]
    have hn := eZ.hom.naturality (alpha.hom.app L)
    dsimp only [Functor.id_map] at hn
    rw [reassoc_of% hn, ha]
  apply (cancel_epi (TZ.map (J.map (iX.hom.app K)))).1
  rw [← Category.assoc]
  have hn := beta.hom.naturality (iX.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [hn, Category.assoc, ← J.map_comp]
  have hn' := eX.hom.naturality (iX.hom.app K)
  dsimp only [Functor.id_map, Functor.id_obj] at hn'
  rw [hn', J.map_comp, ← Category.assoc, he]
  exact (eZ.hom.naturality (J.map (iX.hom.app K))).symm

/-- Identity coefficient maps give identity comparisons under the canonical scalar
unitors, and their scalar counit is the scalar multiplication unitor.
Source: Stacks Tag 07A6 (blueprint: lem-sp-open-scalar-counit-square).

Proof: the scalar restriction comparison is identity on every extension-presheaf section;
its termwise localization obeys the published sfOpenRestriction_derived_id law.
The scalar counit is the scalar unitor followed by the restriction unitor, by the counit
formula for left-adjoint uniqueness. Substitute these two facts into openScalarCounitSquare
and use naturality of the ambient scalar unitor. Cancelling the invertible restriction
unitor proves the tensor identity on scalar restrictions. Naturality at the restriction
unitor of any object extends this to every object. Empty opens, whole opens and zero
complexes obey the same equations. -/
theorem openScalarCounitIdentity (R : Type u) [CommRing R] [Finite R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (∀ L : proEtaleDerivedCategory X R,
      (sfOpenRestrictionDerived j (RingHom.id R)).hom.app L ≫
          (sfOpenDerivedCoefficientRestrictionId Z R).hom.app
            ((sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj L) =
        (sfIntrinsicExtensionByZero j R).mapDerivedCategory.map
          ((sfOpenDerivedCoefficientRestrictionId X R).hom.app L)) ∧
    (∀ M : proEtaleDerivedCategory X R,
      (reductionOpenScalarIso (RingHom.id R) j).hom.app M ≫
          (sfIntrinsicExtensionByZero j R).mapDerivedCategory.map
            ((openScalarCounitScalarUnitor R X).hom.app M) =
        (openScalarCounitScalarUnitor R Z).hom.app
          ((sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj M)) ∧
    (∀ (W : Scheme.{u}) (L : proEtaleDerivedCategory W R),
      (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := W) (RingHom.id R))).counit.app L =
        (openScalarCounitScalarUnitor R W).hom.app
            ((scalarRestriction (RingHom.id R) W).obj L) ≫
          (sfOpenDerivedCoefficientRestrictionId W R).hom.app L) := by
  have hc (W : Scheme.{u}) (L : proEtaleDerivedCategory W R) :
      (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := W) (RingHom.id R))).counit.app L =
        (openScalarCounitScalarUnitor R W).hom.app
            ((scalarRestriction (RingHom.id R) W).obj L) ≫
          (sfOpenDerivedCoefficientRestrictionId W R).hom.app L := by
    simpa only [openScalarCounitScalarUnitor, Adjunction.ofNatIsoRight_counit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.id_map, Iso.symm_inv,
      Adjunction.id_counit, NatTrans.id_app, Category.comp_id] using
      (Adjunction.leftAdjointUniq_hom_app_counit
        (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := W) (RingHom.id R)))
        (Adjunction.id.ofNatIsoRight (sfOpenDerivedCoefficientRestrictionId W R).symm) L).symm
  refine ⟨sfOpenRestriction_derived_id j R, ?_, hc⟩
  intro M
  apply identityOfCounitSquare (sfIntrinsicExtensionByZero j R).mapDerivedCategory
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := X) (RingHom.id R)))
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := Z) (RingHom.id R)))
    (sfOpenDerivedCoefficientRestrictionId X R) (sfOpenDerivedCoefficientRestrictionId Z R)
    (openScalarCounitScalarUnitor R X) (openScalarCounitScalarUnitor R Z)
    (sfOpenRestrictionDerived j (RingHom.id R)) (reductionOpenScalarIso (RingHom.id R) j)
    (sfOpenRestriction_derived_id j R) (hc X) (hc Z)
  intro L
  exact congrArg (fun t ↦ t.app L) (openScalarCounitSquare (RingHom.id R) j)


end AlgebraicGeometry.ProEtale
