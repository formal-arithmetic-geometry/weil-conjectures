/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Paper.MateOpenRestriction
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
import Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization
import Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.CategoryTheory.ExactDerivedAdjunction
import WeilConjectures.Compactification.RefinementUniqueness

/-! # Source-open locality of the exceptional scalar mate

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph
(blueprint: lem-sp-open-exceptional-scalar-locality).

The equality is written after the adjunction-preserving source-open identification.
For a compactification X -> Z -> Y, its restriction U -> Z -> Y represents the
compactification of f j in these coordinates. The compositor is constructed inline from
the composite open adjunctions by the unique unit-preserving left-adjoint comparison.
All membership witnesses only restrict the specified ambient functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.OpenScalarLocality

/-- The existing compact-support functor restricted by a membership witness.
This is only the standard ObjectProperty lift, with no new functor construction.
Source: Locality paragraph, F_h (blueprint: lem-sp-open-exceptional-scalar-locality). -/
abbrev support (R : Type u) [CommRing R] [Finite R]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y)
    (h : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R i p).obj M.obj)) :=
  (spFiniteConstructibleTor Y R).lift
    ((spFiniteConstructibleTor X R).ι ⋙ reductionCompactSupport R i p) h

/-- The given exceptional adjunction, with unchanged ambient compact-support functor.
Source: Locality paragraph, F_h adjoint to G_h
(blueprint: lem-sp-open-exceptional-scalar-locality). -/
structure SupportAdjunction (R : Type u) [CommRing R] [Finite R]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y) where
  preserves : ∀ M : spFiniteConstructibleTorCategory X R,
    spFiniteConstructibleTor Y R ((reductionCompactSupport R i p).obj M.obj)
  right : spFiniteConstructibleTorCategory Y R ⥤ spFiniteConstructibleTorCategory X R
  adjunction : support R i p preserves ⊣ right

/-- Restrict the actual derived open extension. Source: Locality paragraph, J_R
(blueprint: lem-sp-open-exceptional-scalar-locality). -/
def extension (R : Type u) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj L.obj)) :=
  (spFiniteConstructibleTor X R).lift
    ((spFiniteConstructibleTor U R).ι ⋙ sfIntrinsicDerivedOpen R j) h

/-- Restrict the canonical constant-coefficient inverse image. Source: Locality
paragraph, U_R = j^*. (blueprint: lem-sp-open-exceptional-scalar-locality). -/
def restriction (R : Type u) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor U R ((proEtaleConstantRingDerivedPullback R j).obj M.obj)) :=
  (spFiniteConstructibleTor U R).lift
    ((spFiniteConstructibleTor X R).ι ⋙ proEtaleConstantRingDerivedPullback R j) h

/-- The actual open adjunction, localized termwise, with the canonical unit-preserving
change from realization to constant-section pullback coordinates, then restricted
along full inclusions. Source: Locality paragraph, J_R adjoint to U_R and counit v_R
(blueprint: lem-sp-open-exceptional-scalar-locality). -/
def openAdjunction (R : Type u) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (hJ : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj L.obj))
    (hU : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor U R ((proEtaleConstantRingDerivedPullback R j).obj M.obj)) :
    extension R j hJ ⊣ restriction R j hU :=
  letI : CatCommSq
      ((sfIntrinsicExtensionByZero j R).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (sfIntrinsicDerivedOpen R j) :=
    ⟨(sfIntrinsicExtensionByZero j R).mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq
      ((sfIntrinsicPullback R j).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (sfIntrinsicDerivedPullback R j) :=
    ⟨(sfIntrinsicPullback R j).mapDerivedCategoryFactors.symm⟩
  ((((sfIntrinsicOpenAdjunction R j).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (sfIntrinsicDerivedOpen R j) (sfIntrinsicDerivedPullback R j)).ofNatIsoRight
      (openSquareDerivedPullbackModel R j).symm).restrictFullyFaithful
      (spFiniteConstructibleTor U R).fullyFaithfulι
      (spFiniteConstructibleTor X R).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- The canonical left-adjoint composition comparison for the restricted
compactification, constructed inline by uniqueness of left adjoints for the composite
open adjunctions and descended termwise.
Source: Locality paragraph, F_g = F_f J_R
(blueprint: lem-sp-open-exceptional-scalar-locality). -/
def supportComposition (R : Type u) [CommRing R] [Finite R]
    {U X Z Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : X ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y)
    (a : SupportAdjunction R i p)
    (hJ : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj L.obj))
    (hG : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R (j ≫ i) p).obj L.obj)) :
    support R (j ≫ i) p hG ≅ extension R j hJ ⋙ support R i p a.preserves :=
  Functor.fullyFaithfulCancelRight (spFiniteConstructibleTor Y R).ι
    (Functor.isoWhiskerLeft (spFiniteConstructibleTor U R).ι
      (Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso
          (((((sfIntrinsicOpenAdjunction R j).comp (sfIntrinsicOpenAdjunction R i)).ofNatIsoRight
            (sfIntrinsicPullbackComp R j i).symm).leftAdjointUniq
              (sfIntrinsicOpenAdjunction R (j ≫ i))).symm) ≪≫
          Functor.mapDerivedCategoryCompIso
            (sfIntrinsicExtensionByZero j R) (sfIntrinsicExtensionByZero i R))
        (directImageConstantPush R p) ≪≫ Functor.associator _ _ _))

/-- The composite adjunction in the actual compactification coordinates. Thus its
right adjoint is U_R G_f, and its counit is precisely epsilon_f F_f(v_R), with
supportComposition inserted. Source: Locality paragraph and Stacks 0DV0
(blueprint: lem-sp-open-exceptional-scalar-locality). -/
def composite (R : Type u) [CommRing R] [Finite R]
    {U X Z Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : X ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y)
    (a : SupportAdjunction R i p)
    (hJ : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj L.obj))
    (hU : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor U R ((proEtaleConstantRingDerivedPullback R j).obj M.obj))
    (hG : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R (j ≫ i) p).obj L.obj)) :
    SupportAdjunction R (j ≫ i) p where
  preserves := hG
  right := a.right ⋙ restriction R j hU
  adjunction := ((openAdjunction R j hJ hU).comp a.adjunction).ofNatIsoLeft
    (supportComposition R j i p a hJ hG).symm

/-- The specified exceptional scalar component, defined by the B-adjunction Hom
bijection applied to the inverse of the actual b followed by the extended A-counit.
The isomorphism witness supplies only the inverse of this specified map. No inverse
of the exceptional component is used. Source: defining display before Locality
(blueprint: lem-sp-open-exceptional-scalar-locality). -/
def component {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y)
    (a : SupportAdjunction A i p) (b : SupportAdjunction B i p)
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hb : ∀ M : spFiniteConstructibleTorCategory X A,
      IsIso ((reductionDirectImageComparison φ i p).app M.obj))
    (K : spFiniteConstructibleTorCategory Y A) :
    (scalarExtensionFunctor φ X).obj (a.right.obj K).obj ⟶
      (b.right.obj ⟨(scalarExtensionFunctor φ Y).obj K.obj, hSY K⟩).obj :=
  (b.adjunction.homEquiv
    ⟨(scalarExtensionFunctor φ X).obj (a.right.obj K).obj, hSX (a.right.obj K)⟩
    ⟨(scalarExtensionFunctor φ Y).obj K.obj, hSY K⟩
    (ObjectProperty.homMk
      (@inv _ _ _ _ ((reductionDirectImageComparison φ i p).app (a.right.obj K).obj)
        (hb (a.right.obj K)) ≫
        (scalarExtensionFunctor φ Y).map (a.adjunction.counit.app K).hom))).hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem counit_calculation
    {XA XB YA YB : Type*}
    [Category XA] [Category XB] [Category YA] [Category YB]
    (FA : XA ⥤ YA) (FB : XB ⥤ YB) (TX : XA ⥤ XB) (TY : YA ⥤ YB)
    (b : FA ⋙ TY ⟶ TX ⋙ FB)
    {L M : XA} {N W : XB} {K D : YA} {E : YB}
    (v : L ⟶ M) (εA : FA.obj M ⟶ K) (εB : FB.obj N ⟶ TY.obj K)
    (r : TX.obj M ⟶ N) (q : TX.obj L ≅ W)
    (sA : D ⟶ FA.obj L) (sB : E ⟶ FB.obj W)
    (bg : TY.obj D ⟶ E) [IsIso bg] [IsIso (b.app M)]
    (t : W ⟶ N)
    (ht : t = q.inv ≫ TX.map v ≫ r)
    (hr : FB.map r ≫ εB = inv (b.app M) ≫ TY.map εA)
    (hs : TY.map sA ≫ b.app L ≫ FB.map q.hom = bg ≫ sB) :
    inv bg ≫ TY.map (sA ≫ FA.map v ≫ εA) = sB ≫ FB.map t ≫ εB := by
  apply (cancel_epi bg).1
  simp only [IsIso.hom_inv_id_assoc, Functor.map_comp]
  rw [← Category.assoc bg sB, ← hs, ht]
  simp only [FB.map_comp, Category.assoc]
  rw [← FB.map_comp_assoc, q.hom_inv_id, FB.map_id, Category.id_comp]
  have hn := b.naturality v
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, hr]
  simp only [IsIso.hom_inv_id_assoc]

private theorem exact_counit_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.Additive] [L₂.Additive] [R₁.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂) (r : R₁ ≅ R₂)
    (he : ∀ K, e.hom.app (R₁.obj K) ≫ L₂.map (r.hom.app K) ≫ b.counit.app K =
      a.counit.app K) (K : DerivedCategory D) :
    (Functor.mapDerivedCategoryNatIso e).hom.app (R₁.mapDerivedCategory.obj K) ≫
      L₂.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso r).hom.app K) ≫
      b.mapExactDerivedCategory.counit.app K = a.mapExactDerivedCategory.counit.app K := by
  suffices h : Functor.whiskerLeft R₁.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso e).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso r).hom L₂.mapDerivedCategory ≫
      b.mapExactDerivedCategory.counit = a.mapExactDerivedCategory.counit from
    congr_app h K
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso D (.up ℤ))
  intro P
  let : CatCommSq (L₁.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q L₁.mapDerivedCategory := ⟨L₁.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (R₁.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q R₁.mapDerivedCategory := ⟨R₁.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (L₂.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q L₂.mapDerivedCategory := ⟨L₂.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (R₂.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q R₂.mapDerivedCategory := ⟨R₂.mapDerivedCategoryFactors.symm⟩
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app]
  change _ ≫ _ ≫ (L₂.mapDerivedCategory.map (R₂.mapDerivedCategoryFactors.hom.app P) ≫
      L₂.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).counit.app P)) =
    L₁.mapDerivedCategory.map (R₁.mapDerivedCategoryFactors.hom.app P) ≫
      L₁.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P)
  rw [← cancel_epi (L₁.mapDerivedCategory.map (R₁.mapDerivedCategoryFactors.inv.app P))]
  simp only [← L₁.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [(Functor.mapDerivedCategoryNatIso e).hom.naturality_assoc
    (R₁.mapDerivedCategoryFactors.inv.app P)]
  have hrf := congrArg L₂.mapDerivedCategory.map
    (Functor.mapDerivedCategoryNatIso_fac r P)
  simp only [Functor.map_comp] at hrf
  rw [reassoc_of% hrf]
  simp only [← L₂.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  rw [L₂.mapDerivedCategoryFactors_hom_naturality_assoc]
  erw [Functor.mapDerivedCategoryNatIso_fac_assoc e]
  simp only [← DerivedCategory.Q.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  ext q
  simpa only [Functor.mapHomologicalComplex, Functor.id_obj,
    Functor.mapHomologicalComplex_obj_X, NatTrans.mapHomologicalComplex_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_counit_app_f] using he (P.X q)

private theorem open_counit_model (R : Type u) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (hJ : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj L.obj))
    (hU : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor U R ((proEtaleConstantRingDerivedPullback R j).obj M.obj))
    (M : spFiniteConstructibleTorCategory X R) :
    ((openAdjunction R j hJ hU).counit.app M).hom =
      (reductionOpenModel R j).hom.app
          ((proEtaleConstantRingDerivedPullback R j).obj M.obj) ≫
        (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X R)
          (proEtaleConstantRing U R) (proEtaleConstantRingComparison j R)).counit.app
            M.obj := by
  let a := sfIntrinsicOpenAdjunction R j
  let b : proEtaleRingOpenExtension j (proEtaleConstantRing X R)
      (proEtaleConstantRing U R) (proEtaleConstantRingComparison j R) ⊣
      proEtaleConstantRingPullback R j := Adjunction.ofIsRightAdjoint _
  let r := (openSquarePullbackModel R j).symm
  let e := (a.ofNatIsoRight r).leftAdjointUniq b
  have he (N : proEtaleRingModules X (proEtaleConstantRing X R)) :
      e.hom.app ((sfIntrinsicPullback R j).obj N) ≫
          (proEtaleRingOpenExtension j (proEtaleConstantRing X R)
            (proEtaleConstantRing U R) (proEtaleConstantRingComparison j R)).map (r.hom.app N) ≫
          b.counit.app N = a.counit.app N := by
    rw [← e.hom.naturality_assoc]
    have ht := (a.ofNatIsoRight r).leftAdjointUniq_hom_app_counit b N
    simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
      Functor.whiskerRight_app] at ht
    rw [ht]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  have hd := exact_counit_transport a b e r he M.obj
  have hr := Adjunction.map_restrictFullyFaithful_counit_app
    (a.mapExactDerivedCategory.ofNatIsoRight
      (openSquareDerivedPullbackModel R j).symm)
    (spFiniteConstructibleTor U R).fullyFaithfulι
    (spFiniteConstructibleTor X R).fullyFaithfulι
    (L := extension R j hJ) (R := restriction R j hU) (Iso.refl _) (Iso.refl _) M
  change ((spFiniteConstructibleTor X R).ι.map
    ((openAdjunction R j hJ hU).counit.app M)) = _
  erw [hr]
  simp only [Iso.refl_inv, NatTrans.id_app]
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_inv]
  erw [Category.id_comp, (sfIntrinsicExtensionByZero j R).mapDerivedCategory.map_id,
    Category.id_comp]
  change (sfIntrinsicExtensionByZero j R).mapDerivedCategory.map
      ((openSquareDerivedPullbackModel R j).hom.app M.obj) ≫
    a.mapExactDerivedCategory.counit.app M.obj = _
  rw [← hd]
  have hn := (Functor.mapDerivedCategoryNatIso e).hom.naturality
    ((openSquareDerivedPullbackModel R j).hom.app M.obj)
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc]
  change _ = _
  simp only [openSquareDerivedPullbackModel, r, Functor.mapDerivedCategoryNatIso_symm,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl


attribute [local irreducible] reductionDerivedChange
  proEtaleRingDerivedOpenAdjunction
  reductionDirectImageComparison openScalarIso directImageScalarPullbackIso

private theorem open_scalar_counit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (hJA : ∀ L : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor X A ((sfIntrinsicDerivedOpen A j).obj L.obj))
    (hUA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor U A ((proEtaleConstantRingDerivedPullback A j).obj M.obj))
    (hJB : ∀ L : spFiniteConstructibleTorCategory U B,
      spFiniteConstructibleTor X B ((sfIntrinsicDerivedOpen B j).obj L.obj))
    (hUB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor U B ((proEtaleConstantRingDerivedPullback B j).obj M.obj))
    (M : spFiniteConstructibleTorCategory X A)
    (hM : spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (h : (openExtension (A := B) j).map
        ((directImageScalarPullbackIso φ j).inv.app M.obj) ≫
      (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X B)
        (proEtaleConstantRing U B) (proEtaleConstantRingComparison j B)).counit.app
          ((scalarExtensionFunctor φ X).obj M.obj) =
      (openScalarIso φ j).inv.app
          ((proEtaleConstantRingDerivedPullback A j).obj M.obj) ≫
        (scalarExtensionFunctor φ X).map
          ((proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X A)
            (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A)).counit.app
              M.obj)) :
    (sfIntrinsicDerivedOpen B j).map ((directImageScalarPullbackIso φ j).inv.app M.obj) ≫
      ((openAdjunction B j hJB hUB).counit.app
        ⟨(scalarExtensionFunctor φ X).obj M.obj, hM⟩).hom =
      (reductionOpenScalarIso φ j).inv.app
          ((proEtaleConstantRingDerivedPullback A j).obj M.obj) ≫
        (scalarExtensionFunctor φ X).map
          ((openAdjunction A j hJA hUA).counit.app M).hom := by
  unfold scalarExtensionFunctor at *
  rw [open_counit_model, open_counit_model]
  erw [(reductionOpenModel B j).hom.naturality_assoc
    ((directImageScalarPullbackIso φ j).inv.app M.obj), h]
  simp only [reductionOpenScalarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  simp only [scalarExtensionFunctor, Functor.comp_obj]
  rw [← (scalarExtension φ X).map_comp_assoc, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]


private theorem refinement_refl (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f) :
    OpenInverseTranspose.refinement R c c = Iso.refl _ := by
  apply (OpenInverseTranspose.canonicalRefinement_existsUnique R c c).unique
  · exact (OpenInverseTranspose.canonicalRefinement_existsUnique R c c).exists.choose_spec
  · intro Q E s
    have hr := Compactification.Refinement.ext_of_isSchemeTheoreticallyDominant
      (Compactification.isSchemeTheoreticallyDominant_inf_i c c)
      (Compactification.infFst c c) (Compactification.infSnd c c)
    have he : Etale.rightDerivedLowerShriekOfCompactificationIso
        (ULift.{u + 1, u} R) c c = Iso.refl _ := by
      dsimp only [Etale.rightDerivedLowerShriekOfCompactificationIso]
      have hc : asIso (Etale.rightDerivedLowerShriekOfCompactificationComparison
          (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (Compactification.infFst c c)
          (Compactification.isPullback_infFst c c)) =
          asIso (Etale.rightDerivedLowerShriekOfCompactificationComparison
          (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (Compactification.infSnd c c)
          (Compactification.isPullback_infSnd c c)) := by
        congr 2
      rw [hc, Iso.self_symm_id]
    dsimp only [OpenInverseTranspose.refinementModel, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
    rw [he]
    simp only [Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id]
    erw [← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    rfl

private theorem eq_app_of_iso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α β : F ⟶ G)
    {M N : C} (e : M ≅ N) (h : α.app N = β.app N) : α.app M = β.app M := by
  apply (cancel_mono (G.map e.hom)).1
  rw [← α.naturality, ← β.naturality, h]

private noncomputable def ambientComposition (R : Type u) [CommRing R] [Finite R]
    {U X Z Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : X ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y) :
    reductionCompactSupport R (j ≫ i) p ≅
      sfIntrinsicDerivedOpen R j ⋙ reductionCompactSupport R i p :=
  Functor.isoWhiskerRight (sfIntrinsicDerivedOpenComp R j i)
    (directImageConstantPush R p) ≪≫ Functor.associator _ _ _

private theorem supportComposition_hom (R : Type u) [CommRing R] [Finite R]
    {U X Z Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : X ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y)
    (a : SupportAdjunction R i p)
    (hJ : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj L.obj))
    (hG : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R (j ≫ i) p).obj L.obj))
    (L : spFiniteConstructibleTorCategory U R) :
    ((supportComposition R j i p a hJ hG).hom.app L).hom =
      (ambientComposition R j i p).hom.app L.obj := by
  change ((spFiniteConstructibleTor Y R).ι.map
    ((supportComposition R j i p a hJ hG).hom.app L)) = _
  simp only [supportComposition, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  rfl

private theorem inverseComposition_hom (R : Type u) [CommRing R] [Finite R]
    {U X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (c : Compactification f)
    (hF : ∀ L : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R c.i c.g).obj L.obj))
    (hJ : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj L.obj))
    (hG : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor Y R
        ((reductionCompactSupport R (j ≫ c.i) c.g).obj L.obj))
    (L : spFiniteConstructibleTorCategory U R) :
    ((OpenInverseTranspose.composition R j c (c.precomp j) hF hJ hG).hom.app L).hom =
      (ambientComposition R j c.i c.g).hom.app L.obj := by
  change ((spFiniteConstructibleTor Y R).ι.map
    ((OpenInverseTranspose.composition R j c (c.precomp j) hF hJ hG).hom.app L)) = _
  simp only [OpenInverseTranspose.composition, refinement_refl,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  erw [Category.id_comp]
  rfl

private theorem composite_counit (R : Type u) [CommRing R] [Finite R]
    {U X Z Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : X ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y)
    (a : SupportAdjunction R i p)
    (hJ : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj L.obj))
    (hU : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor U R ((proEtaleConstantRingDerivedPullback R j).obj M.obj))
    (hG : ∀ L : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R (j ≫ i) p).obj L.obj))
    (K : spFiniteConstructibleTorCategory Y R) :
    ((composite R j i p a hJ hU hG).adjunction.counit.app K).hom =
      (ambientComposition R j i p).hom.app
          ((proEtaleConstantRingDerivedPullback R j).obj (a.right.obj K).obj) ≫
        (reductionCompactSupport R i p).map
          ((openAdjunction R j hJ hU).counit.app (a.right.obj K)).hom ≫
        (a.adjunction.counit.app K).hom := by
  change ((spFiniteConstructibleTor Y R).ι.map
    ((composite R j i p a hJ hU hG).adjunction.counit.app K)) = _
  simp only [composite, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_inv, Adjunction.comp_counit_app,
    Functor.map_comp]
  simp only [ObjectProperty.ι_map]
  rw [supportComposition_hom]
  rfl

private theorem finiteTor_of_iso (R : Type u) [CommRing R] [Finite R]
    (T : Scheme.{u}) {M N : proEtaleDerivedCategory T R} (e : M ≅ N)
    (h : spFiniteConstructibleTor T R M) : spFiniteConstructibleTor T R N := by
  rcases h with ⟨⟨a, b, hab, hbd⟩, hc, a', b', hab', ht⟩
  refine ⟨⟨a, b, hab, fun q hq ↦ (hbd q hq).of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso e.symm)⟩, ?_, a', b', hab', ?_⟩
  · intro q
    rw [proEtaleModuleRestriction_constructible_iff]
    have hcq := hc q
    rw [proEtaleModuleRestriction_constructible_iff] at hcq
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T R).mapIso
        ((DerivedCategory.homologyFunctor _ q).mapIso e)) hcq
  · intro L P hL v hv hP F q hq
    exact ht L P ⟨hL.some ≪≫ e.symm⟩ v hv hP F q hq

private theorem component_counit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i] (p : Z ⟶ Y)
    (a : SupportAdjunction A i p) (b : SupportAdjunction B i p)
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hb : ∀ M : spFiniteConstructibleTorCategory X A,
      IsIso ((reductionDirectImageComparison φ i p).app M.obj))
    (K : spFiniteConstructibleTorCategory Y A) :
    (reductionCompactSupport B i p).map (component φ i p a b hSX hSY hb K) ≫
        (b.adjunction.counit.app ⟨(scalarExtensionFunctor φ Y).obj K.obj, hSY K⟩).hom =
      @inv _ _ _ _ ((reductionDirectImageComparison φ i p).app (a.right.obj K).obj)
        (hb (a.right.obj K)) ≫
        (scalarExtensionFunctor φ Y).map (a.adjunction.counit.app K).hom := by
  let S : spFiniteConstructibleTorCategory X B :=
    ⟨(scalarExtensionFunctor φ X).obj (a.right.obj K).obj, hSX (a.right.obj K)⟩
  let T : spFiniteConstructibleTorCategory Y B :=
    ⟨(scalarExtensionFunctor φ Y).obj K.obj, hSY K⟩
  let t : (support B i p b.preserves).obj S ⟶ T := ObjectProperty.homMk
    (@inv _ _ _ _ ((reductionDirectImageComparison φ i p).app (a.right.obj K).obj)
      (hb (a.right.obj K)) ≫
      (scalarExtensionFunctor φ Y).map (a.adjunction.counit.app K).hom)
  have he := (b.adjunction.homEquiv S T).symm_apply_apply t
  rw [Adjunction.homEquiv_counit] at he
  exact congrArg (fun z ↦ z.hom) he



private theorem coefficient_composition
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (_hp : 0 < pchar) (_hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {U X Z Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
    (i : X ⟶ Z) [IsOpenImmersion i] [i.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (_hf : i ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (_hA : (ℓ ^ n : A) = 0) (_hB : (ℓ ^ n : B) = 0)
    (a : SupportAdjunction A i p) (b : SupportAdjunction B i p)
    (hJA : ∀ L : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor X A ((sfIntrinsicDerivedOpen A j).obj L.obj))
    (hUA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor U A ((proEtaleConstantRingDerivedPullback A j).obj M.obj))
    (hGA : ∀ L : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A (j ≫ i) p).obj L.obj))
    (hJB : ∀ L : spFiniteConstructibleTorCategory U B,
      spFiniteConstructibleTor X B ((sfIntrinsicDerivedOpen B j).obj L.obj))
    (hUB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor U B ((proEtaleConstantRingDerivedPullback B j).obj M.obj))
    (hGB : ∀ L : spFiniteConstructibleTorCategory U B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B (j ≫ i) p).obj L.obj))
    (hSU : ∀ L : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor U B ((scalarExtensionFunctor φ U).obj L.obj))
    (_hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (_hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hbf : ∀ M : spFiniteConstructibleTorCategory X A,
      IsIso ((reductionDirectImageComparison φ i p).app M.obj))
    (hbg : ∀ L : spFiniteConstructibleTorCategory U A,
      IsIso ((reductionDirectImageComparison φ (j ≫ i) p).app L.obj))
    (K : spFiniteConstructibleTorCategory Y A) :
    (scalarExtensionFunctor φ Y).map
        ((ambientComposition A j i p).hom.app
          ((proEtaleConstantRingDerivedPullback A j).obj (a.right.obj K).obj)) ≫
      (reductionDirectImageComparison φ i p).app
        ((sfIntrinsicDerivedOpen A j).obj
          ((proEtaleConstantRingDerivedPullback A j).obj (a.right.obj K).obj)) ≫
      (reductionCompactSupport B i p).map ((reductionOpenScalarIso φ j).hom.app
        ((proEtaleConstantRingDerivedPullback A j).obj (a.right.obj K).obj)) =
      (reductionDirectImageComparison φ (j ≫ i) p).app
          ((proEtaleConstantRingDerivedPullback A j).obj (a.right.obj K).obj) ≫
        (ambientComposition B j i p).hom.app
          ((scalarExtensionFunctor φ U).obj
            ((proEtaleConstantRingDerivedPullback A j).obj (a.right.obj K).obj)) := by
  let c : Compactification f := ⟨Z, p, i, _hf.symm, inferInstance, inferInstance⟩
  let hUA' : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor U A ((sfIntrinsicDerivedPullback A j).obj M.obj) :=
    fun M ↦ finiteTor_of_iso A U ((openSquareDerivedPullbackModel A j).app M.obj) (hUA M)
  let hUB' : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor U B ((sfIntrinsicDerivedPullback B j).obj M.obj) :=
    fun M ↦ finiteTor_of_iso B U ((openSquareDerivedPullbackModel B j).app M.obj) (hUB M)
  have hN : 1 ≤ ℓ ^ n := one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
  have h := (OpenInverseTranspose.openScalarInverseTransposeFactorization
    ℓ pchar k _hp _hℓ φ n hN _hA _hB f j c (c.precomp j)
    a.preserves hJA hUA' hGA a.right a.adjunction
    b.preserves hJB hUB' hGB b.right b.adjunction hSU hbf hbg K).2.2.1
  let α : reductionCompactSupport A (j ≫ i) p ⋙ scalarExtensionFunctor φ Y ⟶
      scalarExtensionFunctor φ U ⋙ sfIntrinsicDerivedOpen B j ⋙
        reductionCompactSupport B i p :=
    Functor.whiskerRight (ambientComposition A j i p).hom (scalarExtensionFunctor φ Y) ≫
      Functor.whiskerLeft (sfIntrinsicDerivedOpen A j) (reductionDirectImageComparison φ i p) ≫
      Functor.whiskerRight (reductionOpenScalarIso φ j).hom (reductionCompactSupport B i p)
  let β : reductionCompactSupport A (j ≫ i) p ⋙ scalarExtensionFunctor φ Y ⟶
      scalarExtensionFunctor φ U ⋙ sfIntrinsicDerivedOpen B j ⋙
        reductionCompactSupport B i p :=
    reductionDirectImageComparison φ (j ≫ i) p ≫
      Functor.whiskerLeft (scalarExtensionFunctor φ U) (ambientComposition B j i p).hom
  apply eq_app_of_iso α β ((openSquareDerivedPullbackModel A j).app (a.right.obj K).obj)
  rw [inverseComposition_hom, inverseComposition_hom] at h
  simpa only [α, β, c, Compactification.precomp, OpenInverseTranspose.restriction,
    OpenInverseTranspose.support, ObjectProperty.lift_obj_obj, ObjectProperty.ι_obj,
    Functor.comp_obj, sfIntrinsicDerivedOpen,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using h


/-- The exceptional scalar mate commutes with restriction to any quasi-compact source
open, after the specified adjunction-preserving composition identifications.
Source: main-20261015, sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph
(blueprint: lem-sp-open-exceptional-scalar-locality).

Proof plan: Fix K, M = G_f,A K and L = U_A M. Let d be the displayed right side.
The defining transpose equation for component at f is exactly the hypothesis r of
lem-sp-open-scalar-restricted-transpose-expansion. That lemma, using the actual
open counit, expands the B-composite counit applied to F_g,B(d) as the extended
f-counit, b_f(M) inverse, F_f,B(T_X(v_A,M)), and F_f,B(b_j(L) inverse).
lem-sp-open-scalar-inverse-transpose-factorization identifies this expression with
the extended composite A-counit followed by b_g(L) inverse. Its assertion applies
to every intrinsic pro-etale finite-Tor L, so no etale-origin assumption is added.
This is the defining transpose of component at g. The composite Hom bijection of
def-weil-pbc-composite-adjunction is injective, and therefore the two components
are equal. No smoothness or invertibility of either exceptional component is used.
-/
theorem openExceptionalScalarLocality
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (_hp : 0 < pchar) (_hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {U X Z Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
    (i : X ⟶ Z) [IsOpenImmersion i] [i.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (_hf : i ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (_hA : (ℓ ^ n : A) = 0) (_hB : (ℓ ^ n : B) = 0)
    (a : SupportAdjunction A i p) (b : SupportAdjunction B i p)
    (hJA : ∀ L : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor X A ((sfIntrinsicDerivedOpen A j).obj L.obj))
    (hUA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor U A ((proEtaleConstantRingDerivedPullback A j).obj M.obj))
    (hGA : ∀ L : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A (j ≫ i) p).obj L.obj))
    (hJB : ∀ L : spFiniteConstructibleTorCategory U B,
      spFiniteConstructibleTor X B ((sfIntrinsicDerivedOpen B j).obj L.obj))
    (hUB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor U B ((proEtaleConstantRingDerivedPullback B j).obj M.obj))
    (hGB : ∀ L : spFiniteConstructibleTorCategory U B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B (j ≫ i) p).obj L.obj))
    (hSU : ∀ L : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor U B ((scalarExtensionFunctor φ U).obj L.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hbf : ∀ M : spFiniteConstructibleTorCategory X A,
      IsIso ((reductionDirectImageComparison φ i p).app M.obj))
    (hbg : ∀ L : spFiniteConstructibleTorCategory U A,
      IsIso ((reductionDirectImageComparison φ (j ≫ i) p).app L.obj))
    (K : spFiniteConstructibleTorCategory Y A) :
    component φ (j ≫ i) p (composite A j i p a hJA hUA hGA)
        (composite B j i p b hJB hUB hGB) hSU hSY hbg K =
      (directImageScalarPullbackIso φ j).inv.app (a.right.obj K).obj ≫
        (proEtaleConstantRingDerivedPullback B j).map
          (component φ i p a b hSX hSY hbf K) := by
  let c : Compactification f := ⟨Z, p, i, _hf.symm, inferInstance, inferInstance⟩
  let M := a.right.obj K
  let L := (restriction A j hUA).obj M
  let T : spFiniteConstructibleTorCategory Y B :=
    ⟨(scalarExtensionFunctor φ Y).obj K.obj, hSY K⟩
  let S : spFiniteConstructibleTorCategory U B :=
    ⟨(scalarExtensionFunctor φ U).obj L.obj, hSU L⟩
  let r := component φ i p a b hSX hSY hbf K
  let d : S ⟶ ((composite B j i p b hJB hUB hGB).right.obj T) :=
    ObjectProperty.homMk ((directImageScalarPullbackIso φ j).inv.app M.obj ≫
      (proEtaleConstantRingDerivedPullback B j).map r)
  let ga := composite A j i p a hJA hUA hGA
  let gb := composite B j i p b hJB hUB hGB
  let := hbg L
  let := hbf M
  have hr := component_counit φ i p a b hSX hSY hbf K
  have hN : 1 ≤ ℓ ^ n := Nat.one_le_pow n ℓ (Fact.out : ℓ.Prime).pos
  have ho := (openScalarRestrictedTransposeExpansion ℓ pchar k _hp (Ne.symm _hℓ)
    φ n hN _hA _hB f j c a.preserves b.preserves a.right b.right
    a.adjunction b.adjunction K (hSY K) (hbf M) r hr).1
  have hv := open_scalar_counit φ j hJA hUA hJB hUB M (hSX M) ho
  have hn := (openAdjunction B j hJB hUB).counit.naturality
    (ObjectProperty.homMk r :
      (⟨(scalarExtensionFunctor φ X).obj M.obj, hSX M⟩ :
        spFiniteConstructibleTorCategory X B) ⟶ b.right.obj T)
  have ht : (sfIntrinsicDerivedOpen B j).map d.hom ≫
      ((openAdjunction B j hJB hUB).counit.app (b.right.obj T)).hom =
      (reductionOpenScalarIso φ j).inv.app L.obj ≫
        (scalarExtensionFunctor φ X).map
          ((openAdjunction A j hJA hUA).counit.app M).hom ≫ r := by
    change (sfIntrinsicDerivedOpen B j).map
      ((directImageScalarPullbackIso φ j).inv.app M.obj ≫
        (proEtaleConstantRingDerivedPullback B j).map r) ≫ _ = _
    rw [Functor.map_comp, Category.assoc]
    have hn' := congrArg (fun z ↦ z.hom) hn
    change (sfIntrinsicDerivedOpen B j).map
        ((proEtaleConstantRingDerivedPullback B j).map r) ≫ _ = _ at hn'
    simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.id_map,
      ObjectProperty.homMk_hom] at hn'
    erw [hn', ← Category.assoc, hv]
    simp only [Category.assoc]
    rfl
  have hs := coefficient_composition ℓ pchar _hp _hℓ k f j i p _hf φ n _hA _hB
    a b hJA hUA hGA hJB hUB hGB hSU hSX hSY hbf hbg K
  have he := counit_calculation (reductionCompactSupport A i p)
    (reductionCompactSupport B i p) (scalarExtensionFunctor φ X)
    (scalarExtensionFunctor φ Y) (reductionDirectImageComparison φ i p)
    ((openAdjunction A j hJA hUA).counit.app M).hom
    (a.adjunction.counit.app K).hom (b.adjunction.counit.app T).hom r
    ((reductionOpenScalarIso φ j).app L.obj)
    ((ambientComposition A j i p).hom.app L.obj)
    ((ambientComposition B j i p).hom.app S.obj)
    ((reductionDirectImageComparison φ (j ≫ i) p).app L.obj)
    ((sfIntrinsicDerivedOpen B j).map d.hom ≫
      ((openAdjunction B j hJB hUB).counit.app (b.right.obj T)).hom)
    ht hr hs
  have htranspose :
      (gb.adjunction.homEquiv S T).symm
        (ObjectProperty.homMk (component φ (j ≫ i) p ga gb hSU hSY hbg K)) =
      (gb.adjunction.homEquiv S T).symm d := by
    apply (spFiniteConstructibleTor Y B).ι.map_injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    change (reductionCompactSupport B (j ≫ i) p).map
        (component φ (j ≫ i) p ga gb hSU hSY hbg K) ≫
        (gb.adjunction.counit.app T).hom = _
    rw [component_counit]
    change inv ((reductionDirectImageComparison φ (j ≫ i) p).app L.obj) ≫
      (scalarExtensionFunctor φ Y).map (ga.adjunction.counit.app K).hom = _
    simp only [ObjectProperty.ι_map]
    change _ = (reductionCompactSupport B (j ≫ i) p).map d.hom ≫
      ((composite B j i p b hJB hUB hGB).adjunction.counit.app T).hom
    rw [composite_counit, composite_counit]
    erw [(ambientComposition B j i p).hom.naturality_assoc d.hom]
    simpa only [L, M, T, restriction, ObjectProperty.lift_obj_obj, ObjectProperty.ι_obj,
      Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.map_comp,
      Category.assoc] using he
  exact congrArg (fun z ↦ z.hom) ((gb.adjunction.homEquiv S T).symm.injective htranspose)

end AlgebraicGeometry.ProEtale.OpenScalarLocality
