/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralFieldCompactScalarSiteSquare
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility2
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# Data for the general-field etale/pro-etale summation counit

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts (lines 20-35):
integral summation, graph
normalization and finite-site transport
(blueprint: def-pur-general-field-etale-sum-data).

The transport record retains the actual sum/evaluation counit and characterizes
its graph comparison on every etale origin.  The coefficient comparison is
likewise characterized by the ordinary summandwise balancing, rather than chosen
as an unspecified isomorphism.  No data is selected from the existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Abbreviation for the already recorded ordinary etale finite-ctf full subcategory.
Source: blueprint Charts, finite coefficient domains
(blueprint: def-pur-general-field-etale-sum-data). -/
abbrev generalFieldEtaleCtf (T : Scheme.{u}) (R : Type u) [CommRing R] :=
  (Etale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T).FullSubcategory

/-- Restriction of the actual intrinsic inverse image; only membership is supplied.
Source: blueprint Charts, transport of inverse image
(blueprint: def-pur-general-field-etale-sum-data). -/
def generalFieldCtfPullback (R : Type u) [CommRing R] [Finite R]
    {U V : Scheme.{u}} (e : U ⟶ V)
    (h : ∀ K : spFiniteConstructibleTorCategory V R,
      spFiniteConstructibleTor U R
        ((proEtaleConstantRingDerivedPullback R e).obj K.obj)) :=
  (spFiniteConstructibleTor U R).lift
    ((spFiniteConstructibleTor V R).ι ⋙ proEtaleConstantRingDerivedPullback R e) h

/-- Restriction of ordinary etale inverse image, in its left-derived coordinates.
Source: blueprint Charts, ordinary sum/evaluation adjunction
(blueprint: def-pur-general-field-etale-sum-data). -/
def generalFieldEtaleCtfPullback (R : Type u) [CommRing R] [Finite R]
    {U V : Scheme.{u}} (e : U ⟶ V)
    (h : ∀ K : generalFieldEtaleCtf V R,
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) U
        ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} R) e).obj K.obj)) :=
  (Etale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) U).lift
    ((Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) V).ι ⋙
      Etale.ordinaryFinitePullback (ULift.{u + 1, u} R) e) h

/-- The published compact-support comparison, expressed in reduction-site coordinates.
Its factors are the canonical realization change and the actual proper/open site map.
Source: blueprint Charts, the map s_R
(blueprint: def-pur-general-field-etale-sum-data). -/
def generalFieldSumCompactSiteIso (R : Type u) [CommRing R] [Finite R]
    {U V : Scheme.{u}} {e : U ⟶ V} (c : Compactification e)
    (L : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))) :=
  (reductionCompactSupport R c.i c.g).mapIso
      ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso R U).app L.obj).symm ≪≫
    (canonicalCompactSupportSiteIso R c L).symm ≪≫
    (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso R V).app
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c).obj L.obj)

/-- A realization of the ordinary sum adjunction on the intrinsic finite-ctf categories.
All comparison data are fixed by the two normalization fields: graph extension
for compact support and the transported sum/evaluation counit.  In particular the
adjunction is not an unspecified adjunction on isomorphic functors.
Source: blueprint Charts, finite-site transport and graph normalization
(blueprint: def-pur-general-field-etale-sum-data). -/
structure GeneralFieldEtaleSumRealization
    (R : Type u) [CommRing R] [Finite R]
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (e : U ⟶ V) [AlgebraicGeometry.Etale e] [IsSeparated e]
    (c : Compactification e)
    (hF : ∀ M : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor V R ((reductionCompactSupport R c.i c.g).obj M.obj)) where
  /-- Comparison is an equivalence on the source finite-ctf category. -/
  source_equivalence : (reductionSiteCtf U R).IsEquivalence
  /-- Comparison is an equivalence on the target finite-ctf category. -/
  target_equivalence : (reductionSiteCtf V R).IsEquivalence
  /-- The actual inverse image preserves finite-ctf objects. -/
  pullback_preserves : ∀ K : spFiniteConstructibleTorCategory V R,
    spFiniteConstructibleTor U R
      ((proEtaleConstantRingDerivedPullback R e).obj K.obj)
  /-- Ordinary inverse image preserves finite-ctf objects. -/
  etale_pullback_preserves : ∀ K : generalFieldEtaleCtf V R,
    Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) U
      ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} R) e).obj K.obj)
  /-- The transported summation functor. -/
  sum : spFiniteConstructibleTorCategory U R ⥤ spFiniteConstructibleTorCategory V R
  /-- Its adjunction to the actual inverse image. -/
  adjunction : sum ⊣ generalFieldCtfPullback R e pullback_preserves
  /-- The transport identification with the ordinary summation functor. -/
  sumSite : reductionSiteCtf U R ⋙ sum ⋙ (spFiniteConstructibleTor V R).ι ≅
    (Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) U).ι ⋙
      (Etale.etaleLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) e inferInstance).mapDerivedCategory ⋙
        reductionSite R V
  /-- The compact-support-to-sum comparison. -/
  graph : reductionCtfCompactSupport R c.i c.g hF ≅ sum
  /-- Its value on every bounded-below etale origin is the canonical graph comparison. -/
  graph_normalization : ∀ (L : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
      (hL : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) U L.obj),
    (graph.hom.app ((reductionSiteCtf U R).obj ⟨L.obj, hL⟩)).hom ≫
        sumSite.hom.app ⟨L.obj, hL⟩ =
      (generalFieldSumCompactSiteIso R c L).hom ≫
        (reductionSite R V).map
          (((Etale.canonicalEtaleCompactSupportNormalization
            (ULift.{u + 1, u} R)).comparison e c).hom.app L.obj)
  /-- The counit is ordinary evaluation, transported by the specified site comparisons. -/
  counit_normalization : ∀ L : generalFieldEtaleCtf V R,
    (adjunction.counit.app ((reductionSiteCtf V R).obj L)).hom =
      (sum.map (ObjectProperty.homMk
        (X := (generalFieldCtfPullback R e pullback_preserves).obj
          ((reductionSiteCtf V R).obj L))
        (Y := (reductionSiteCtf U R).obj
          ((generalFieldEtaleCtfPullback R e etale_pullback_preserves).obj L))
        ((reductionSitePullbackIso R e).hom.app L.obj))).hom ≫
      sumSite.hom.app
        ((generalFieldEtaleCtfPullback R e etale_pullback_preserves).obj L) ≫
      (reductionSite R V).map
        (((Etale.derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) e inferInstance).ofNatIsoRight
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) e).symm).counit.app L.obj)

/-- Realization commutes with ordinary scalar extension through the unique left-adjoint
comparison of the actual exact restriction square. No fixed-tensor model is used.
Source: blueprint Charts, canonical coefficient transport
(blueprint: def-pur-general-field-etale-sum-data). -/
def generalFieldOrdinaryRealizationScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence.{u} T A).functor ⋙ scalarExtensionFunctor.{u} φ T ≅
      @OrdinaryScalarSite.scalar.{u} T.ProEt inferInstance
        (reductionProEtaleSmall T) (Scheme.ProEt.topology T)
        (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
          (sfIntrinsicDerivedEquivalence.{u} T B).functor := by
  let EA := sfIntrinsicDerivedEquivalence.{u} T A
  let EB := sfIntrinsicDerivedEquivalence.{u} T B
  let SI := scalarExtensionFunctor.{u} φ T
  let RI := pbcDerivedRestrict.{u} (proEtaleConstantRingMap (T := T) φ)
  let SO := @OrdinaryScalarSite.scalar.{u} T.ProEt inferInstance
    (reductionProEtaleSmall T) (Scheme.ProEt.topology T)
    (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
    (RingHom.ulift.{u + 1, u + 1, u, u} φ)
  let RO := @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
    (reductionProEtaleSmall T) (Scheme.ProEt.topology T)
    (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
    (RingHom.ulift.{u + 1, u + 1, u, u} φ)
  let adj : (EA.functor ⋙ SI) ⋙ EB.inverse ⊣ EB.functor ⋙ RI ⋙ EA.inverse :=
    (EA.toAdjunction.comp
      (proEtaleRingDerivedExtensionAdjunction.{u}
        (proEtaleConstantRingMap (T := T) φ))).comp EB.symm.toAdjunction
  let r : EB.functor ⋙ RI ⋙ EA.inverse ≅ RO :=
    (Functor.associator EB.functor RI EA.inverse).symm ≪≫
      Functor.isoWhiskerRight (reductionRealizationRestrict.{u} φ T) EA.inverse ≪≫
      Functor.associator RO EA.functor EA.inverse ≪≫
      Functor.isoWhiskerLeft RO EA.unitIso.symm ≪≫ Functor.rightUnitor RO
  let q : (EA.functor ⋙ SI) ⋙ EB.inverse ≅ SO :=
    (adj.ofNatIsoRight r).leftAdjointUniq
      (@CoefficientScalarRepresentatives.adjunction.{u} T.ProEt inferInstance
        (reductionProEtaleSmall T) (Scheme.ProEt.topology T)
        (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
        (RingHom.ulift.{u + 1, u + 1, u, u} φ))
  exact (Functor.rightUnitor (EA.functor ⋙ SI)).symm ≪≫
    Functor.isoWhiskerLeft (EA.functor ⋙ SI) EB.counitIso.symm ≪≫
    (Functor.associator (EA.functor ⋙ SI) EB.inverse EB.functor).symm ≪≫
    Functor.isoWhiskerRight q EB.functor

/-- Canonical scalar/site comparison, using ordinary-site delta and the
restriction-normalized realization comparison, with no legacy tensor model.
Source: blueprint Charts, delta in the transported summation formula
(blueprint: def-pur-general-field-etale-sum-data). -/
def generalFieldOrdinarySiteScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    reductionSite A T ⋙ scalarExtensionFunctor φ T ≅
      OrdinaryScalarSite.scalar.{u} T.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙ reductionSite B T :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (generalFieldOrdinaryRealizationScalarIso φ T) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (OrdinaryScalarSite.delta.{u} (RingHom.ulift.{u + 1, u + 1, u, u} φ) T) _ ≪≫
    Functor.associator _ _ _

/-- Restrict ordinary derived coefficient extension to the recorded etale domain.
Source: blueprint Charts, coefficient transport
(blueprint: def-pur-general-field-etale-sum-data). -/
def generalFieldEtaleCtfScalar
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (h : ∀ L : generalFieldEtaleCtf T A,
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T
        ((OrdinaryScalarSite.scalar.{u} T.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj L.obj)) :=
  (Etale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).lift
    ((Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).ι ⋙
      OrdinaryScalarSite.scalar.{u} T.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)) h


/-- The canonical site functor is an equivalence on the finite-ctf categories.
Source: the finite-site comparison in Charts; the proof is the existing
`ReductionExceptionalRealization` argument with its public intrinsic predicate API.
(blueprint: def-pur-general-field-etale-sum-data).
Proof: full faithfulness follows from the ordinary finite-coefficient comparison
and the intrinsic realization equivalence. For essential surjectivity, realize an
intrinsic object on the fixed-module site, choose its constructible etale origin,
and reflect the Tor interval through the exact comparison. -/
theorem generalFieldSiteCtf_isEquivalence (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R] : (reductionSiteCtf T R).IsEquivalence := by
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T
  let E := sfIntrinsicDerivedEquivalence T R
  have hbij (K L : generalFieldEtaleCtf T R) :
      Function.Bijective (fun f : K ⟶ L ↦ (reductionSiteCtf T R).map f) := by
    have h := bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj L.property.1.1.1
    constructor
    · intro f g he
      apply ObjectProperty.hom_ext
      apply h.injective
      exact E.functor.map_injective (congrArg (fun f ↦ f.hom) he)
    · intro f
      obtain ⟨g, hg⟩ := h.surjective (E.functor.preimage f.hom)
      refine ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ ?_⟩
      change E.functor.map (C.mapDerivedCategory.map g) = f.hom
      change C.mapDerivedCategory.map g = E.functor.preimage f.hom at hg
      exact (congrArg E.functor.map hg).trans (E.functor.map_preimage f.hom)
  have : (reductionSiteCtf T R).Full := ⟨fun {K L} f ↦ (hbij K L).surjective f⟩
  have : (reductionSiteCtf T R).Faithful := ⟨fun {K L} f g h ↦ (hbij K L).injective h⟩
  have : (reductionSiteCtf T R).EssSurj := by
    constructor
    intro M
    let K := E.inverse.obj M.obj
    have hK := (reductionCtf_realization_iff T R K).mp
      (reductionCtf_of_iso T R (E.counitIso.app M.obj).symm M.property)
    obtain ⟨L, hL, ⟨e⟩⟩ := hK.1
    have ht := (DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) T).prop_of_iso e.symm hK
    obtain ⟨a, b, hab⟩ := ht.2
    have hctf : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) T L :=
      ⟨hL, a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b L).mp hab⟩
    refine ⟨⟨L, hctf⟩, ⟨(spFiniteConstructibleTor T R).isoMk ?_⟩⟩
    exact E.functor.mapIso e ≪≫ E.counitIso.app M.obj
  exact {}

/-- Ordinary inverse image preserves the finite-ctf domain used here.
Source: Charts, transport of inverse image.
(blueprint: def-pur-general-field-etale-sum-data).
Proof: apply the existing constructible finite-Tor stability of left-derived
inverse image; `ordinaryFinitePullback` is that same functor. -/
theorem generalFieldEtalePullback_preserves (R : Type u) [CommRing R]
    {U V : Scheme.{u}} (e : U ⟶ V) (K : generalFieldEtaleCtf V R) :
    Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) U
      ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} R) e).obj K.obj) :=
  Etale.constructibleFiniteTor_leftDerivedUpperStar _ e K.property

/-- The actual intrinsic inverse image preserves finite-ctf objects.
Source: Charts, finite-site transport of the exact inverse image.
(blueprint: def-pur-general-field-etale-sum-data).
Proof: present the input by an etale finite-ctf object using the comparison
equivalence. Ordinary inverse image stays in that domain by stability. The
specified site/pullback comparison and the image of the presentation isomorphism
identify its realization with the required intrinsic inverse image. -/
theorem generalFieldPullback_preserves (R : Type u) [CommRing R] [Finite R]
    {U V : Scheme.{u}} (e : U ⟶ V) (K : spFiniteConstructibleTorCategory V R) :
    spFiniteConstructibleTor U R
      ((proEtaleConstantRingDerivedPullback R e).obj K.obj) := by
  let := generalFieldSiteCtf_isEquivalence V R
  let E := (reductionSiteCtf V R).asEquivalence
  let L := E.inverse.obj K
  let L' : generalFieldEtaleCtf U R :=
    ⟨_, generalFieldEtalePullback_preserves R e L⟩
  exact reductionCtf_of_iso U R
    ((reductionSitePullbackIso R e).symm.app L.obj ≪≫
      (proEtaleConstantRingDerivedPullback R e).mapIso
        ((spFiniteConstructibleTor V R).ι.mapIso (E.counitIso.app K)))
    ((reductionSiteCtf U R).obj L').property

section Scalar

variable {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- Restrict the specified ordinary scalar/site mate to finite-ctf objects.
Source: Charts, canonical coefficient transport.
(blueprint: def-pur-general-field-etale-sum-data).
The underlying components are precisely the published scalar/site comparison. -/
def generalFieldSiteCtfScalarIso (φ : A →+* B) (T : Scheme.{u})
    (hT : ∀ M : spFiniteConstructibleTorCategory T A,
      spFiniteConstructibleTor T B ((scalarExtensionFunctor φ T).obj M.obj))
    (hTe : ∀ L : generalFieldEtaleCtf T A,
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T
        ((OrdinaryScalarSite.scalar T.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj L.obj)) :
    reductionSiteCtf T A ⋙ reductionCtfScalar φ T hT ≅
      generalFieldEtaleCtfScalar φ T hTe ⋙ reductionSiteCtf T B :=
  NatIso.ofComponents
    (fun L ↦ (spFiniteConstructibleTor T B).isoMk
      ((generalFieldOrdinarySiteScalarIso φ T).app L.obj))
    (fun f ↦ ObjectProperty.hom_ext _
      ((generalFieldOrdinarySiteScalarIso φ T).hom.naturality f.hom))

end Scalar

section SumScalar

variable {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
variable (φ : A →+* B)
variable {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
variable (e : U ⟶ V) [AlgebraicGeometry.Etale e] [IsSeparated e]
variable (c : Compactification e)
variable (hFA : ∀ M : spFiniteConstructibleTorCategory U A,
  spFiniteConstructibleTor V A ((reductionCompactSupport A c.i c.g).obj M.obj))
variable (hFB : ∀ M : spFiniteConstructibleTorCategory U B,
  spFiniteConstructibleTor V B ((reductionCompactSupport B c.i c.g).obj M.obj))
variable (hTU : ∀ M : spFiniteConstructibleTorCategory U A,
  spFiniteConstructibleTor U B ((scalarExtensionFunctor φ U).obj M.obj))
variable (hTV : ∀ M : spFiniteConstructibleTorCategory V A,
  spFiniteConstructibleTor V B ((scalarExtensionFunctor φ V).obj M.obj))
variable (hTeU : ∀ L : generalFieldEtaleCtf U A,
  Etale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U
    ((OrdinaryScalarSite.scalar U.smallEtaleTopology
      (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj L.obj))

/-- The ordinary summandwise balancing, conjugated by the specified site comparisons.
Source: Charts, integral summation and finite-site scalar transport.
(blueprint: def-pur-general-field-etale-sum-data).
All five factors are specified natural isomorphisms, so this constructs the map
rather than selecting an unspecified isomorphism. -/
def generalFieldSumScalarOnEtaleOrigins
    (DA : GeneralFieldEtaleSumRealization A e c hFA)
    (DB : GeneralFieldEtaleSumRealization B e c hFB) :
    reductionSiteCtf U A ⋙
        ((DA.sum ⋙ reductionCtfScalar φ V hTV) ⋙ (spFiniteConstructibleTor V B).ι) ≅
      reductionSiteCtf U A ⋙
        ((reductionCtfScalar φ U hTU ⋙ DB.sum) ⋙ (spFiniteConstructibleTor V B).ι) :=
  Functor.isoWhiskerRight DA.sumSite (scalarExtensionFunctor φ V) ≪≫
    Functor.isoWhiskerLeft
      ((Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).ι ⋙
        (Etale.etaleLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e inferInstance).mapDerivedCategory)
      (generalFieldOrdinarySiteScalarIso φ V) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (Etale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).ι
        (CoefficientCompatibility.sumScalar
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) e)) (reductionSite B V) ≪≫
    Functor.isoWhiskerLeft (generalFieldEtaleCtfScalar φ U hTeU) DB.sumSite.symm ≪≫
    Functor.isoWhiskerRight (generalFieldSiteCtfScalarIso φ U hTU hTeU).symm
      (DB.sum ⋙ (spFiniteConstructibleTor V B).ι)

/-- Extend the specified origin balancing uniquely through the comparison equivalence.
Source: Charts, transport of summandwise coefficient balancing.
(blueprint: def-pur-general-field-etale-sum-data).
The two preimages are under fully faithful functors: first precomposition by an
equivalence, then inclusion of the full finite-ctf category. -/
def generalFieldEtaleSumScalarIso
    (DA : GeneralFieldEtaleSumRealization A e c hFA)
    (DB : GeneralFieldEtaleSumRealization B e c hFB) :
    DA.sum ⋙ reductionCtfScalar φ V hTV ≅ reductionCtfScalar φ U hTU ⋙ DB.sum := by
  letI := DA.source_equivalence
  let P :
      (spFiniteConstructibleTorCategory U A ⥤ proEtaleDerivedCategory V B) ⥤
        (generalFieldEtaleCtf U A ⥤ proEtaleDerivedCategory V B) :=
    (reductionSiteCtf U A).asEquivalence.symm.congrLeft.functor
  exact ((spFiniteConstructibleTor V B).fullyFaithfulι.whiskeringRight _).preimageIso
    (P.preimageIso (generalFieldSumScalarOnEtaleOrigins φ e c hFA hFB hTU hTV hTeU DA DB))

/-- The constructed scalar isomorphism has the prescribed component on every origin.
Source: Charts, uniqueness of finite-site transport.
(blueprint: def-pur-general-field-etale-sum-data).
Proof: apply the map/preimage identities for the fully faithful inclusion and
for precomposition by the comparison equivalence, then evaluate at the origin. -/
theorem generalFieldEtaleSumScalarIso_hom_on_origin
    (DA : GeneralFieldEtaleSumRealization A e c hFA)
    (DB : GeneralFieldEtaleSumRealization B e c hFB) (L : generalFieldEtaleCtf U A) :
    ((generalFieldEtaleSumScalarIso φ e c hFA hFB hTU hTV hTeU DA DB).hom.app
        ((reductionSiteCtf U A).obj L)).hom =
      (generalFieldSumScalarOnEtaleOrigins φ e c hFA hFB hTU hTV hTeU DA DB).hom.app L := by
  let := DA.source_equivalence
  let P :
      (spFiniteConstructibleTorCategory U A ⥤ proEtaleDerivedCategory V B) ⥤
        (generalFieldEtaleCtf U A ⥤ proEtaleDerivedCategory V B) :=
    (reductionSiteCtf U A).asEquivalence.symm.congrLeft.functor
  let W := (spFiniteConstructibleTor V B).fullyFaithfulι.whiskeringRight
    (spFiniteConstructibleTorCategory U A)
  let q := generalFieldSumScalarOnEtaleOrigins φ e c hFA hFB hTU hTV hTeU DA DB
  have hW := W.map_preimage (P.preimage q.hom)
  have hP := P.map_preimage q.hom
  exact NatTrans.congr_app ((congrArg P.map hW).trans hP) L

set_option maxRecDepth 4096 in
/-- The scalar isomorphism is normalized by the ordinary summandwise balancing.
Source: Charts, definition of transported summation balancing.
(blueprint: def-pur-general-field-etale-sum-data).
Proof: expand its origin component, cancel the inverse scalar/site comparison
against its hom, then cancel the inverse summation/site comparison against its hom. -/
theorem generalFieldEtaleSumScalarIso_normalization
    (DA : GeneralFieldEtaleSumRealization A e c hFA)
    (DB : GeneralFieldEtaleSumRealization B e c hFB) (L : generalFieldEtaleCtf U A) :
    ((generalFieldEtaleSumScalarIso φ e c hFA hFB hTU hTV hTeU DA DB).hom.app
        ((reductionSiteCtf U A).obj L)).hom ≫
      (DB.sum.map ((generalFieldSiteCtfScalarIso φ U hTU hTeU).hom.app L)).hom ≫
      DB.sumSite.hom.app ((generalFieldEtaleCtfScalar φ U hTeU).obj L) =
    (scalarExtensionFunctor φ V).map (DA.sumSite.hom.app L) ≫
      (generalFieldOrdinarySiteScalarIso φ V).hom.app
        ((Etale.etaleLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e inferInstance).mapDerivedCategory.obj
          L.obj) ≫
      (reductionSite B V).map
        ((CoefficientCompatibility.sumScalar
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) e).hom.app L.obj) := by
  rw [generalFieldEtaleSumScalarIso_hom_on_origin]
  simp only [generalFieldSumScalarOnEtaleOrigins, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    Category.assoc, ObjectProperty.ι_map]
  have hc :
      (DB.sum.map ((generalFieldSiteCtfScalarIso φ U hTU hTeU).inv.app L)).hom ≫
        (DB.sum.map ((generalFieldSiteCtfScalarIso φ U hTU hTeU).hom.app L)).hom = 𝟙 _ :=
    ((DB.sum ⋙ (spFiniteConstructibleTor V B).ι).mapIso
      ((generalFieldSiteCtfScalarIso φ U hTU hTeU).app L)).inv_hom_id
  erw [← Category.assoc
    ((DB.sum.map ((generalFieldSiteCtfScalarIso φ U hTU hTeU).inv.app L)).hom)
    ((DB.sum.map ((generalFieldSiteCtfScalarIso φ U hTU hTeU).hom.app L)).hom), hc,
    Category.id_comp, DB.sumSite.inv_hom_id_app, Category.comp_id]
  rfl

end SumScalar

end AlgebraicGeometry.ProEtale
