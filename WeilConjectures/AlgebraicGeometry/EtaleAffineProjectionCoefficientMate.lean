/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Targets.VectorBundlePurity
public import WeilConjectures.SecSmoothPurity.ReductionExceptional
public import WeilConjectures.AlgebraicGeometry.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ReductionSiteCoefficientPasting
import WeilConjectures.AlgebraicGeometry.AffineCounitScalar
import WeilConjectures.AlgebraicGeometry.EtaleAffineIntegrationCoefficientEquation
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.EtaleProEtaleAdjunctionTransfer
import all WeilConjectures.AlgebraicGeometry.EtaleProEtaleCoefficientCompatibility

/-! # The normalized affine projection coefficient mate

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Charts and uniqueness of transposes
(blueprint: lem-pur-etale-affine-projection-coefficient-mate).

The existing ordered affine tower is canonically affine space by
`affineTraceAffineSpaceIso`. Positive coefficient levels are indexed by their
predecessors. The ordinary mate, scalar map, Tate reassociation and site transport
are the published constructions, with their actual counits retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The integration-normalized purity comparison. The affine adjunction has the
specified iterated projective-line integration as counit. Transport its left functor
by the proper/open compactification comparison, then use uniqueness of right adjoints.
Source: blueprint Charts, vector-bundle integration on the trivial bundle
(blueprint: lem-pur-etale-affine-projection-coefficient-mate). -/
def affineProjectionPurityIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (V : Scheme.{u}) [IsNoetherian V] (d N : ℕ) (hA : (N : A) = 0)
    (hV : IsUnit (N : Γ(V, ⊤))) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) :
    affineTraceRight A N hA V d ≅
      rightDerivedUpperShriek A (affineTraceProjection V d) :=
  ((affineTraceAdjunction A N hA t D V hV d).ofNatIsoLeft
    (ProEtale.reductionEtaleAffineLeftIso A V d
      (HasCompactification.compactification (affineTraceProjection V d)))).rightAdjointUniq
        (rightDerivedUpperShriekAdjunction A
          (affineTraceProjection V d))

/-- The ordinary part of the assertion, including the domain on which the specified
coefficient projection is invertible. Every normalized P1 datum is allowed; its fields
fix the Kummer classes, trace and counit, so these are not extra orientation choices.
Source: blueprint Charts and uniqueness of transposes
(blueprint: lem-pur-etale-affine-projection-coefficient-mate). -/
def AffineProjectionCoefficientAssertion
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (V : Scheme.{u}) [IsNoetherian V] (d N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (hV : IsUnit (N : Γ(V, ⊤))) : Prop :=
  ∀ (tA : OrdinaryFiniteTwistTransport A N hA)
    (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (L : DerivedCategoryModule A V),
    DerivedCategory.isBoundedConstructible A V L →
    (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A V a b L) →
    IsIso (ExceptionalCoefficients.compactSupportMap φ
      (HasCompactification.compactification (affineTraceProjection V d))
      ((rightDerivedUpperShriek A
        (affineTraceProjection V d)).obj L)) ∧
    IsIso (ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L) ∧
    (scalarExtension φ (affineTraceTower V d)).map
        ((affineProjectionPurityIso A V d N hA hV tA DA).hom.app L) ≫
      ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L =
    (ProEtale.reductionEtaleAffineScalarIso φ V N hA hB hV d L).hom ≫
      (affineProjectionPurityIso B V d N hB hV tB DB).hom.app
        ((scalarExtension φ V).obj L)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- The site clause in intrinsic Dctf coordinates. The origin comparison o is constrained
by its actual site/scalar equation. The two realizations retain the actual counits.
For any constructible adjunctions and their defining coefficient transpose c, the equation
identifies c with the site transport of the ordinary-etale transpose. This includes every
ordinary origin and is invariant under its canonical isomorphisms.
Source: blueprint Charts; det-sp-reduction-exceptional defining transpose equation
(blueprint: lem-pur-etale-affine-projection-coefficient-mate). -/
def AffineProjectionCoefficientSiteAssertion
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (V : Scheme.{u}) (d : ℕ)
    (C : Compactification (affineTraceProjection V d)) : Prop :=
  ∀ (hFA : ∀ M : spFiniteConstructibleTorCategory (affineTraceTower V d) A,
      spFiniteConstructibleTor V A ((reductionCompactSupport A C.i C.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory (affineTraceTower V d) B,
      spFiniteConstructibleTor V B ((reductionCompactSupport B C.i C.g).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory (affineTraceTower V d) A,
      spFiniteConstructibleTor (affineTraceTower V d) B
        ((scalarExtensionFunctor φ (affineTraceTower V d)).obj M.obj))
    (hSV : ∀ L : spFiniteConstructibleTorCategory V A,
      spFiniteConstructibleTor V B ((scalarExtensionFunctor φ V).obj L.obj))
    (GA : spFiniteConstructibleTorCategory V A ⥤
      spFiniteConstructibleTorCategory (affineTraceTower V d) A)
    (GB : spFiniteConstructibleTorCategory V B ⥤
      spFiniteConstructibleTorCategory (affineTraceTower V d) B)
    (adjA : reductionCtfCompactSupport A C.i C.g hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B C.i C.g hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A C.i C.g hFA GA adjA)
    (RB : ReductionExceptionalRealization B C.i C.g hFB GB adjB)
    (o : RA.origin ⋙ Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) V ≅
      reductionCtfScalar φ V hSV ⋙ RB.origin),
    (∀ L : spFiniteConstructibleTorCategory V A,
      (reductionSite B V).map (o.hom.app L) ≫
          RB.originIso.hom.app ((reductionCtfScalar φ V hSV).obj L) =
        (reductionSiteScalarIso φ V).inv.app (RA.origin.obj L) ≫
          (scalarExtensionFunctor φ V).map (RA.originIso.hom.app L)) →
    ∀ c : GA ⋙ reductionCtfScalar φ (affineTraceTower V d) hSX ⟶
      reductionCtfScalar φ V hSV ⋙ GB,
    ∀ hb : ∀ L : spFiniteConstructibleTorCategory V A,
      IsIso ((reductionDirectImageComparison φ C.i C.g).app (GA.obj L).obj),
    (∀ L : spFiniteConstructibleTorCategory V A,
      (reductionCompactSupport B C.i C.g).map (c.app L).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ V hSV).obj L)).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison φ C.i C.g).app (GA.obj L).obj) (hb L) ≫
          (scalarExtensionFunctor φ V).map (adjA.counit.app L).hom) →
    ∀ L : spFiniteConstructibleTorCategory V A,
      (c.app L).hom ≫ RB.rightIso.hom.app ((reductionCtfScalar φ V hSV).obj L) =
        (scalarExtensionFunctor φ (affineTraceTower V d)).map (RA.rightIso.hom.app L) ≫
        (reductionSiteScalarIso φ (affineTraceTower V d)).hom.app
          (RA.right.obj (RA.origin.obj L)) ≫
        (reductionSite B (affineTraceTower V d)).map
          (RB.adjunction.homEquiv _ _
            (Etale.ExceptionalCoefficients.comparisonInverse
              (RingHom.ulift.{u + 1, u + 1, u, u} φ)
              (⟨C.Z, C.g, C.i, rfl, inferInstance, inferInstance⟩ : Compactification (C.i ≫ C.g))
              (RA.right.obj (RA.origin.obj L)) ≫
            (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) V).map
              (RA.adjunction.counit.app (RA.origin.obj L))) ≫
            RB.right.map (o.hom.app L))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

private theorem affineProjectionPurityIso_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (V : Scheme.{u}) [IsNoetherian V] (d N : ℕ) (hA : (N : A) = 0)
    (hV : IsUnit (N : Γ(V, ⊤))) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) (L : DerivedCategoryModule A V) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (HasCompactification.compactification (affineTraceProjection V d))).map
        ((affineProjectionPurityIso A V d N hA hV t D).hom.app L) ≫
      (rightDerivedUpperShriekAdjunction A
        (affineTraceProjection V d)).counit.app L =
    (ProEtale.reductionEtaleAffineLeftIso A V d
      (HasCompactification.compactification (affineTraceProjection V d))).inv.app _ ≫
        (affineTraceAdjunction A N hA t D V hV d).counit.app L := by
  let adj := (affineTraceAdjunction A N hA t D V hV d).ofNatIsoLeft
    (ProEtale.reductionEtaleAffineLeftIso A V d
      (HasCompactification.compactification (affineTraceProjection V d)))
  exact adj.rightAdjointUniq_hom_app_counit
    (rightDerivedUpperShriekAdjunction A
      (affineTraceProjection V d)) L

private theorem affineScalarCounit_allData (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (V : Scheme.{u}) [IsNoetherian V] (hV : IsUnit (N : Γ(V, ⊤))) (d : ℕ)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) (L : DerivedCategoryModule A V) :
    (ProEtale.reductionEtaleAffineLeftIso A V d
      (HasCompactification.compactification (affineTraceProjection V d))).inv.app _ ≫
        (affineTraceAdjunction A N hA t D V hV d).counit.app L =
      affineScalarCompactificationCounit N hN A hA V hV d
        (HasCompactification.compactification (affineTraceProjection V d)) L := by
  obtain rfl := ordinaryFiniteTwistTransport_unique A N hA t
    (projectiveLineTraceTransport N hN A hA)
  have hD : D = projectiveLineTraceDatum N hN A hA := by
    funext T inst hT
    exact ordinaryFiniteP1Datum_unique A N hA _ T hT _ _
  rw [hD]
  rfl

private theorem normalizeCounitEquation
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {A B Z : C} {W X Y : D}
    (gA : A ⟶ B) (epsA : B ⟶ Z) (zA : A ⟶ Z)
    (q : T.obj A ⟶ W) (a : W ⟶ X) (gB : X ⟶ Y)
    (epsB : Y ⟶ T.obj Z) (zB : X ⟶ T.obj Z)
    (hA : gA ≫ epsA = zA) (hB : gB ≫ epsB = zB)
    (h : q ≫ a ≫ zB = T.map zA) :
    q ≫ a ≫ gB ≫ epsB = T.map (gA ≫ epsA) := by
  rw [hB, hA]
  exact h

-- Keep the associativity calculation over abstract arrows: the scheme-specific
-- comparison constructions are large and must be used only through their equations.
private theorem coefficientCounitPasting
    {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ X₁₁ : D}
    (b : X₀ ⟶ X₁) (u : X₁ ⟶ X₂) (v : X₂ ⟶ X₃) (sB : X₃ ⟶ X₄)
    (epsB : X₄ ⟶ X₅) (oriB : X₅ ⟶ X₆)
    (x : X₀ ⟶ X₇) (b' : X₇ ⟶ X₂) (sA : X₇ ⟶ X₈)
    (δ : X₈ ⟶ X₉) (r : X₉ ⟶ X₄) (qeps : X₉ ⟶ X₁₀)
    (o : X₁₀ ⟶ X₅) (epsA : X₈ ⟶ X₁₁) (e : X₁₁ ≅ X₁₀)
    (oriA : X₁₁ ⟶ X₆)
    (hn : b ≫ u = x ≫ b') (hs : b' ≫ v ≫ sB = sA ≫ δ ≫ r)
    (ht : r ≫ epsB = qeps ≫ o) (hd : δ ≫ qeps = epsA ≫ e.hom)
    (ho : o ≫ oriB = e.inv ≫ oriA) :
    b ≫ u ≫ v ≫ sB ≫ epsB ≫ oriB = x ≫ sA ≫ epsA ≫ oriA := by
  rw [← Category.assoc b u, hn]
  simp only [Category.assoc]
  rw [reassoc_of% hs, reassoc_of% ht, reassoc_of% hd, ho]
  simp only [Iso.hom_inv_id_assoc]

private theorem mapCounitPasting
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {U V W R : D} (b : U ⟶ F.obj X)
    (u : X ⟶ Y) (v : Y ⟶ Z) (s : F.obj Z ⟶ V)
    (eps : V ⟶ W) (o : W ⟶ R) (r : U ⟶ R)
    (h : b ≫ F.map u ≫ F.map v ≫ s ≫ eps ≫ o = r) :
    b ≫ F.map (u ≫ v) ≫ (s ≫ eps ≫ o) = r := by
  simpa only [F.map_comp, Category.assoc] using h

-- Pasting at bounded-below endpoints only needs the displayed support components.
private theorem siteCounitPasting
    {CA DA CB DB IA JA IB JB : Type*}
    [Category CA] [Category DA] [Category CB] [Category DB]
    [Category IA] [Category JA] [Category IB] [Category JB]
    (FA : CA ⥤ DA) (FB : CB ⥤ DB) (FAi : IA ⥤ JA) (FBi : IB ⥤ JB)
    (UA : CA ⥤ IA) (VA : DA ⥤ JA) (UB : CB ⥤ IB) (VB : DB ⥤ JB)
    (S : CA ⥤ CB) (T : DA ⥤ DB) (SX : IA ⥤ IB) (SY : JA ⥤ JB)
    (δX : UA ⋙ SX ≅ S ⋙ UB) (δY : VA ⋙ SY ≅ T ⋙ VB)
    (b : FAi ⋙ SY ⟶ SX ⋙ FBi)
    {M : CA} {N : CB} {L : DA} {K : DB} {X : IA} {I : JA}
    (e : X ≅ UA.obj M) (o : T.obj L ≅ K)
    (sA : FAi.obj (UA.obj M) ⟶ VA.obj (FA.obj M))
    (sB : FBi.obj (UB.obj N) ⟶ VB.obj (FB.obj N))
    (epsA : FA.obj M ⟶ L) (epsB : FB.obj N ⟶ K)
    (oriA : VA.obj L ⟶ I) (oriB : VB.obj K ⟶ SY.obj I)
    (eps : FAi.obj X ⟶ I) (q : T.obj (FA.obj M) ⟶ FB.obj (S.obj M))
    (t : S.obj M ⟶ N)
    (hc : FAi.map e.hom ≫ sA ≫ VA.map epsA ≫ oriA = eps)
    (ho : VB.map o.hom ≫ oriB = (δY.app L).inv ≫ SY.map oriA)
    (ht : q ≫ FB.map t ≫ epsB = T.map epsA ≫ o.hom)
    (hs : SY.map sA ≫ (δY.app (FA.obj M)).hom ≫ VB.map (q ≫ FB.map t) =
      b.app (UA.obj M) ≫ FBi.map ((δX.app M).hom ≫ UB.map t) ≫ sB) :
    b.app X ≫ FBi.map (SX.map e.hom ≫ (δX.app M).hom ≫ UB.map t) ≫
      (sB ≫ VB.map epsB ≫ oriB) = SY.map eps := by
  have hn := b.naturality e.hom
  change SY.map (FAi.map e.hom) ≫ _ = b.app X ≫ FBi.map (SX.map e.hom) at hn
  have hd := δY.hom.naturality epsA
  change SY.map (VA.map epsA) ≫ _ =
    (δY.app (FA.obj M)).hom ≫ VB.map (T.map epsA) at hd
  have ht' : (q ≫ FB.map t) ≫ epsB = T.map epsA ≫ o.hom := by
    simpa only [Category.assoc] using ht
  have htm : VB.map (q ≫ FB.map t) ≫ VB.map epsB =
      VB.map (T.map epsA) ≫ VB.map o.hom :=
    (VB.map_comp _ _).symm.trans
      ((congrArg VB.map ht').trans (VB.map_comp _ _))
  have hc' := congrArg SY.map hc
  simp only [Functor.map_comp] at hc'
  have hh := coefficientCounitPasting (b.app X) (FBi.map (SX.map e.hom))
    (FBi.map ((δX.app M).hom ≫ UB.map t)) sB (VB.map epsB) oriB
    (SY.map (FAi.map e.hom)) _ (SY.map sA) (δY.app (FA.obj M)).hom
    _ (VB.map (T.map epsA)) (VB.map o.hom) (SY.map (VA.map epsA))
    (δY.app L) (SY.map oriA) hn.symm hs.symm htm hd.symm ho
  exact mapCounitPasting FBi (b.app X) (SX.map e.hom)
    ((δX.app M).hom ≫ UB.map t) sB (VB.map epsB) oriB (SY.map eps) (hh.trans hc')

private theorem compareConjugatedCounit
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {U V : D} (e : Y ≅ Z) (w : X ⟶ Z)
    (eps : F.obj Y ⟶ V) (z : F.obj Z ⟶ V) (b : U ⟶ F.obj X) [IsIso b]
    (r : U ⟶ V) (he : eps = F.map e.hom ≫ z)
    (hw : b ≫ F.map w ≫ z = r) :
    F.map (w ≫ e.inv) ≫ eps = inv b ≫ r := by
  rw [he, F.map_comp]
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id,
    F.map_id, Category.id_comp]
  apply (cancel_epi b).1
  simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hw

private theorem counitUniqueOfInjective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {U V : D} (e : Y ≅ Z) (w : X ⟶ Z)
    (c : X ⟶ Y) (eps : F.obj Y ⟶ V) (z : F.obj Z ⟶ V)
    (b : U ⟶ F.obj X) [hb : IsIso b] (r : U ⟶ V)
    (hinj : Function.Injective (fun f : X ⟶ Y ↦ F.map f ≫ eps))
    (he : eps = F.map e.hom ≫ z)
    (hc : F.map c ≫ eps = inv b ≫ r) (hw : b ≫ F.map w ≫ z = r) :
    c ≫ e.hom = w := by
  have h : c = w ≫ e.inv := hinj
    (hc.trans (compareConjugatedCounit F e w eps z b r he hw).symm)
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem liftCounitInjective
    {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (hF : ∀ M : P.FullSubcategory, Q (F.obj M.obj))
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adj : Q.lift (P.ι ⋙ F) hF ⊣ G)
    (X : P.FullSubcategory) (Y : Q.FullSubcategory) :
    Function.Injective (fun f : X.obj ⟶ (G.obj Y).obj ↦
      F.map f ≫ (adj.counit.app Y).hom) := by
  intro f g h
  have he : (adj.homEquiv _ _).symm (ObjectProperty.homMk f) =
      (adj.homEquiv _ _).symm (ObjectProperty.homMk g) := by
    apply ObjectProperty.hom_ext
    exact h
  exact congrArg InducedCategory.Hom.hom ((adj.homEquiv _ _).symm.injective he)

private theorem inverseTransposeCounit
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {M : C} {L K U : D} (q : U ⟶ F.obj M) [hq : IsIso q]
    (r : U ⟶ L) (o : L ⟶ K) :
    q ≫ F.map (adj.homEquiv _ _ (inv q ≫ r) ≫ G.map o) ≫ adj.counit.app K =
      r ≫ o := by
  have h := adj.homEquiv_naturality_right_symm
    (adj.homEquiv M L (inv q ≫ r)) o
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at h
  rw [h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

private theorem comparisonInverse_eq_inv
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (C : Compactification f)
    (M : DerivedCategoryModule A X)
    (h : IsIso (ExceptionalCoefficients.compactSupportMap φ C M)) :
    ExceptionalCoefficients.comparisonInverse φ C M =
      @inv _ _ _ _ (ExceptionalCoefficients.compactSupportMap φ C M) h := by
  dsimp only [ExceptionalCoefficients.comparisonInverse]
  rw [dif_pos h]

private theorem normalizedMateComponent
    {CA DA CB DB : Type*} [Category CA] [Category DA] [Category CB] [Category DB]
    {FA : CA ⥤ DA} {GA HA : DA ⥤ CA} {FB : CB ⥤ DB} {GB HB : DB ⥤ CB}
    (adjA : FA ⊣ GA) (adjB : FB ⊣ GB) (γA : HA ≅ GA) (γB : HB ≅ GB)
    (S : CA ⥤ CB) (T : DA ⥤ DB) (K : DA)
    (qH : T.obj (FA.obj (HA.obj K)) ≅ FB.obj (S.obj (HA.obj K)))
    (qG : T.obj (FA.obj (GA.obj K)) ≅ FB.obj (S.obj (GA.obj K)))
    (a : S.obj (HA.obj K) ≅ HB.obj (T.obj K))
    (b : S.obj (GA.obj K) ⟶ GB.obj (T.obj K))
    (hb : FB.map b ≫ adjB.counit.app (T.obj K) =
      qG.inv ≫ T.map (adjA.counit.app K))
    (hn : T.map (FA.map (γA.hom.app K)) ≫ qG.hom =
      qH.hom ≫ FB.map (S.map (γA.hom.app K)))
    (hz : qH.hom ≫ FB.map a.hom ≫ FB.map (γB.hom.app (T.obj K)) ≫
        adjB.counit.app (T.obj K) =
      T.map (FA.map (γA.hom.app K) ≫ adjA.counit.app K)) :
    IsIso b ∧ S.map (γA.hom.app K) ≫ b = a.hom ≫ γB.hom.app (T.obj K) := by
  have he : S.map (γA.hom.app K) ≫ b = a.hom ≫ γB.hom.app (T.obj K) := by
    apply (adjB.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, FB.map_comp, Category.assoc]
    rw [hb]
    apply (cancel_epi qH.hom).1
    rw [← Category.assoc qH.hom, ← hn]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simpa only [T.map_comp, Category.assoc] using hz.symm
  refine ⟨?_, he⟩
  have hf : b = S.map (γA.inv.app K) ≫ a.hom ≫ γB.hom.app (T.obj K) := by
    apply (cancel_epi (S.map (γA.hom.app K))).1
    simpa only [← S.map_comp_assoc, Iso.hom_inv_id_app, S.map_id,
      Category.id_comp, Category.assoc] using he
  rw [hf]
  infer_instance

attribute [local irreducible] ProEtale.reductionSiteScalarIso
  ProEtale.reductionSiteCompactSupportIso ProEtale.reductionDirectImageComparison
  ProEtale.reductionSite ProEtale.scalarExtensionFunctor
  ProEtale.reductionEtaleAffineScalarIso affineProjectionPurityIso

open ProEtale in
private def coefficientSiteAssertion
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (C : Compactification f) : Prop :=
  ∀ (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A C.i C.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B C.i C.g).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B
        ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ L : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj L.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤
      spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤
      spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A C.i C.g hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B C.i C.g hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A C.i C.g hFA GA adjA)
    (RB : ReductionExceptionalRealization B C.i C.g hFB GB adjB)
    (o : RA.origin ⋙ Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y ≅
      reductionCtfScalar φ Y hSY ⋙ RB.origin),
    (∀ L : spFiniteConstructibleTorCategory Y A,
      (reductionSite B Y).map (o.hom.app L) ≫
          RB.originIso.hom.app ((reductionCtfScalar φ Y hSY).obj L) =
        (reductionSiteScalarIso φ Y).inv.app (RA.origin.obj L) ≫
          (scalarExtensionFunctor φ Y).map (RA.originIso.hom.app L)) →
    ∀ c : GA ⋙ reductionCtfScalar φ X hSX ⟶
      reductionCtfScalar φ Y hSY ⋙ GB,
    ∀ hb : ∀ L : spFiniteConstructibleTorCategory Y A,
      IsIso ((reductionDirectImageComparison φ C.i C.g).app (GA.obj L).obj),
    (∀ L : spFiniteConstructibleTorCategory Y A,
      (reductionCompactSupport B C.i C.g).map (c.app L).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj L)).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison φ C.i C.g).app (GA.obj L).obj) (hb L) ≫
          (scalarExtensionFunctor φ Y).map (adjA.counit.app L).hom) →
    ∀ L : spFiniteConstructibleTorCategory Y A,
      (c.app L).hom ≫ RB.rightIso.hom.app ((reductionCtfScalar φ Y hSY).obj L) =
        (scalarExtensionFunctor φ X).map (RA.rightIso.hom.app L) ≫
        (reductionSiteScalarIso φ X).hom.app
          (RA.right.obj (RA.origin.obj L)) ≫
        (reductionSite B X).map
          (RB.adjunction.homEquiv _ _
            (Etale.ExceptionalCoefficients.comparisonInverse
              (RingHom.ulift.{u + 1, u + 1, u, u} φ)
              (⟨C.Z, C.g, C.i, rfl, inferInstance, inferInstance⟩ : Compactification (C.i ≫ C.g))
              (RA.right.obj (RA.origin.obj L)) ≫
            (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).map
              (RA.adjunction.counit.app (RA.origin.obj L))) ≫
            RB.right.map (o.hom.app L))


-- The record and its consumers synthesize different proofs of the same site
-- instances. Build an explicit congruence instead of unfolding the derived functors.
private meta def proofArgumentCongruence (fuel : Nat) (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let fuel + 1 := fuel | throwError "congruence depth"
  if a.isFVar then
    if let some v ← a.fvarId!.getValue? then
      return ← proofArgumentCongruence fuel v b
  if b.isFVar then
    if let some v ← b.fvarId!.getValue? then
      return ← proofArgumentCongruence fuel a v
  if a.isLet then
    return ← proofArgumentCongruence fuel (a.letBody!.instantiate1 a.letValue!) b
  if b.isLet then
    return ← proofArgumentCongruence fuel a (b.letBody!.instantiate1 b.letValue!)
  if a.isMData then
    return ← proofArgumentCongruence fuel a.mdataExpr! b
  if b.isMData then
    return ← proofArgumentCongruence fuel a b.mdataExpr!
  if a == b then
    return ← Lean.Meta.mkAppM ``HEq.refl #[a]
  if ← Lean.Meta.isProof a then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
  if a.isApp && b.isApp && a.getAppFn == b.getAppFn then
    try
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if aa.size != ba.size then throwError "arity mismatch"
      let th ← Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
      let mut args : Array Lean.Expr := #[]
      for i in [:aa.size] do
        let h ← proofArgumentCongruence fuel aa[i]! ba[i]!
        let h ← if th.argKinds[i]! == Lean.Meta.CongrArgKind.eq then
            Lean.Meta.mkAppM ``eq_of_heq #[h]
          else pure h
        args := args ++ #[aa[i]!, ba[i]!, h]
      let out := Lean.mkAppN th.proof args
      let ty ← Lean.Meta.inferType out
      if ty.isEq then return ← Lean.Meta.mkAppM ``heq_of_eq #[out]
      return out
    catch _ => pure ()
  if ← Lean.Meta.isDefEq a b then
    return ← Lean.Meta.mkAppM ``HEq.refl #[a]
  throwError "nonapplication mismatch: {a} / {b}"

-- The site argument uses the finite rings through their functors only; keep
-- the large quotient-stage presentations out of its elaboration.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem coefficientSiteAssertion_proof
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (C : Compactification f)
    (hcompact : ∀ M : DerivedCategoryModule (ULift.{u + 1, u} A) X,
      IsIso (ExceptionalCoefficients.compactSupportMap
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        (⟨C.Z, C.g, C.i, rfl, inferInstance, inferInstance⟩ :
          Compactification (C.i ≫ C.g)) M)) :
    coefficientSiteAssertion A B φ C := by
  intro hFA hFB hSX hSV GA GB adjA adjB RA RB o ho c hb hc L
  let ψ := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let C' : Compactification (C.i ≫ C.g) :=
    ⟨C.Z, C.g, C.i, rfl, inferInstance, inferInstance⟩
  let FBi := ProEtale.reductionCompactSupport B C.i C.g
  let SY := ProEtale.scalarExtensionFunctor φ Y
  let SX := ProEtale.scalarExtensionFunctor φ X
  let M := RA.right.obj (RA.origin.obj L)
  let K := (ProEtale.reductionCtfScalar φ Y hSV).obj L
  let N := RB.right.obj (RB.origin.obj K)
  let eA := RA.rightIso.app L
  let eB := RB.rightIso.app K
  let q := ExceptionalCoefficients.compactSupportMap ψ C' M
  let b := (ProEtale.reductionDirectImageComparison φ C.i C.g).app (GA.obj L).obj
  let t := RB.adjunction.homEquiv _ _
    (ExceptionalCoefficients.comparisonInverse ψ C' M ≫
      (scalarExtension ψ Y).map (RA.adjunction.counit.app (RA.origin.obj L))) ≫
    RB.right.map (o.hom.app L)
  let z := (ProEtale.reductionSiteCompactSupportIso B C.i C.g).hom.app
    ⟨N, RB.right_plus K⟩ ≫
    (ProEtale.reductionSite B Y).map
      (RB.adjunction.counit.app (RB.origin.obj K)) ≫ RB.originIso.hom.app K
  let v := (ProEtale.reductionSiteScalarIso φ X).hom.app M ≫
    (ProEtale.reductionSite B X).map t
  let w := SX.map eA.hom ≫ v
  have hq : IsIso q := hcompact M
  have ht : q ≫ (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) C').map t ≫
      RB.adjunction.counit.app (RB.origin.obj K) =
    (scalarExtension ψ Y).map (RA.adjunction.counit.app (RA.origin.obj L)) ≫
      o.hom.app L := by
    have h := inverseTransposeCounit (hq := hq) RB.adjunction q
      ((scalarExtension ψ Y).map (RA.adjunction.counit.app (RA.origin.obj L)))
      (o.hom.app L)
    simpa only [t, q, K, Functor.comp_obj, comparisonInverse_eq_inv ψ C' M hq] using h
  have hs := ProEtale.reductionSiteCoefficientPasting φ C.i C.g M (RA.right_plus L)
    N (RB.right_plus K) t
  have hw : b ≫ FBi.map w ≫ z = SY.map (adjA.counit.app L).hom := by
    exact siteCounitPasting
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) C')
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) C')
      (ProEtale.reductionCompactSupport A C.i C.g) FBi
      (ProEtale.reductionSite A X) (ProEtale.reductionSite A Y)
      (ProEtale.reductionSite B X) (ProEtale.reductionSite B Y)
      (scalarExtension ψ X) (scalarExtension ψ Y) SX SY
      (ProEtale.reductionSiteScalarIso φ X)
      (ProEtale.reductionSiteScalarIso φ Y)
      (ProEtale.reductionDirectImageComparison φ C.i C.g) eA (o.app L)
      ((ProEtale.reductionSiteCompactSupportIso A C.i C.g).hom.app ⟨M, RA.right_plus L⟩)
      ((ProEtale.reductionSiteCompactSupportIso B C.i C.g).hom.app ⟨N, RB.right_plus K⟩)
      (RA.adjunction.counit.app (RA.origin.obj L))
      (RB.adjunction.counit.app (RB.origin.obj K))
      (RA.originIso.hom.app L) (RB.originIso.hom.app K)
      (adjA.counit.app L).hom q t (by
        have h := RA.counit L
        run_tac Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let d ← g.getDecl
          let mut last : Option Lean.LocalDecl := none
          for l in d.lctx do
            last := some l
          let some hdecl := last | throwError "missing hypothesis"
          let source ← Lean.Meta.whnf (← Lean.instantiateMVars hdecl.type)
          let target ← Lean.Meta.whnf (← Lean.instantiateMVars d.type)
          let he ← proofArgumentCongruence 100 source target
          let eq ← Lean.Meta.mkAppM ``eq_of_heq #[he]
          let result ← Lean.Meta.mkAppM ``Eq.mp #[eq, hdecl.toExpr]
          g.assign result
      ) (ho L) ht hs
  exact counitUniqueOfInjective (hb := hb L) FBi eB w (c.app L).hom
    (adjB.counit.app K).hom z b (SY.map (adjA.counit.app L).hom)
    (liftCounitInjective (ProEtale.spFiniteConstructibleTor X B)
      (ProEtale.spFiniteConstructibleTor Y B) FBi hFB GB adjB
        ((ProEtale.reductionCtfScalar φ X hSX).obj (GA.obj L)) K)
    (by
      have h := (RB.counit K).symm
      run_tac Lean.Elab.Tactic.withMainContext do
        let g ← Lean.Elab.Tactic.getMainGoal
        let d ← g.getDecl
        let mut last : Option Lean.LocalDecl := none
        for l in d.lctx do
          last := some l
        let some hdecl := last | throwError "missing hypothesis"
        let source ← Lean.Meta.whnf (← Lean.instantiateMVars hdecl.type)
        let target ← Lean.Meta.whnf (← Lean.instantiateMVars d.type)
        let he ← proofArgumentCongruence 100 source target
        let eq ← Lean.Meta.mkAppM ``eq_of_heq #[he]
        let result ← Lean.Meta.mkAppM ``Eq.mp #[eq, hdecl.toExpr]
        g.assign result
    ) (hc L) hw

-- Keep the normalization argument independent of quotient-ring presentations.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem ordinaryAffineProjectionAssertion
    (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hell : ell ≠ pchar)
    (k : Type u) [Field k] [CharP k pchar]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (r : ℕ) (hA : ((ell ^ r : ℕ) : A) = 0)
    (hB : ((ell ^ r : ℕ) : B) = 0)
    (V : Scheme.{u}) [IsNoetherian V] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (hN : IsUnit ((ell ^ r : ℕ) : Γ(V, ⊤)))
    (d : ℕ) : AffineProjectionCoefficientAssertion A B φ V d (ell ^ r) hA hB hN := by
  let : IsNoetherian (affineTraceTower V d) := affineTraceNoetherian V d
  intro tA DA tB DB L hL hTor
  let c := HasCompactification.compactification (affineTraceProjection V d)
  let FA := rightDerivedLowerShriek
    (ModuleCat.{u + 1} A) (affineTraceProjection V d)
  let FB := rightDerivedLowerShriek
    (ModuleCat.{u + 1} B) (affineTraceProjection V d)
  let γA := affineProjectionPurityIso _ V d _ hA hN tA DA
  let γB := affineProjectionPurityIso _ V d _ hB hN tB DB
  let adjA := rightDerivedUpperShriekAdjunction
    A (affineTraceProjection V d)
  let adjB := rightDerivedUpperShriekAdjunction
    B (affineTraceProjection V d)
  let Q := scalarExtension φ V
  let SX := scalarExtension φ (affineTraceTower V d)
  let a := ProEtale.reductionEtaleAffineScalarIso φ V _ hA hB hN d L
  have hc := etaleCompactScalarCoherence φ (affineTraceProjection V d) c
  have hq (M : DerivedCategoryModule A
      (affineTraceTower V d)) : IsIso (ExceptionalCoefficients.compactSupportMap φ c M) :=
    hc.1 M
  have hctf : ProEtale.AdjunctionTransfer.etaleProperty
      A V L := by
    refine ⟨hL, ?_⟩
    obtain ⟨a, b, h⟩ := hTor
    exact ⟨a, b, DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp h⟩
  obtain ⟨hV', hN', heq⟩ := affine_counit_scalar ell pchar hp (Ne.symm hell) k
    _ _ φ r hA hB V d c L hctf
  have hnorm : ExceptionalCoefficients.compactSupportMap φ c
      ((affineTraceRight _ _ hA V d).obj L) ≫ FB.map a.hom ≫
      FB.map (γB.hom.app (Q.obj L)) ≫ adjB.counit.app (Q.obj L) =
    Q.map (FA.map (γA.hom.app L) ≫ adjA.counit.app L) := by
    have hγA := (affineProjectionPurityIso_counit _ V d _ hA hN tA DA L).trans
      (affineScalarCounit_allData _ (pow_pos (Fact.out : ell.Prime).pos _) _ hA
        V hN d tA DA L)
    have hγB := (affineProjectionPurityIso_counit _ V d _ hB hN tB DB (Q.obj L)).trans
      (affineScalarCounit_allData _ (pow_pos (Fact.out : ell.Prime).pos _) _ hB
        V hN d tB DB (Q.obj L))
    apply normalizeCounitEquation Q (FA.map (γA.hom.app L)) (adjA.counit.app L) _
      _ (FB.map a.hom) (FB.map (γB.hom.app (Q.obj L)))
      (adjB.counit.app (Q.obj L)) _ hγA hγB
    simpa only [ProEtale.CoefficientCompatibility.etaleCoefficientMap_eq_compactScalarMap,
      compactScalarMap, a, FA, FB, Q, c, rightDerivedLowerShriek] using heq
  let qH := @asIso _ _ _ _
    (ExceptionalCoefficients.compactSupportMap φ c ((affineTraceRight _ _ hA V d).obj L))
    (hq _)
  let qG := @asIso _ _ _ _
    (ExceptionalCoefficients.compactSupportMap φ c
      ((rightDerivedUpperShriek A (affineTraceProjection V d)).obj L))
    (hq _)
  have hb : FB.map (ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L) ≫
      adjB.counit.app (Q.obj L) = qG.inv ≫ Q.map (adjA.counit.app L) := by
    have hh := (adjB.homEquiv _ _).symm_apply_apply
      (ExceptionalCoefficients.comparisonInverse φ c
        ((rightDerivedUpperShriek A (affineTraceProjection V d)).obj L) ≫
        Q.map (adjA.counit.app L))
    change FB.map (ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L) ≫
      adjB.counit.app (Q.obj L) = _ at hh
    simp only [qG, asIso_inv]
    dsimp only [ExceptionalCoefficients.comparisonInverse] at hh
    rw [dif_pos (hq _)] at hh
    exact hh
  have hn := compactScalarMap_naturality φ c (γA.hom.app L)
  change Q.map (FA.map (γA.hom.app L)) ≫ _ =
    _ ≫ FB.map (SX.map (γA.hom.app L)) at hn
  have hresult := normalizedMateComponent adjA adjB γA γB SX Q L qH qG a
    (ExceptionalCoefficients.mateMap φ (affineTraceProjection V d) L) hb
    (by simpa only [qH, qG, asIso_hom] using hn)
    (by simpa only [qH, asIso_hom, FA, FB, Q, rightDerivedLowerShriek, c] using hnorm)
  exact ⟨hq _, hresult.1, hresult.2⟩

/-- The actual ordinary-etale affine projection mate is invertible, is canonical
coefficient/Tate/shift reassociation under integration-normalized purity, and transports
to the specified constructible pro-etale coefficient mate. Levels m,n index m+1,n+1.
Source: blueprint main-20261015, sk-lem-sp-reduction-exceptional.proof.md, Charts
(blueprint: lem-pur-etale-affine-projection-coefficient-mate).

Proof: obtain the arithmetic and Noetherian witnesses from the affine integration
coefficient equation. Uniqueness of the normalized twist transport and P1 datum
identifies every allowed affine counit with the canonical one. The affine counit
scalar identity and compact scalar coherence then give the actual integration
normalization equation. Apply the inverse B-adjunction Hom bijection: naturality of
the compact scalar map and the right-adjoint uniqueness counit identity identify the
ordinary mate with the conjugate of canonical affine scalar reassociation. All three
factors are invertible. For the site clause, transpose the ordinary scalar counit,
compose with the given origin comparison, and use the intrinsic site/coefficient
pasting square. Naturality and the two realization counit equations show that its
conjugate satisfies exactly the intrinsic mate equation. Cancel the invertible
intrinsic coefficient map and apply the injective B-adjunction inverse Hom bijection. -/
theorem etaleAffineProjectionCoefficientMate
    (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hell : ell ≠ pchar)
    (k : Type u) [Field k] [CharP k pchar]
    (E F : Type u) [Field E] [Field F]
    [Algebra (Padic ell) E] [Algebra (Padic ell) F]
    [FiniteDimensional (Padic ell) E] [FiniteDimensional (Padic ell) F]
    (m n : ℕ)
    (φ : Padic.coefficientExtensionRing ell E (m + 1) →+*
      Padic.coefficientExtensionRing ell F (n + 1))
    (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (d : ℕ) :
    ∃ (hV : IsNoetherian V)
      (hA : ((ell ^ (max (m + 1) (n + 1)) : ℕ) :
        ULift.{u + 1, u} (Padic.coefficientExtensionRing ell E (m + 1))) = 0)
      (hB : ((ell ^ (max (m + 1) (n + 1)) : ℕ) :
        ULift.{u + 1, u} (Padic.coefficientExtensionRing ell F (n + 1))) = 0)
      (hN : IsUnit ((ell ^ (max (m + 1) (n + 1)) : ℕ) : Γ(V, ⊤))),
      @AffineProjectionCoefficientAssertion.{u} _ _ inferInstance inferInstance
        (vectorBundlePurityFiniteCoefficient ell E m)
        (vectorBundlePurityFiniteCoefficient ell F n)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) V hV d
        (ell ^ (max (m + 1) (n + 1))) hA hB hN ∧
      @ProEtale.AffineProjectionCoefficientSiteAssertion.{u} _ _ inferInstance inferInstance
        (Padic.finite_coefficientExtensionRing ell E (m + 1) (Nat.le_add_left 1 _))
        (Padic.finite_coefficientExtensionRing ell F (n + 1) (Nat.le_add_left 1 _)) φ V d
        (HasCompactification.compactification (affineTraceProjection V d)) := by
  let ψ := RingHom.ulift.{u + 1, u + 1, u, u} φ
  obtain ⟨hV, hN, hA, hB, _⟩ := AffineIntegrationCoefficient.equation
    ell pchar hp (Ne.symm hell) k E F m n ψ V d
  let := hV
  let : IsNoetherian (affineTraceTower V d) := affineTraceNoetherian V d
  refine ⟨hV, hA, hB, hN, ?_, ?_⟩
  · exact ordinaryAffineProjectionAssertion ell pchar hp hell k _ _ ψ _ hA hB V hN d
  · apply coefficientSiteAssertion_proof φ
      (HasCompactification.compactification (affineTraceProjection V d))
    intro M
    exact (etaleCompactScalarCoherence ψ _ _).1 M

end AlgebraicGeometry.Etale
