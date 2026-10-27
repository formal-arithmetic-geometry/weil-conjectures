/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralSystemReductionFullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.Paper.IntegralPullbackSystemComparison
import all Sheaf.Paper.IntegralAmbientOperationModels
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Projection-normalized integral reconstruction on a finite geometric fibre

Source: Bhatt--Scholze, Lemmas 3.5.7 and 6.7.2; Stacks Project, Tag 0941
(blueprint: lem-zl-finite-integral-fibre-reconstruction).All systems are objects of the derived
  category of strict semilinear systems.
The index n means the exponent n+1. The system exchange and germ maps below are
actual adjunction mates, and the integral comparisons retain their projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

set_option allowUnsafeReducibility true in
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor WeilConjectures.integralDerivedPullback
  HasDerivedCategory.standard
  AlgebraicGeometry.ProEtale.VaryingRing.pull AlgebraicGeometry.ProEtale.VaryingRing.push

namespace WeilConjectures.ZlFibreReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The published positive quotient rings, lifted to the site's coefficient size.
Source: Bhatt--Scholze, Section 6.5
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
abbrev rings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))

/-- The actual quotient transitions. Source: Bhatt--Scholze, Section 6.5
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
abbrev transition (n : ℕ) : rings l E (n + 1) ⟶ rings l E n :=
  CommRingCat.ofHom ((Padic.coefficientExtensionTransition l E (n + 1)).ulift)

/-- Exact inverse image on the recorded derived system category.
Source: Stacks 03D3, 0941 (blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  AlgebraicGeometry.ProEtale.VaryingRing.G (rings l E) (transition l E) f

/-- The total system direct image. Source: Stacks 079P, 0941
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  AlgebraicGeometry.ProEtale.VaryingRing.P (rings l E) (transition l E) f

/-- Completed integral direct image, as the total limit of the finite-image system.
Source: Bhatt--Scholze, Sections 6.5 and 6.7
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def image {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ⋙
    push l E f ⋙ coefficientSequenceLimit l E Y

/-- Geometric points over the specified point, including an empty fibre.
Source: blueprint finite-stalk paragraph
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
abbrev Points {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :=
  {x : s ⟶ X // x ≫ f = y}

/-- The unique lift to the chosen scheme pullback.
Source: Stacks 01JX (blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def pointLift {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) (x : Points f y) :
    s ⟶ Limits.pullback f y :=
  Limits.pullback.lift x.val (𝟙 s) (by simpa using x.property)

attribute [local irreducible] AlgebraicGeometry.ProEtale.VaryingRing.gComp
  AlgebraicGeometry.ProEtale.VaryingRing.adj

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The canonical system exchange: pullback commutation followed by the counit of f.
Source: Stacks 07A6; blueprint finite-stalk paragraph
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def exchange {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (M : coefficientSequenceDerived l E X) :
    (pull l E y).obj ((push l E f).obj M) ⟶
      (push l E (Limits.pullback.snd f y)).obj
        ((pull l E (Limits.pullback.fst f y)).obj M) :=
  ((AlgebraicGeometry.ProEtale.VaryingRing.adj (rings l E) (transition l E)
      (Limits.pullback.snd f y)).homEquiv _ _)
    ((AlgebraicGeometry.ProEtale.VaryingRing.gComp (rings l E) (transition l E)
        (Limits.pullback.snd f y) y).inv.app ((push l E f).obj M) ≫
      (eqToIso (congrArg (fun g ↦ pull l E g) (Limits.pullback.condition (f := f) (g :=
        y)).symm)).hom.app
        ((push l E f).obj M) ≫
      (AlgebraicGeometry.ProEtale.VaryingRing.gComp (rings l E) (transition l E)
        (Limits.pullback.fst f y) f).hom.app ((push l E f).obj M) ≫
      (pull l E (Limits.pullback.fst f y)).map
        ((AlgebraicGeometry.ProEtale.VaryingRing.adj (rings l E) (transition l E) f).counit.app M))

/-- A component of the counit-germ map, using h i_x = id and v i_x = x.
Source: Stacks 07A6; blueprint finite-stalk paragraph
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def germ {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (M : coefficientSequenceDerived l E X) (x : Points f y) :
    (push l E (Limits.pullback.snd f y)).obj
        ((pull l E (Limits.pullback.fst f y)).obj M) ⟶ (pull l E x.val).obj M :=
  (AlgebraicGeometry.ProEtale.VaryingRing.gId (rings l E) (transition l E) s).inv.app _ ≫
    (eqToIso (congrArg (fun g ↦ pull l E g)
      (Limits.pullback.lift_snd x.val (𝟙 s) (by simpa using x.property)).symm)).hom.app _ ≫
    (AlgebraicGeometry.ProEtale.VaryingRing.gComp (rings l E) (transition l E)
      (pointLift f y x) (Limits.pullback.snd f y)).hom.app _ ≫
    (pull l E (pointLift f y x)).map
      ((AlgebraicGeometry.ProEtale.VaryingRing.adj (rings l E) (transition l E)
        (Limits.pullback.snd f y)).counit.app _) ≫
    (AlgebraicGeometry.ProEtale.VaryingRing.gComp (rings l E) (transition l E)
      (pointLift f y x) (Limits.pullback.fst f y)).inv.app M ≫
    (eqToIso (congrArg (fun g ↦ pull l E g)
      (Limits.pullback.lift_fst x.val (𝟙 s) (by simpa using x.property)))).hom.app M

/-- The strict pullback reduction system, with its quotient transitions.
Source: Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def pullSystem {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E Y)) : coefficientSequenceDerived l E X :=
  (pull l E f).obj
    ((coefficientDerivedSystemEvaluationCalculus l E Y).choose.reduction.obj K)

/-- Evaluation identifies the pulled strict system with finite inverse image of K_n.
Source: Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def pullEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E X n).obj (pullSystem l E f K) ≅
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).obj
          ((scalarReductionDerivedExtension l E Y n).obj K) :=
  (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n).app
        ((coefficientDerivedSystemEvaluationCalculus l E Y).choose.reduction.obj K) ≪≫
    (proEtaleConstantRingDerivedPullback
      (Padic.coefficientExtensionRing l E (n + 1)) f).mapIso
        (((coefficientDerivedSystemEvaluationCalculus l E Y).choose.reductionEvaluation n).app K)

/-- Projection normalization for the completed pullback/total-system-limit comparison.
It uses the recorded canonical reduction isomorphism on every flat-term K-flat
representative. Its constructibility and residue-invertibility parameters are internal
universal tests: the theorem separately proves constructibility, and ell distinct from
the characteristic implies invertibility in every residue field of a k-scheme.
Source: Bhatt--Scholze, Lemma 3.5.7; Stacks 0941
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def PullNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (c : (integralDerivedPullback l E f).obj K ≅
      (coefficientSequenceLimit l E X).obj (pullSystem l E f K)) : Prop :=
  ∀ [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hK : sfIntegralConstructible l E Y K)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ),
    c.hom ≫ (coefficientSequenceProjection l E X n).app (pullSystem l E f K) =
      ((coefficientFiniteAdjunction l E X n).homEquiv _ _)
        ((integralSystemPullbackReductionIso l E f ⟨K, hK⟩ P e n).hom ≫
          (pullEvaluation l E f K n).inv)

/-- The system counit comparison induced by a normalized completed pullback comparison.
Source: Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def reductionComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (c : (integralDerivedPullback l E f).obj K ≅
      (coefficientSequenceLimit l E X).obj (pullSystem l E f K)) :=
  (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.map c.hom ≫
    (coefficientDerivedSystemEvaluationCalculus l E X).choose.adjunction.counit.app
      (pullSystem l E f K)

/-- The direct-image system of the strict reductions.
Source: Bhatt--Scholze, Lemma 6.7.2
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def imageSystem {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) :=
  (push l E f).obj
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.obj K)

/-- The two systems in the geometric-fibre exchange, prior to taking any limit.
Source: blueprint finite-stalk paragraph
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def exchangeSource {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) :=
  (pull l E y).obj (imageSystem l E f K)

/-- The finite-image system on the geometric fibre.
Source: blueprint finite-stalk paragraph
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def fibreSystem {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) :=
  (push l E (Limits.pullback.snd f y)).obj
    (pullSystem l E (Limits.pullback.fst f y) K)

/-- Total-limit identification of the iterated integral image, induced by the actual
pullback reduction counit. Source: Bhatt--Scholze, Lemmas 3.5.7 and 6.7.2
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def fibreComparison {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    (c : (integralDerivedPullback l E (Limits.pullback.fst f y)).obj K ≅
      (coefficientSequenceLimit l E (Limits.pullback f y)).obj
        (pullSystem l E (Limits.pullback.fst f y) K)) :=
  (coefficientSequenceLimit l E s).map
    ((push l E (Limits.pullback.snd f y)).map
      (reductionComparison l E (Limits.pullback.fst f y) K c))

/-- The comparison of y-pullback of the integral image with the exchange source.
It uses the system counit at F before applying total limit.
Source: Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def exchangeComparison {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    (c : (integralDerivedPullback l E y).obj ((image l E f).obj K) ≅
      (coefficientSequenceLimit l E s).obj
        (pullSystem l E y ((image l E f).obj K))) :=
  c.hom ≫ (coefficientSequenceLimit l E s).map
    ((pull l E y).map
      ((coefficientDerivedSystemEvaluationCalculus l E _).choose.adjunction.counit.app
        (imageSystem l E f K)))

/-- The canonical finite biproduct map of total limits, specified by its components.
Source: Stacks 0941 (blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def limitBiproduct {s : Scheme.{u}} {I : Type u} [Finite I]
    (T : I → coefficientSequenceDerived l E s) :
    (coefficientSequenceLimit l E s).obj (⨁ T) ⟶
      ⨁ (fun x ↦ (coefficientSequenceLimit l E s).obj (T x)) :=
  biproduct.lift (fun x ↦ (coefficientSequenceLimit l E s).map (biproduct.π T x))

/-- The counit-germ system arrow into its finite biproduct, with no nonempty assumption.
Source: blueprint finite-stalk paragraph
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def restriction {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) [Finite (Points f y)]
    (K : DerivedCategory (scalarReductionSource l E X)) :=
  biproduct.lift (fun x : Points f y ↦ germ l E f y
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.obj K) x)

/-- Finite sums of the actual completed-module complexes exist by finite products.
Source: Stacks 0941 (blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
instance complexFiniteBiproducts (s : Scheme.{u}) :
    HasFiniteBiproducts.{u + 1, u + 2}
      (CochainComplex (integralTowerModules.{u, u} l E s) ℤ) :=
  Abelian.hasFiniteBiproducts

/-- Tower finite sums are componentwise finite sums of complexes.
Source: Stacks 0941 (blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
instance towerFiniteBiproducts (s : Scheme.{u}) :
    HasFiniteBiproducts.{u + 1, u + 2}
      (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules.{u, u} l E s) ℤ) :=
  Abelian.hasFiniteBiproducts

/-- The finite strict point towers on one good representative.
Source: Stacks 0941; blueprint finite-stalk paragraph
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def pointTower {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) (x : Points f y) :=
  (integralOperationsPullbackTowerFunctor l E x.val).obj P.obj

/-- The strict finite Roos comparison, obtained from its component projections.
Source: Stacks 0941 (blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def roosBiproduct {s : Scheme.{u}} {I : Type u} [Finite I]
    (T : I → ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E s) ℤ) :
    integralOperationsRoos (⨁ T) ⟶ ⨁ (fun x ↦ integralOperationsRoos (T x)) :=
  biproduct.lift (fun x ↦ (integralOperationsRoosFunctor.map (biproduct.π T x)))

/-- Identity on sections identifies finite direct image with the canonical constant action.
Source: Stacks 03D3, 07A6
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def finitePushforwardModel {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    AlgebraicGeometry.ProEtale.StrictTower.moduleDirectImage (rings l E n) f ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) :=
  SheafOfModules.pushforwardCongr
    (congrArg (fun q ↦
      (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map q)
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
        (proEtaleCoefficientDirectImageMap f
          (Padic.coefficientExtensionRing l E (n + 1)))))

/-- System direct-image evaluation with its original constant-section scalar action.
Source: Stacks 07A6 (blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def imageEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E Y n).obj (imageSystem l E f K) ≅
      sfFiniteDerivedDirectImage l E f K n :=
  (AlgebraicGeometry.ProEtale.VaryingRing.evalP (rings l E) (transition l E) f n).app
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.obj K) ≪≫
    (Functor.rightDerivedFunctorNatIso (finitePushforwardModel l E f n)).app _ ≪≫
    (proEtaleConstantDerivedDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))).mapIso
        (((coefficientDerivedSystemEvaluationCalculus l E X).choose.reductionEvaluation n).app K)

/-- The normalized projection from the system-limit image to its restricted finite image.
Source: Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def imageProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  (coefficientSequenceProjection l E Y n).app (imageSystem l E f K) ≫
    (coefficientFiniteDerivedRestriction l E Y n).map (imageEvaluation l E f K n).hom

/-- Identification with the recorded tower direct image, preserving its actual projections.
Source: Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-zl-finite-integral-fibre-reconstruction). -/
def ImageNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) : Prop :=
  ∀ [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K),
    ∃ e : L.obj ≅ (image l E f).obj K,
      ∀ n : ℕ, e.hom ≫ imageProjection l E f K n =
        L.projection ≫ Pi.π (sfDirectImageTerm l E f K) n

/-- Integral finite geometric-fibre reconstruction with the actual system counits,
strict exchange and counit-germ maps, projection identities and naturality.
Source: Bhatt--Scholze, Lemmas 3.5.7 and 6.7.2; Stacks 0941
(blueprint: lem-zl-finite-integral-fibre-reconstruction).Proof, following the seven steps of the
  node:
1. Finite completed-image comparison gives constructibility and invertible reduction
comparisons. Integral operations preserve constructibility for v. Coherent pullback
reduction identifies the pullback system using the actual projection adjuncts.
For each k-scheme the image of ell is a unit in k since ell and p are distinct primes;
the structure map from k to each residue field transports that unit. Thus every
residue-invertibility test in PullNormalization is inhabited, without a new hypothesis.
Use the constructibility conclusions for its constructibility tests.
2. Form the reduction/total-limit counit at the finite-image system. Its evaluations
are the canonical reduction comparisons, so conservative evaluation makes it invertible
as a system map, including the quotient transitions.
3. Apply the same completed-image result to h and Lv*K. Counit naturality identifies
its composite with the pushforward of the v-comparison with the counit at h_*v*R(K).
4. The finite counit-restriction tower lemma gives finite P_y and the specified exchange
and germ system maps, with invertible evaluations. Their total limits are invertible.
The completed pullback definition and the first counit identify the source of b.
5. Exact sectionwise countable products give the strict Roos model. Reindex the finite
point coordinate and the countable level coordinate. This commutes with differential
and 1-s, hence with the signed cone and its shift, preserving every projection.
For an empty fibre both sides are zero and the comparison is the unique zero iso.
6. Compose the actual limit of the germ map with this finite biproduct comparison.
Each summand is completed point pullback by its normalized construction. Pullback
preservation gives integral constructibility, so both isomorphisms restrict to Dbc.
7. Naturality of limit projections for the strict exchange and germ maps gives the
stated projection equations. The counits, mates and finite coordinate comparison
are natural in K. Every construction precedes taking point sections. -/
theorem finite_integral_fibre_reconstruction
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (X Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] (y : Spec (.of D.k) ⟶ Y.left) :
    Finite (Points f.left y) ∧
    ∀ [Finite (Points f.left y)],
    ∃ (cv : ∀ K : sfIntegralConstructibleCategory l E X.left,
        (integralDerivedPullback l E (Limits.pullback.fst f.left y)).obj K.obj ≅
          (coefficientSequenceLimit l E (Limits.pullback f.left y)).obj
            (pullSystem l E (Limits.pullback.fst f.left y) K.obj))
      (cy : ∀ K : sfIntegralConstructibleCategory l E X.left,
        (integralDerivedPullback l E y).obj ((image l E f.left).obj K.obj) ≅
          (coefficientSequenceLimit l E (Spec (.of D.k))).obj
            (pullSystem l E y ((image l E f.left).obj K.obj)))
      (cx : ∀ (K : sfIntegralConstructibleCategory l E X.left) (x : Points f.left y),
        (integralDerivedPullback l E x.val).obj K.obj ≅
          (coefficientSequenceLimit l E (Spec (.of D.k))).obj (pullSystem l E x.val K.obj))
      (b : ∀ K : sfIntegralConstructibleCategory l E X.left,
        (integralDerivedPullback l E y).obj ((image l E f.left).obj K.obj) ≅
          (image l E (Limits.pullback.snd f.left y)).obj
            ((integralDerivedPullback l E (Limits.pullback.fst f.left y)).obj K.obj))
      (r : ∀ K : sfIntegralConstructibleCategory l E X.left,
        (image l E (Limits.pullback.snd f.left y)).obj
            ((integralDerivedPullback l E (Limits.pullback.fst f.left y)).obj K.obj) ≅
          ⨁ (fun x : Points f.left y ↦ (integralDerivedPullback l E x.val).obj K.obj)),
      (∀ K : sfIntegralConstructibleCategory l E X.left,
        sfIntegralConstructible l E Y.left ((image l E f.left).obj K.obj) ∧
        sfIntegralConstructible l E (Limits.pullback f.left y)
          ((integralDerivedPullback l E (Limits.pullback.fst f.left y)).obj K.obj) ∧
        sfIntegralConstructible l E (Spec (.of D.k))
          ((image l E (Limits.pullback.snd f.left y)).obj
            ((integralDerivedPullback l E (Limits.pullback.fst f.left y)).obj K.obj))) ∧
      (∀ K : sfIntegralConstructibleCategory l E X.left,
        ImageNormalization l E f.left K.obj ∧
        ImageNormalization l E (Limits.pullback.snd f.left y)
          ((integralDerivedPullback l E (Limits.pullback.fst f.left y)).obj K.obj)) ∧
      (∀ K : sfIntegralConstructibleCategory l E X.left,
        PullNormalization l E (Limits.pullback.fst f.left y) K.obj (cv K) ∧
        PullNormalization l E y ((image l E f.left).obj K.obj) (cy K) ∧
        ∀ x : Points f.left y, PullNormalization l E x.val K.obj (cx K x)) ∧
      (∀ K : sfIntegralConstructibleCategory l E X.left,
        IsIso ((coefficientDerivedSystemEvaluationCalculus l E
          Y.left).choose.adjunction.counit.app (imageSystem l E f.left K.obj)) ∧
        IsIso (reductionComparison l E (Limits.pullback.fst f.left y) K.obj (cv K)) ∧
        IsIso ((coefficientDerivedSystemEvaluationCalculus l E (Spec (.of
          D.k))).choose.reduction.map (fibreComparison l E f.left y K.obj (cv K)) ≫
          (coefficientDerivedSystemEvaluationCalculus l E (Spec (.of
            D.k))).choose.adjunction.counit.app (fibreSystem l E f.left y K.obj))) ∧
      (∀ K : sfIntegralConstructibleCategory l E X.left,
        (b K).hom ≫ fibreComparison l E f.left y K.obj (cv K) =
          exchangeComparison l E f.left y K.obj (cy K) ≫
            (coefficientSequenceLimit l E (Spec (.of D.k))).map
              (exchange l E f.left y
                ((coefficientDerivedSystemEvaluationCalculus l E X.left).choose.reduction.obj
                  K.obj))) ∧
      (∀ K : sfIntegralConstructibleCategory l E X.left,
        (r K).hom = fibreComparison l E f.left y K.obj (cv K) ≫
          (coefficientSequenceLimit l E (Spec (.of D.k))).map
            (restriction l E f.left y K.obj) ≫
          limitBiproduct l E (fun x : Points f.left y ↦ pullSystem l E x.val K.obj) ≫
          biproduct.map (fun x : Points f.left y ↦ (cx K x).inv)) ∧
      (∀ (K : sfIntegralConstructibleCategory l E X.left) (n : ℕ),
        (b K).hom ≫ fibreComparison l E f.left y K.obj (cv K) ≫
          (coefficientSequenceProjection l E (Spec (.of D.k)) n).app
            (fibreSystem l E f.left y K.obj) =
        exchangeComparison l E f.left y K.obj (cy K) ≫
          (coefficientSequenceProjection l E (Spec (.of D.k)) n).app
            (exchangeSource l E f.left y K.obj) ≫
          (coefficientFiniteDerivedRestriction l E (Spec (.of D.k)) n).map
            ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map
              (exchange l E f.left y
                ((coefficientDerivedSystemEvaluationCalculus l E X.left).choose.reduction.obj
                  K.obj)))) ∧
      (∀ (K : sfIntegralConstructibleCategory l E X.left) (x : Points f.left y) (n : ℕ),
        (r K).hom ≫ biproduct.π
            (fun z : Points f.left y ↦ (integralDerivedPullback l E z.val).obj K.obj) x ≫
          (cx K x).hom ≫ (coefficientSequenceProjection l E (Spec (.of D.k)) n).app
            (pullSystem l E x.val K.obj) =
        fibreComparison l E f.left y K.obj (cv K) ≫
          (coefficientSequenceProjection l E (Spec (.of D.k)) n).app
            (fibreSystem l E f.left y K.obj) ≫
          (coefficientFiniteDerivedRestriction l E (Spec (.of D.k)) n).map
            ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map
              (germ l E f.left y
                ((coefficientDerivedSystemEvaluationCalculus l E X.left).choose.reduction.obj
                  K.obj) x))) ∧
      (∀ K : sfIntegralConstructibleCategory l E X.left,
        IsIso (limitBiproduct l E (fun x : Points f.left y ↦ pullSystem l E x.val K.obj))) ∧
      (∀ (K L : sfIntegralConstructibleCategory l E X.left) (a : K ⟶ L),
        (integralDerivedPullback l E y).map ((image l E f.left).map a.hom) ≫ (b L).hom =
          (b K).hom ≫ (image l E (Limits.pullback.snd f.left y)).map
            ((integralDerivedPullback l E (Limits.pullback.fst f.left y)).map a.hom)) ∧
      (∀ (K L : sfIntegralConstructibleCategory l E X.left) (a : K ⟶ L),
        (image l E (Limits.pullback.snd f.left y)).map
            ((integralDerivedPullback l E (Limits.pullback.fst f.left y)).map a.hom) ≫
          (r L).hom = (r K).hom ≫ biproduct.map
            (fun x : Points f.left y ↦ (integralDerivedPullback l E x.val).map a.hom)) := by
  sorry

attribute [local implicit_reducible] integralOperationsRoosFunctor integralOperationsRoos

private abbrev towerProductFunctor {A : Type*} [Category* A] [Abelian A]
    [HasCountableProducts A] : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ where
  obj T := ∏ᶜ (fun n : ℕ ↦ T.obj (op n))
  map a := Limits.Pi.map (fun n : ℕ ↦ a.app (op n))
  map_id T := by apply Pi.hom_ext; intro n; simp
  map_comp a b := by apply Pi.hom_ext; intro n; simp

private instance towerProductFunctor_additive {A : Type*} [Category* A] [Abelian A]
    [HasCountableProducts A] : (towerProductFunctor (A := A)).Additive where
  map_add {U V a b} := by
    apply Pi.hom_ext
    intro n
    simp [towerProductFunctor, Preadditive.add_comp, Preadditive.comp_add]

private theorem roos_hom_ext {A : Type*} [Category* A] [Abelian A]
    [HasCountableProducts A] {T : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    {P : CochainComplex A ℤ} (a b : P ⟶ integralOperationsRoos T)
    (hf : a ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary T) =
      b ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary T))
    (hs : ∀ i : ℤ, a.f i ≫ (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary T)).v i (i - 1) (by omega) =
      b.f i ≫ (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary T)).v i (i - 1) (by omega)) : a = b := by
  ext i : 1
  have hfi := congrArg (fun z ↦ z.f i) hf
  change a.f i ≫ _ = b.f i ≫ _ at hfi
  have hid := CochainComplex.mappingCocone.id_X (scalarRoosBoundary T) i (i - 1)
    (by omega)
  have ha := congrArg (fun z ↦ a.f i ≫ z) hid
  have hb := congrArg (fun z ↦ b.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at ha hb
  rw [hfi, hs i] at ha
  simpa only [integralOperationsRoos, Category.comp_id] using ha.symm.trans hb

private instance roosFunctor_additive {A : Type*} [Category* A] [Abelian A]
    [HasCountableProducts A] : (integralOperationsRoosFunctor (A := A)).Additive where
  map_add {U V a b} := by
    apply roos_hom_ext
    · dsimp only [integralOperationsRoosFunctor]
      rw [(IntegralAmbient.roosMap_coordinates (a + b)).1]
      simp only [Preadditive.add_comp, (IntegralAmbient.roosMap_coordinates a).1,
        (IntegralAmbient.roosMap_coordinates b).1]
      have hp := (towerProductFunctor (A := A)).map_add (f := a) (g := b)
      change Limits.Pi.map (fun n : ℕ ↦ (a + b).app (op n)) =
        Limits.Pi.map (fun n : ℕ ↦ a.app (op n)) + Limits.Pi.map (fun n : ℕ ↦ b.app (op n)) at hp
      rw [hp, Preadditive.comp_add]
    · intro i
      dsimp only [integralOperationsRoosFunctor]
      rw [(IntegralAmbient.roosMap_coordinates (a + b)).2 i (i - 1) (by omega)]
      simp only [HomologicalComplex.add_f_apply, Preadditive.add_comp,
        (IntegralAmbient.roosMap_coordinates a).2 i (i - 1) (by omega),
        (IntegralAmbient.roosMap_coordinates b).2 i (i - 1) (by omega)]
      have hp := congrArg (fun z ↦ z.f (i - 1))
        ((towerProductFunctor (A := A)).map_add (f := a) (g := b))
      dsimp only [towerProductFunctor, HomologicalComplex.add_f_apply] at hp
      rw [hp, Preadditive.comp_add]

attribute [local instance] Abelian.hasFiniteBiproducts

private theorem finite_roos_comparison {A : Type*} [Category* A] [Abelian A]
    [HasCountableProducts A] {I : Type*} [Finite I]
    (T : I → ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    IsIso (integralOperationsRoosFunctor.biproductComparison T) ∧
    (∃ α : (∏ᶜ (fun n : ℕ ↦ (⨁ (T)).obj (op n))) ≅
        ⨁ (fun x : I ↦ ∏ᶜ (fun n : ℕ ↦ (T x).obj (op n))),
      (∀ (x : I) (n : ℕ),
        α.hom ≫ biproduct.π
            (fun z : I ↦ ∏ᶜ (fun m : ℕ ↦ (T z).obj (op m))) x ≫
          Pi.π (fun m : ℕ ↦ (T x).obj (op m)) n =
        Pi.π (fun m : ℕ ↦ (⨁ (T)).obj (op m)) n ≫
          (biproduct.π (T) x).app (op n)) ∧
      towerTransitionEndomorphism
          (K := fun n : ℕ ↦ (⨁ (T)).obj (op n))
          (integralOperationsTowerStep (⨁ (T))) ≫ α.hom =
        α.hom ≫ biproduct.map (fun x : I ↦
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ (T x).obj (op n))
            (integralOperationsTowerStep (T x)))) ∧
    (∀ n : ℕ,
      integralOperationsRoosFunctor.biproductComparison T ≫ biproduct.lift
          (fun x : I ↦ biproduct.π
            (fun z : I ↦ integralOperationsRoos (T z)) x ≫
            CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun m : ℕ ↦ (T x).obj (op m))
              (integralOperationsTowerStep (T x))) ≫
            Pi.π (fun m : ℕ ↦ (T x).obj (op m)) n) =
        CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun m : ℕ ↦ (⨁ (T)).obj (op m))
              (integralOperationsTowerStep (⨁ (T)))) ≫
          Pi.π (fun m : ℕ ↦ (⨁ (T)).obj (op m)) n ≫
          biproduct.lift (fun x : I ↦
            (biproduct.π (T) x).app (op n))) ∧
    (IsEmpty (I) →
      IsZero (integralOperationsRoos (⨁ (T))) ∧
      IsZero (⨁ (fun x : I ↦ integralOperationsRoos (T x))) ∧
      ∀ e : integralOperationsRoos (⨁ (T)) ≅
          ⨁ (fun x : I ↦ integralOperationsRoos (T x)),
        e.hom = integralOperationsRoosFunctor.biproductComparison T) := by
  let F := integralOperationsRoosFunctor (A := A)
  have hr : IsIso (F.biproductComparison T) := by
    change IsIso ((F.mapBiproduct T).hom)
    infer_instance
  refine ⟨hr, ?_, ?_, ?_⟩
  · refine ⟨towerProductFunctor.mapBiproduct T, ?_, ?_⟩
    · intro x n
      change (towerProductFunctor.mapBiproduct T).hom ≫ biproduct.π _ x ≫ Pi.π _ n = _
      have hx := Functor.biproductComparison_π towerProductFunctor T x
      have hn := congrArg (fun a ↦ a ≫ Pi.π (fun m : ℕ ↦ (T x).obj (op m)) n) hx
      exact (Category.assoc _ _ _).symm.trans
        (hn.trans (Pi.map_π (fun m : ℕ ↦ (biproduct.π T x).app (op m)) n))
    · apply biproduct.hom_ext
      intro x
      simp only [Category.assoc, biproduct.map_π]
      rw [Functor.mapBiproduct_hom, biproduct.lift_π,
        biproduct.lift_π_assoc]
      exact integralOperationsRoos_square (biproduct.π T x)
  · intro n
    apply biproduct.hom_ext
    intro x
    simp only [Category.assoc, biproduct.lift_π]
    have hx := Functor.biproductComparison_π integralOperationsRoosFunctor T x
    have hn := congrArg (fun a ↦ a ≫
      CochainComplex.mappingCocone.fst (scalarRoosBoundary (T x)) ≫
        Pi.π (fun m : ℕ ↦ (T x).obj (op m)) n) hx
    refine (Category.assoc _ _ _).symm.trans (hn.trans ?_)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a ↦ a ≫ Pi.π (fun m : ℕ ↦ (T x).obj (op m)) n)
        (IntegralAmbient.roosMap_coordinates (biproduct.π T x)).1).trans
          (by simp only [Category.assoc, Pi.map_π]))
  · intro h
    let := h
    have hz : IsZero (⨁ (fun x : I ↦ integralOperationsRoos (T x))) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply biproduct.hom_ext
      intro x
      exact isEmptyElim x
    have hs : IsZero (integralOperationsRoos (⨁ T)) :=
      hz.of_iso (asIso (F.biproductComparison T))
    exact ⟨hs, hz, fun e ↦ hs.eq_of_src _ _⟩

/-- The finite Roos comparison is the coordinate reindexing on both cone products.
Its source towers are the actual restricted finite point pullbacks on one flat-term
K-flat representative. The chain-map type retains the differentials; the displayed
square retains 1-s, and roosBiproduct applies the same product maps on both shifted
cone coordinates. The empty comparison is uniquely the zero-object isomorphism.
Source: Stacks 0941, elementary finite-coordinate reindexing; node proof step 5
(blueprint: lem-zl-finite-integral-fibre-reconstruction).Proof: write a product coordinate as
  (x,n). Finite support in x is automatic.
Reindex (t_(x,n))_n as ((t_(x,n))_n)_x, with the reverse reindexing as inverse.
The coefficient differential and tower transition each act on the same coordinate,
so the comparison commutes with d and 1-s. Apply it on both products in the cone;
this preserves the signed cone differential and the shift [-1]. The x projection
is the Roos map of the x tower projection, hence gives exactly roosBiproduct.
The nth projection and all (x,n) coordinates are unchanged. For an empty fibre,
every finite sum and product of its zero complexes is zero, so the comparison
is the only morphism and the unique isomorphism between these zero objects. -/
theorem finite_integral_fibre_roos
    {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) [Finite (Points f y)]
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    IsIso (roosBiproduct l E (pointTower l E f y P)) ∧
    (∃ α : (∏ᶜ (fun n : ℕ ↦ (⨁ (pointTower l E f y P)).obj (op n))) ≅
        ⨁ (fun x : Points f y ↦ ∏ᶜ (fun n : ℕ ↦ (pointTower l E f y P x).obj (op n))),
      (∀ (x : Points f y) (n : ℕ),
        α.hom ≫ biproduct.π
            (fun z : Points f y ↦ ∏ᶜ (fun m : ℕ ↦ (pointTower l E f y P z).obj (op m))) x ≫
          Pi.π (fun m : ℕ ↦ (pointTower l E f y P x).obj (op m)) n =
        Pi.π (fun m : ℕ ↦ (⨁ (pointTower l E f y P)).obj (op m)) n ≫
          (biproduct.π (pointTower l E f y P) x).app (op n)) ∧
      towerTransitionEndomorphism
          (K := fun n : ℕ ↦ (⨁ (pointTower l E f y P)).obj (op n))
          (integralOperationsTowerStep (⨁ (pointTower l E f y P))) ≫ α.hom =
        α.hom ≫ biproduct.map (fun x : Points f y ↦
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ (pointTower l E f y P x).obj (op n))
            (integralOperationsTowerStep (pointTower l E f y P x)))) ∧
    (∀ n : ℕ,
      roosBiproduct l E (pointTower l E f y P) ≫ biproduct.lift
          (fun x : Points f y ↦ biproduct.π
            (fun z : Points f y ↦ integralOperationsRoos (pointTower l E f y P z)) x ≫
            CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun m : ℕ ↦ (pointTower l E f y P x).obj (op m))
              (integralOperationsTowerStep (pointTower l E f y P x))) ≫
            Pi.π (fun m : ℕ ↦ (pointTower l E f y P x).obj (op m)) n) =
        CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun m : ℕ ↦ (⨁ (pointTower l E f y P)).obj (op m))
              (integralOperationsTowerStep (⨁ (pointTower l E f y P)))) ≫
          Pi.π (fun m : ℕ ↦ (⨁ (pointTower l E f y P)).obj (op m)) n ≫
          biproduct.lift (fun x : Points f y ↦
            (biproduct.π (pointTower l E f y P) x).app (op n))) ∧
    (IsEmpty (Points f y) →
      IsZero (integralOperationsRoos (⨁ (pointTower l E f y P))) ∧
      IsZero (⨁ (fun x : Points f y ↦ integralOperationsRoos (pointTower l E f y P x))) ∧
      ∀ e : integralOperationsRoos (⨁ (pointTower l E f y P)) ≅
          ⨁ (fun x : Points f y ↦ integralOperationsRoos (pointTower l E f y P x)),
        e.hom = roosBiproduct l E (pointTower l E f y P)) := by
  exact finite_roos_comparison (pointTower l E f y P)

end WeilConjectures.ZlFibreReconstruction
