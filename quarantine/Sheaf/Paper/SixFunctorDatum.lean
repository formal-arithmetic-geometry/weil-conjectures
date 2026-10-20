/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
public import Sheaf.CategoryTheory.RingedSitePerfectDuality
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# Axiomatized six-functor data

Source: current blueprint main-20261015, sec-proetale-coefficients,
sk-def-sf-operations/def-sf-datum, axioms (A1)--(A6) (blueprint: def-sf-datum).

The operation datum fixes the actual coefficient categories and constructions.
The structures below impose properties on those operations; they do not assert
that a concrete six-functor datum exists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w a b a' b'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.SuppliedExchangeProjection
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The inherited finite bounded-constructible triangulation, from the recorded
closure theorem, not a new triangulation. Source: the finite-Tor domain convention
of A6 (blueprint: def-sf-datum). -/
instance sixFunctorBoundedTriangulated
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) (X : SixFunctorSpace D) :
    ObjectProperty.IsTriangulated (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left) :=
  (@proEtale_bounded_constructible_isTriangulated X.obj.left
    (Padic.coefficientExtensionRing C.l E n) _
    (Padic.finite_coefficientExtensionRing C.l E n hn)).2

/-- Reassociate the same compactification, transporting only its factorization.
Source: the associativity convention in A4 (blueprint: def-sf-datum). -/
def sixFunctorAssocCompactification {D : FiniteFieldDatum.{u}}
    {W X Y Z : SixFunctorSpace D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (c : Compactification ((f ≫ g) ≫ h).hom.left) :
    Compactification (f ≫ g ≫ h).hom.left :=
  (congrArg (fun e : W ⟶ Z ↦ e.hom.left) (Category.assoc f g h)) ▸ c

/-- Direct-image composition is the unique right-adjoint mate of pullback composition.
Consequently the comparison uses the pasted unit and counit, rather than another
adjunction on the same functors. Source: A1 (blueprint: def-sf-datum). -/
def sixFunctorDirectComposition {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) : S.direct (f ≫ g) ≅ S.direct f ⋙ S.direct g :=
  (S.pullDirectAdjunction (f ≫ g)).rightAdjointUniq
    (((S.pullDirectAdjunction g).comp (S.pullDirectAdjunction f)).ofNatIsoLeft
      (S.pullComposition f g).symm)

/-- Exceptional composition is the unique right-adjoint mate of the supplied support
composition; its units and counits are the pasted ones.
Source: A1 and A4 (blueprint: def-sf-datum). -/
def sixFunctorExceptionalComposition {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) :
    S.exceptional (f ≫ g) cfg ≅ S.exceptional g cg ⋙ S.exceptional f cf :=
  (S.exceptionalAdjunction (f ≫ g) cfg).rightAdjointUniq
    (((S.exceptionalAdjunction f cf).comp (S.exceptionalAdjunction g cg)).ofNatIsoLeft
      (S.composition f g cf cg cfg).symm)

/-- Finite-Tor preservation and the support pentagon. Adjunctions and proper coincidence
are already fields of S; their composition comparisons are the mates defined above.
The pentagon is written on components, including the canonical associativity transport.
Source: A1 and A4 on their displayed domains (blueprint: def-sf-datum). -/
structure SixFunctorCoherentStage {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (P : ∀ X, ObjectProperty (B X)) where
  pullDomain : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (K : B Y), P Y K → P X ((S.pull f).obj K)
  directDomain : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (K : B X), P X K → P Y ((S.direct f).obj K)
  supportDomain : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : B X), P X K → P Y ((S.support f c).obj K)
  exceptionalDomain : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : B Y), P Y K → P X ((S.exceptional f c).obj K)
  pentagon : ∀ {W X Y Z : SixFunctorSpace D}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : B W), P W K →
    HEq ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K))
      ((S.composition f (g ≫ h) cf cgh
        (sixFunctorAssocCompactification f g h cfgh)).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K))

/-- The supplied higher-stage exchange and projection maps are invertible on finite-Tor
inputs; the direct-image exchange has exactly the proper-or-smooth alternative.
Source: A2 and A3 (blueprint: def-sf-datum). -/
structure SixFunctorExchangeAxioms {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ X, ObjectProperty (B X)) : Prop where
  compactExchange : ∀ (Q : SixFunctorCompactifiedSquare D) (K : B Q.X), P Q.X K →
    IsIso ((A Q).stage.compactExchange.app K)
  directExchange : ∀ (Q : SixFunctorCompactifiedSquare D) (K : B Q.X), P Q.X K →
    (IsProper Q.f.hom.left ∨ Smooth Q.g.hom.left) → IsIso ((A Q).stage.exchange.app K)
  projection : ∀ (Q : SixFunctorCompactifiedSquare D) (K : B Q.X) (L : B Q.Y),
    P Q.X K → P Q.Y L → IsIso ((A Q).projectionComponent K L)

/-- The restriction of the actual partial internal Hom to finite-Tor pairs.
No replacement bifunctor is supplied. Source: the Hom domain of A6
(blueprint: def-sf-datum). -/
def sixFunctorDomainHom {B : Type a} [Category.{b} B]
    (P : ObjectProperty B) (Q : ObjectProperty (Bᵒᵖ × B))
    (H : Q.FullSubcategory ⥤ B)
    (hq : ∀ K L : P.FullSubcategory, Q (op K.obj, L.obj))
    (hp : ∀ K L : P.FullSubcategory,
      P (H.obj ⟨(op K.obj, L.obj), hq K L⟩)) :
    (P.FullSubcategory)ᵒᵖ × P.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (Q.lift (P.ι.op.prod P.ι) (fun KL ↦ hq KL.1.unop KL.2) ⋙ H)
    (fun KL ↦ hp KL.1.unop KL.2)

/-- A closed presentation of the actual tensor and internal Hom on the finite-Tor
category. Normalization to coefficient models is imposed by the datum below.
Source: the six operations and A6 (blueprint: def-sf-datum). -/
structure SixFunctorClosedDomain {B : Type a} [Category.{b} B]
    (P : ObjectProperty B) (Q : ObjectProperty (Bᵒᵖ × B))
    (H : Q.FullSubcategory ⥤ B) where
  homPermitted : ∀ K L : P.FullSubcategory, Q (op K.obj, L.obj)
  homDomain : ∀ K L : P.FullSubcategory,
    P (H.obj ⟨(op K.obj, L.obj), homPermitted K L⟩)
  closed : CoefficientClosedStructure (sixFunctorDomainHom P Q H homPermitted homDomain)
  symmetric : @SymmetricCategory _ _ closed.monoidal

/-- Closed-model comparisons preserve the actual evaluation and signed interchange.
These equations determine the transported double-dual arrow, including coefficient
change. Source: A5 and Verdier biduality in A6 (blueprint: def-sf-datum). -/
structure SixFunctorClosedComparison
    {B : Type a} [Category.{b} B] {B' : Type a'} [Category.{b'} B']
    {H : Bᵒᵖ × B ⥤ B} {H' : B'ᵒᵖ × B' ⥤ B'}
    (S : CoefficientClosedStructure H) (s : @SymmetricCategory _ _ S.monoidal)
    (S' : CoefficientClosedStructure H') (s' : @SymmetricCategory _ _ S'.monoidal)
    (F : B ⥤ B') where
  hom : H ⋙ F ≅ (F.op.prod F) ⋙ H'
  tensor : S.tensor ⋙ F ≅ (F.prod F) ⋙ S'.tensor
  evaluation : ∀ K L : B,
    (tensor.hom.app (H.obj (op K, L), K)) ≫
      S'.tensor.map (Prod.mkHom (hom.hom.app (op K, L)) (𝟙 (F.obj K))) ≫
      S'.evaluation (F.obj K) (F.obj L) = F.map (S.evaluation K L)
  symmetry : ∀ K L : B,
    F.map (s.braiding K L).hom ≫ tensor.hom.app (L, K) =
      tensor.hom.app (K, L) ≫ (s'.braiding (F.obj K) (F.obj L)).hom

/-- Restrict an actual coefficient-change functor to the finite-Tor domains.
Source: A5 on its displayed domains (blueprint: def-sf-datum). -/
def sixFunctorDomainChange {B : Type a} [Category.{b} B]
    {B' : Type a'} [Category.{b'} B'] (P : ObjectProperty B) (P' : ObjectProperty B')
    (F : B ⥤ B') (h : ∀ K : P.FullSubcategory, P' (F.obj K.obj)) :
    P.FullSubcategory ⥤ P'.FullSubcategory :=
  P'.lift (P.ι ⋙ F) h

/-- Coefficient compatibility of tensor, internal Hom, evaluation and signed symmetry
on the actual finite-Tor domains. The functor is the specified reduction, localization,
scalar transition or realization, and the comparisons preserve evaluation, rather than
merely comparing unrelated objects. Together with the operation datum's adjunction and
compositor equations these are the compatibility diagrams for the composites in A2--A3
and the evaluation transpose in A6.
Source: A5 (blueprint: def-sf-datum). -/
structure SixFunctorClosedChange
    {B : Type a} [Category.{b} B] {B' : Type a'} [Category.{b'} B']
    {P : ObjectProperty B} {P' : ObjectProperty B'}
    {Q : ObjectProperty (Bᵒᵖ × B)} {Q' : ObjectProperty (B'ᵒᵖ × B')}
    {H : Q.FullSubcategory ⥤ B} {H' : Q'.FullSubcategory ⥤ B'}
    (M : SixFunctorClosedDomain P Q H) (M' : SixFunctorClosedDomain P' Q' H')
    (F : B ⥤ B') where
  domain : ∀ K : P.FullSubcategory, P' (F.obj K.obj)
  comparison : SixFunctorClosedComparison M.closed M.symmetric M'.closed M'.symmetric
    (sixFunctorDomainChange P P' F domain)

/-- Exact anti-equivalence with invertible evaluation-transpose biduality.
The shift and triangles are the inherited ones on P, including the opposite
triangulation. Source: A6 (blueprint: def-sf-datum). -/
structure SixFunctorVerdierAxioms {B : Type a} [Category.{b} B]
    [HasZeroObject B] [Preadditive B] [HasShift B ℤ]
    [∀ i : ℤ, (shiftFunctor B i).Additive] [Pretriangulated B]
    (P : ObjectProperty B) [P.IsTriangulated]
    {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}
    (M : SixFunctorClosedDomain P Q H) (omega : B) where
  omegaDomain : P omega
  [commShift : ((Functor.curry.obj
    (sixFunctorDomainHom P Q H M.homPermitted M.homDomain)).flip.obj
      ⟨omega, omegaDomain⟩).CommShift ℤ]
  exact : ((Functor.curry.obj
    (sixFunctorDomainHom P Q H M.homPermitted M.homDomain)).flip.obj
      ⟨omega, omegaDomain⟩).IsTriangulated
  equivalence : ((Functor.curry.obj
    (sixFunctorDomainHom P Q H M.homPermitted M.homDomain)).flip.obj
      ⟨omega, omegaDomain⟩).IsEquivalence
  biduality : ∀ K : P.FullSubcategory,
    IsIso (CategoryTheory.ringedSiteBidual M.closed M.symmetric ⟨omega, omegaDomain⟩ K)

/-- The standard localization used by the ambient coefficient categories.
Source: A6, ordinary derived categories (blueprint: def-sf-datum). -/
abbrev sixFunctorRingedModel {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max a b u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max a b u}]
    (R : Sheaf J CommRingCat.{max a b u}) :=
  @RingedSiteDualityModel.{a, b, u, max a b u + 1} C _ J _ _ R
    (HasDerivedCategory.standard _)

/-- An evaluation-normalized embedding of a finite-Tor closed presentation into the
ordinary ringed-site derived category. The identity component fixes Hom coordinates;
evaluation and Koszul symmetry then fix the canonical bidual arrow.
Source: A6 (blueprint: def-sf-datum). -/
structure SixFunctorAmbientClosedModel
    {B : Type a} [Category.{b} B] {A : Type a'} [Category.{b'} A]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B}
    (M : SixFunctorClosedDomain P Q H)
    {H' : Aᵒᵖ × A ⥤ A} (N : CoefficientClosedStructure H')
    (s : @SymmetricCategory _ _ N.monoidal) (F : B ⥤ A) where
  comparison : SixFunctorClosedComparison M.closed M.symmetric N s (P.ι ⋙ F)
  homIdentity : ∀ K L : P.FullSubcategory,
    HEq (comparison.hom.hom.app (op K, L))
      (𝟙 (F.obj (H.obj ⟨(op K.obj, L.obj), M.homPermitted K L⟩)))

/-- Integral and rational closed models at a finite coefficient field, normalized
by the ordinary integral ringed-site model and the actual rationalization functor.
This anchors the common-stage comparisons to the same signed evaluation as the finite
and integral coefficients. Source: A5--A6 (blueprint: def-sf-datum). -/
structure SixFunctorCoefficientClosedModels
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) where
  integral : SixFunctorClosedDomain
    (fun K : sfIntegralConstructibleCategory l E X ↦ finiteTorConstructibleIntegral l E X K.obj)
    (constructibleIntegralHomPairs l E X) (constructibleIntegralHom l E X)
  model : sixFunctorRingedModel.{u, u+1, u} (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X)
  realization : SixFunctorAmbientClosedModel integral model.closed model.symmetric
    (sfIntegralConstructible l E X).ι
  rational : SixFunctorClosedDomain
    (⊤ : ObjectProperty (sfRationalConstructibleCategory l E X))
    (constructibleRationalHomPairs l E X) (rationalDerivedInternalHom l E X)
  rationalization : SixFunctorClosedChange integral rational
    (sfRationalConstructibleLocalization l E X)

/-- All six-functor axioms, on the recorded coefficient categories and finite-Tor
subcategories. A1 uses the adjunctions of the operation datum and the unique mates
`sixFunctorDirectComposition` and `sixFunctorExceptionalComposition`. A4 adds the
pentagon to its supplied compactification and proper comparisons. A5 uses actual
reduction, localization, scalar and realization comparisons, including the three
maps of A2--A3. A6 requires the exact anti-equivalence and the normalized evaluation
transpose to be invertible. No existence or verification theorem is asserted.
Source: current blueprint def-sf-datum, A1--A6 (blueprint: def-sf-datum). -/
structure SixFunctorDatum
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    extends SixFunctorOperationDatum D C E n hn where
  finiteCoherence : SixFunctorCoherentStage finite (toSixFunctorOperationDatum.finiteTorDomain)
  integralCoherence : SixFunctorCoherentStage higher.integral
    (toSixFunctorOperationDatum.integralFiniteTorDomain)
  rationalCoherence : SixFunctorCoherentStage higher.rational (fun _ ↦ ⊤)
  commonCoherence : SixFunctorCoherentStage closure.commonStage (fun _ ↦ ⊤)
  finiteCompactExchange : ∀ (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X),
    toSixFunctorOperationDatum.finiteTorDomain Q.X K →
    IsIso ((toSixFunctorOperationDatum.finiteExchangeProjection Q).2.1.app K)
  finiteDirectExchange : ∀ (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X),
    toSixFunctorOperationDatum.finiteTorDomain Q.X K →
    (IsProper Q.f.hom.left ∨ Smooth Q.g.hom.left) →
    IsIso ((toSixFunctorOperationDatum.finiteExchangeProjection Q).1.app K)
  finiteProjection : ∀ (Q : SixFunctorCompactifiedSquare D)
    (K : finiteTorConstructibleCategory C.l E n hn Q.X.obj.left)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left),
    IsIso (((toSixFunctorOperationDatum.finiteExchangeProjection Q).2.2.app K).app L)
  integralExchange : SixFunctorExchangeAxioms higher.integralExchange
    (toSixFunctorOperationDatum.integralFiniteTorDomain)
  rationalExchange : SixFunctorExchangeAxioms higher.rationalExchange (fun _ ↦ ⊤)
  commonExchange : SixFunctorExchangeAxioms closure.commonStageExchange (fun _ ↦ ⊤)
  finiteClosed : ∀ X : SixFunctorSpace D,
    SixFunctorClosedDomain (toSixFunctorOperationDatum.finiteTorDomain X)
      (sixFunctorFiniteHomPairs D C E n hn X) (sixFunctorFiniteHom D C E n hn X)

  integralClosed : ∀ X : SixFunctorSpace D,
    SixFunctorClosedDomain (toSixFunctorOperationDatum.integralFiniteTorDomain X)
      (constructibleIntegralHomPairs C.l E X.obj.left)
      (constructibleIntegralHom C.l E X.obj.left)
  rationalClosed : ∀ X : SixFunctorSpace D,
    SixFunctorClosedDomain (⊤ : ObjectProperty (sfRationalConstructibleCategory C.l E X.obj.left))
      (constructibleRationalHomPairs C.l E X.obj.left)
      (rationalDerivedInternalHom C.l E X.obj.left)
  commonClosed : ∀ X : SixFunctorSpace D,
    SixFunctorClosedDomain
      (⊤ : ObjectProperty (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left))
      (commonStageHomPairs C.l C.Qbar X.obj.left)
      (commonStageDerivedInternalHom C.l C.Qbar X.obj.left)
  finiteModel : ∀ X : SixFunctorSpace D,
    sixFunctorRingedModel.{u, u+1, u} (ProEt.topology X.obj.left)
      ((constantSheaf (ProEt.topology X.obj.left) CommRingCat.{u+1}).obj
        (.of (ULift.{u+1, u} (Padic.coefficientExtensionRing C.l E n))))
  finiteModelComparison : ∀ X : SixFunctorSpace D,
    SixFunctorAmbientClosedModel (finiteClosed X) (finiteModel X).closed
      (finiteModel X).symmetric (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
  integralModel : ∀ X : SixFunctorSpace D,
    sixFunctorRingedModel.{u, u+1, u} (ProEt.topology X.obj.left)
      (completedIntegralCommRingSheafUnrestricted C.l E X.obj.left)
  integralModelComparison : ∀ X : SixFunctorSpace D,
    SixFunctorAmbientClosedModel (integralClosed X) (integralModel X).closed
      (integralModel X).symmetric (sfIntegralConstructible C.l E X.obj.left).ι
  rationalClosedComparison : ∀ X : SixFunctorSpace D,
    SixFunctorClosedChange (integralClosed X) (rationalClosed X)
      (sfRationalConstructibleLocalization C.l E X.obj.left)
  reductionClosed : ∀ (m : ℕ) (X : SixFunctorSpace D),
    SixFunctorClosedDomain
      (fun K : sixFunctorFiniteCategory D C E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) X ↦
        finiteTorConstructible C.l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
          X.obj.left K.obj)
      (sixFunctorFiniteHomPairs D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) X)
      (sixFunctorFiniteHom D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) X)
  reductionClosedComparison : ∀ (m : ℕ) (X : SixFunctorSpace D),
    SixFunctorClosedChange (integralClosed X) (reductionClosed m X)
      (sixFunctorIntegralReduction D C E m X)
  reductionAtLevel : ∀ (m : ℕ) (_h : m + 1 = n) (X : SixFunctorSpace D),
    HEq (reductionClosed m X) (finiteClosed X)
  coefficientClosedModels : ∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X : SixFunctorSpace D),
    SixFunctorCoefficientClosedModels C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left
  coefficientClosedComparison : ∀ (E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar)
    (h : E₀ ≤ L) (X : SixFunctorSpace D),
    SixFunctorClosedChange (coefficientClosedModels E₀ X).rational
      (coefficientClosedModels L X).rational
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left).T h)
  commonClosedComparison : ∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X : SixFunctorSpace D),
    SixFunctorClosedChange (coefficientClosedModels E₀ X).rational (commonClosed X)
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀)
  [finiteTriangulation : ∀ X : SixFunctorSpace D,
    (toSixFunctorOperationDatum.finiteTorDomain X).IsTriangulated]
  [integralTriangulation : ∀ X : SixFunctorSpace D,
    (toSixFunctorOperationDatum.integralFiniteTorDomain X).IsTriangulated]
  [rationalTriangulation : ∀ X : SixFunctorSpace D,
    (⊤ : ObjectProperty (sfRationalConstructibleCategory C.l E X.obj.left)).IsTriangulated]
  [commonTriangulation : ∀ X : SixFunctorSpace D,
    (⊤ : ObjectProperty
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).IsTriangulated]
  finiteVerdier : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    SixFunctorVerdierAxioms (toSixFunctorOperationDatum.finiteTorDomain X) (finiteClosed X)
      (finiteDuality.dualizing X c)
  integralVerdier : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    SixFunctorVerdierAxioms (toSixFunctorOperationDatum.integralFiniteTorDomain X)
      (integralClosed X) (higher.integralDuality.dualizing X c)
  rationalVerdier : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    SixFunctorVerdierAxioms ⊤ (rationalClosed X) (higher.rationalDuality.dualizing X c)
  commonVerdier : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    SixFunctorVerdierAxioms ⊤ (commonClosed X) (closure.commonStageDuality.dualizing X c)

end WeilConjectures
