/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.AmbientCompleteCoefficientCategories
public import Sheaf.Paper.ECoefficientSmoothBaseChange
public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Sheaf.Paper.PbcScalarExtension
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.StageSystem.Functor
import Sheaf.Paper.IntrinsicQbarCategory

/-! # Smooth base change with algebraically closed ℓ-adic coefficients

Source: blueprint master, sec-smooth-base-change/sk-rem-rest, order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch).

The presentation specifies the finite-stage exchange and tensor comparisons.
Its descent through both ambient Karoubi layers retains the canonical arrow
and independence of the finite stage and admissible lattice.
No constructible landing of the ambient direct images is included.

## Main definitions

* `IntegralComparisons`: scalar comparisons fixed by the published tensor maps.
* `Presentation`: the completed composites and canonical compatible exchange.
* `Presentation.exchange`: descent through the ambient pair and Karoubi categories.

## Main statements

* `qbarCoefficientSmoothBaseChange`: invertibility and stage/lattice independence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

namespace QbarCoefficientSmoothBaseChange

/-- The finite-stage completed pullback/direct-image composite for the square.
Source: blueprint master, sec-smooth-base-change/sk-rem-rest, order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
abbrev smoothLeftStage (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (_sq : ChosenCartesianSquare h e f g) :
    pbcAmbientCompleteKaroubiStage l Ω T E ⥤
      pbcAmbientCompleteKaroubiStage l Ω X E :=
  (Idempotents.functorExtension₂ _ _).obj
    (WeilConjectures.sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g))

/-- The finite-stage direct-image/pullback composite for the square.
Source: blueprint master, sec-smooth-base-change/sk-rem-rest, order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
abbrev smoothRightStage (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (_sq : ChosenCartesianSquare h e f g) :
    pbcAmbientCompleteKaroubiStage l Ω T E ⥤
      pbcAmbientCompleteKaroubiStage l Ω X E :=
  (Idempotents.functorExtension₂ _ _).obj
    (WeilConjectures.sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h))

/-- The canonical finite-stage smooth exchange transformation.
Source: blueprint master, sec-smooth-base-change/sk-rem-rest, order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
abbrev smoothExchangeStage (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g) :
  smoothLeftStage l Ω E sq ⟶ smoothRightStage l Ω E sq :=
  (Idempotents.functorExtension₂ _ _).map
    (WeilConjectures.sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq)

end QbarCoefficientSmoothBaseChange

open WeilConjectures

namespace QbarCoefficientSmoothBaseChange

section Models
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U V : Scheme.{u}} (q : U ⟶ V)

/-- The right-adjoint comparison is the mate of the normalized ordinary tensor comparison.
Source: sketch32, lines 1191--1228 and 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def pushModel :
    sbcAmbientPush l E q ≅ pbcActualDerivedPush q (pbcIntegralDatum l E) :=
  conjugateIsoEquiv
    (proEtaleRingDerivedAdjunction q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q))
    (pbcActualDerivedAdjunction q (pbcIntegralDatum l E)) (sbcOrdinaryDerivedIso l E q)

/-- Transport the existing strict-tower/reflector comparison through reassociation.
Its unit normalization is exactly pbcActualCompletedPullback_tower: the strict
quotient augmentation is preserved, rather than an arbitrary completion isomorphism.
Source: sketch32, lines 1191--1228 and 1291--1321; Stacks 099N
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def pullModel :
    sbcPull l E q ⋙ ObjectProperty.ι (IsPbcComplete l E U) ≅
      ObjectProperty.ι (IsPbcComplete l E V) ⋙
        pbcActualCompletedPull q (pbcIntegralDatum l E) :=
  Functor.isoWhiskerLeft (ObjectProperty.ι (IsPbcComplete l E V))
      (Functor.associator (completedReductionTower V (pbcIntegralDatum l E))
        (completedTowerPullback q (pbcIntegralDatum l E))
        (completedTowerRlim (pbcIntegralDatum l E) U)).symm ≪≫
    (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) q).exists.choose
end Models

section Scalar
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
  [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [dV : Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [iU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [iV : Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
  (q : U ⟶ V)
  {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)

/-- The two recorded coefficient maps have the same finite projections, hence agree.
Source: sketch32, lines 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch).
Proof: both coefficient maps send a continuous quotient section to its image under
pbcFiniteFieldInclusion. The finite projections agree by quotient induction.
Uniqueness of the completed coefficient limit map gives equality; applying the
fixed derived extension construction gives this equality of tensor functors. -/
theorem tensorModel_eq (W : Scheme.{u}) :
    pbcAmbientScalarExtension l Ω W a =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) W := by
  sorry

/-- Transport between the two identical finite-projection-normalized tensors.
Source: sketch32, lines 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def tensorModel (W : Scheme.{u}) := eqToIso (tensorModel_eq l Ω a W)

/-- The canonical integral comparisons, specified by the published scalar mate and
unit-normalized completed tensor comparison. Their underlying equations determine
both isomorphisms uniquely. This packages the construction in proof step 1.
Source: sketch32, lines 1191--1228 and 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
structure IntegralComparisons where
  push : sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω V a ≅
    pbcAmbientCompleteIntegralTransition l Ω U a ⋙
      sbcPush l (pbcFiniteField.{u} l Ω M) q
  pull : sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω U a ≅
    pbcAmbientCompleteIntegralTransition l Ω V a ⋙
      sbcPull l (pbcFiniteField.{u} l Ω M) q
  push_eq : ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) U,
    HEq (push.hom.app K).hom
      (      (tensorModel l Ω a V).hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) V).map
          ((pushModel l (pbcFiniteField.{u} l Ω E) q).hom.app K.obj) ≫
        (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).hom.app K.obj ≫
        (pushModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).obj K.obj) ≫
        (sbcAmbientPush l (pbcFiniteField.{u} l Ω M) q).map
          ((tensorModel l Ω a U).inv.app K.obj))
  pull_eq : ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) V,
    HEq (pull.hom.app K).hom
      (      (tensorModel l Ω a U).hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).map
          ((pullModel l (pbcFiniteField.{u} l Ω E) q).hom.app K) ≫
        (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).inv.app K.obj ≫
        (pbcActualCompletedPull q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω M))).map
          ((tensorModel l Ω a V).inv.app K.obj) ≫
        (pullModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          (⟨(pbcAmbientScalarExtension l Ω V a).obj K.obj,
            pbcAmbientCompleteTensor_preserves l Ω V a K⟩))

end Scalar


section Descent
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iS : Fact (∀ x : S, IsUnit (l : S.presheaf.stalk x))]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
  [iY : Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))]
  (sq : ChosenCartesianSquare h e f g)

/-- A presentation of the specified ambient exchange and its scalar descent.
The integral comparisons are fixed by the actual scalar mate and completion units.
The raw comparison equations localize precisely their composites, also when E=M:
the published integral/raw comparisons retain the tensor unit in that case.
The stage operations and transformation are exactly their Karoubi extensions.
These are witnesses supplied by the theorem, not extra assumptions on K.
Source: sketch32, lines 1191--1228, 1291--1338 and 1439--1455
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
structure Presentation where
  cf : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω f a
  cg : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω g a
  ch : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω h a
  ce : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω e a
  leftBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)
  rightBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)
  leftBeta_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (leftBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) f).obj
            ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((cf a).pull.hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K) ≫
            (sbcPull l (pbcFiniteField.{u} l Ω M) f).map ((cg a).push.hom.app K))
  rightBeta_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (rightBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) h).obj
            ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((ch a).push.hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K) ≫
            (sbcPush l (pbcFiniteField.{u} l Ω M) h).map ((ce a).pull.hom.app K))
  F : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T) (pbcAmbientCompleteSystem l Ω X)
  G : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T) (pbcAmbientCompleteSystem l Ω X)
  F_eq : ∀ E, F.Φ E = smoothLeftStage l Ω E sq
  G_eq : ∀ E, G.Φ E = smoothRightStage l Ω E sq
  F_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (F.β a) ((Idempotents.functorExtension₂ _ _).mapIso (leftBeta a))
  G_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (G.β a) ((Idempotents.functorExtension₂ _ _).mapIso (rightBeta a))
  alpha : StageSystem.Morphism.Hom F G
  alpha_eq : ∀ E, HEq (alpha.τ E) (smoothExchangeStage l Ω E sq)

namespace Presentation
variable (P : Presentation l Ω sq)

/-- Extend the descended exchange to the ambient outer Karoubi envelope.
The Mathlib extension sandwiches components by both images of the outer projector.
Source: sketch32, lines 1412--1455
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
def ambientExchange :
    (Idempotents.functorExtension₂ _ _).obj P.F.functor ⟶
      (Idempotents.functorExtension₂ _ _).obj P.G.functor :=
  (Idempotents.functorExtension₂ _ _).map (StageSystem.Morphism.descNatTrans P.alpha)

/-- The exchange on the recorded raw Qbar category, using its published inclusion
through the finite-stage and outer identity projectors.
Source: sketch32, lines 1412--1455
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
def exchange :=
  Functor.whiskerLeft
    (pbcRawQbarToComplete l Ω T ⋙ pbcConstructibleCompleteQbarInclusion l Ω T)
    P.ambientExchange

/-- The representative at any finite overfield, with the canonical scalar conjugations.
This includes the identity extension and computes the component on every ambient pair.
Source: sketch32, lines 1291--1338 and 1439--1455
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
def atStage (Q : (pbcAmbientCompleteSystem l Ω T).PairCategory)
    (M : Padic.FiniteCoefficientFields l Ω) (a : Q.stage ≤ M) :
    P.F.functor.obj Q ⟶ P.G.functor.obj Q :=
  StageSystem.PairCategory.mkHom M a a
    ((P.F.β a).hom.app Q.obj ≫
      (P.alpha.τ M).app (((pbcAmbientCompleteSystem l Ω T).T a).obj Q.obj) ≫
      (P.G.β a).inv.app Q.obj)
end Presentation
end Descent

end QbarCoefficientSmoothBaseChange

open QbarCoefficientSmoothBaseChange

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  (sq : ChosenCartesianSquare h e f g)

/-- Algebraically closed-coefficient smooth base change on admissible finite-stage inputs.
All geometric hypotheses are explicit. Invertibility at other corners is obtained
from the single hypothesis on S, through the existing prime-unit pullback theorem.
The common-stage admissibility premise spells out the source's preservation condition.
No invertibility of exchange on arbitrary ambient complexes is asserted.

Source: sketch32, lines 1439--1455; blueprint order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch).
Proof:
1. The integral complete operations are additive and linear and their specified exchange
is natural (lem-sbc-completed-operations-linear-natural-exchange). Transport the canonical
scalar mate and unit-normalized pullback comparison of prop-weil-pbc-scalar-extension
through the normalized models. Localize and extend to the finite-stage Karoubi categories;
the tensor-Hom and projector formulas preserve the unit, tower and exchange equations.
2. Apply lem-sbc-coherent-pair-functor-descent to these families. On a representative u
at M its functors act by beta_source ; F_M(u) ; beta_target inverse, with the analogous
formula for G. These are exactly the specified completed composites on pair categories.
3. Scalar compatibility of the integral exchange, and then localization and Karoubi
extension, give alpha.comm. Its quotient descent is the exchange with representative
[E,alpha_E]. The outer Karoubi extension is the actual projector-sandwiched map.
4. For K at E, apply sbc-thm-e-coefficient-smooth-base-change to its admissible lattice.
Include its raw exchange and inverse by the identity finite-stage projector. Both inverse
equations remain true, without identifying the raw category with its Karoubi envelope.
5. The two classes of these arrows remain inverses in the ambient pair category, and
then under the outer identity-projector inclusion. Thus the specified component at K
is invertible in the ambient complete Qbar category. No constructible landing is used.
6. alpha.comm and the tensor tower equation identify atStage with the same component
for every overfield, including E itself. Two overfields have a finite compositum, so
the quotient equality criterion gives common-stage independence. Naturality identifies
the components on isomorphic presentations. The finite-E theorem's equality with the
canonical raw exchange makes the construction independent of each admissible lattice. -/
theorem qbarCoefficientSmoothBaseChange [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (hInvS : IsUnit (l : Γ(S, ⊤))) :
    ∃ P : Presentation
        (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
        (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
        (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
        (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) l Ω sq,
      (∀ (K : @pbcQbarCategory l _ Ω _ _ _ T _ dT
          ⟨sbcPrimeUnitOnSource l g hInvS⟩),
        (∃ (E : Padic.FiniteCoefficientFields l Ω)
          (J : pbcStageCategory l Ω T E)
          (L : IntegralLattice l (pbcFiniteField.{u} l Ω E) T dT.out
            (sbcPrimeUnitOnSource l g hInvS) J),
          L.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω E) T dT.out
            (sbcPrimeUnitOnSource l g hInvS) ∧
          Nonempty ((⟨E, J⟩ : @pbcQbarCategory l _ Ω _ _ _ T _ dT
            ⟨sbcPrimeUnitOnSource l g hInvS⟩) ≅ K) ∧
          (∀ (M : Padic.FiniteCoefficientFields l Ω) (a : E ≤ M),
            ∃ LM : IntegralLattice l (pbcFiniteField.{u} l Ω M) T dT.out
                (sbcPrimeUnitOnSource l g hInvS)
                (((pbcScalarSystem l Ω T dT.out (sbcPrimeUnitOnSource l g hInvS)).T a).obj
                  J),
              LM.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω M) T dT.out
                (sbcPrimeUnitOnSource l g hInvS))) →
        IsIso ((Presentation.exchange
          (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
          (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
          (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
          (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) l Ω sq P).app K)) ∧
      (∀ (Q : (pbcAmbientCompleteSystem l Ω T
          (hInv := ⟨sbcPrimeUnitOnSource l g hInvS⟩)).PairCategory)
        (M : Padic.FiniteCoefficientFields l Ω) (a : Q.stage ≤ M),
        (StageSystem.Morphism.descNatTrans (Presentation.alpha
          (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
          (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
          (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
          (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) P)).app Q =
          Presentation.atStage
            (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
            (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
            (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
            (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) l Ω sq P Q M a) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : PbcRationalConstructible l (pbcFiniteField.{u} l Ω E) T)
        (L L' : IntegralLattice l (pbcFiniteField.{u} l Ω E) T dT.out
          (sbcPrimeUnitOnSource l g hInvS) K),
        L.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω E) T dT.out
          (sbcPrimeUnitOnSource l g hInvS) →
        L'.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω E) T dT.out
          (sbcPrimeUnitOnSource l g hInvS) →
        sbcTransportedExchange l (pbcFiniteField.{u} l Ω E) sq dT.out
            (sbcPrimeUnitOnSource l g hInvS) L =
          sbcTransportedExchange l (pbcFiniteField.{u} l Ω E) sq dT.out
            (sbcPrimeUnitOnSource l g hInvS) L') := by
  sorry

end AlgebraicGeometry.Scheme
