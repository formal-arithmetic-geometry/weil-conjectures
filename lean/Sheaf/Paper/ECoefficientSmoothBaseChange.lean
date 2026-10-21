/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Paper.AdicSmoothBaseChange
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.PbcRationalCategory

/-! # Smooth base change with finite-extension rational coefficients
Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change).
The exchange lives in the raw rationalization of the ambient complete category.
Constructible landing is represented through the fully faithful integral inclusion
and the specified lattice presentation. It makes no integral constructibility claim
about an arbitrary representative merely rationally isomorphic to a constructible one.

## Main statements

- `sbcRationalExchange`: the localized canonical integral mate.
- `sbcTransportedExchange`: transport along a specified presentation.
- `eCoefficientSmoothBaseChange`: invertibility, independence and constructible landing.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)

/-- The scalar localization of the left integral composite, on all complete complexes.
Equivalently this is successive rational direct image and rational completed pullback:
both send a tensor r tensor a to r tensor P_f(D_g(a)).
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalLeft : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPush l E g ⋙ sbcPull l E f)

/-- The scalar localization of the right integral composite, without constructibility
assumptions on its outputs. Source: blueprint order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalRight : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPull l E e ⋙ sbcPush l E h)

/-- Rational exchange is exactly scalar localization of the specified integral mate.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalExchange : sbcRationalLeft l E (f := f) (g := g) ⟶
    sbcRationalRight l E (e := e) (h := h) :=
  ScalarLocalization.betweenNat (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcExchange l E sq)

/-- Localize an ambient integral complete complex by the same raw construction.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
abbrev sbcCompleteRationalize (W : Scheme.{u}) :=
  ScalarLocalization.localization (PbcIntegralRing l E)
    (PbcComplete l E W) (pbcUniformizer l E)

/-- Transport of the lattice exchange along the specified rational presentation.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcTransportedExchange [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) :
    (sbcRationalLeft l E (f := f) (g := g)).obj ((pbcRationalInclusion l E T).obj K) ⟶
      (sbcRationalRight l E (e := e) (h := h)).obj ((pbcRationalInclusion l E T).obj K) :=
  (sbcRationalLeft l E (f := f) (g := g)).map
      ((pbcRationalInclusion l E T).map L.rationalization.inv) ≫
    (sbcRationalExchange l E sq).app
      ((sbcCompleteRationalize l E T).obj ((pbcConstructibleInclusion l E T).obj L.integral)) ≫
    (sbcRationalRight l E (e := e) (h := h)).map
      ((pbcRationalInclusion l E T).map L.rationalization.hom)

/-- Constructible landing means a constructible rational isomorphism representing the
ambient exchange, with the endpoints identified using this lattice presentation.
The integral endpoint identifications precede rationalization, so an arbitrary rational
representative is never inferred to have a constructible integral model.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def SbcConstructibleExchangeRepresentation [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) : Prop :=
  ∃ (J J' : PbcIntegralConstructible l E X)
    (a : (pbcConstructibleInclusion l E X).obj J ≅
      (sbcPull l E f).obj ((sbcPush l E g).obj
        ((pbcConstructibleInclusion l E T).obj L.integral)))
    (b : (pbcConstructibleInclusion l E X).obj J' ≅
      (sbcPush l E h).obj ((sbcPull l E e).obj
        ((pbcConstructibleInclusion l E T).obj L.integral)))
    (β : (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj J ≅
      (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj J'),
    (pbcRationalInclusion l E X).map β.hom ≫
        ((sbcCompleteRationalize l E X).mapIso b ≪≫
          (sbcRationalRight l E (e := e) (h := h)).mapIso
            ((pbcRationalInclusion l E T).mapIso L.rationalization)).hom =
      ((sbcCompleteRationalize l E X).mapIso a ≪≫
        (sbcRationalLeft l E (f := f) (g := g)).mapIso
          ((pbcRationalInclusion l E T).mapIso L.rationalization)).hom ≫
        (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)

/-- Pulling an invertible global integer back to every stalk preserves invertibility.
Source: blueprint order 1445, invertibility on every corner in proof step 1
(blueprint: sbc-thm-e-coefficient-smooth-base-change).
Proof: map the global section through q.appTop and the global-to-stalk germ. Ring maps
preserve units and natural-number casts. This also handles an empty source scheme. -/
theorem sbcPrimeUnitOnSource {U V : Scheme.{u}} (q : U ⟶ V)
    (_hl : IsUnit (l : Γ(V, ⊤))) : ∀ t : U, IsUnit (l : U.presheaf.stalk t) := by
  sorry

/-- Smooth base change for E coefficients, including lattice independence and
constructible landing with the specified endpoint identifications.
The integral and rational constructible categories and both lattice predicates are
the landed Q06 declarations. Their full inclusion into the complete category uses the
same completed coefficient ring and published intrinsic predicate. Completed pullback
is the strict tower construction with its maps. No additional universe equality is required.
Source: blueprint order 1445, sec-smooth-base-change/sk-rem-rest
(blueprint: sbc-thm-e-coefficient-smooth-base-change).

Proof: the ring of integers is a Noetherian DVR with finite residue field; its positive
quotients are finite and have two-term finite-free resolutions. Multiplication by a
positive uniformizer power is injective because the valuation ring is a domain, so
these resolutions give perfect quotients. The residue field has characteristic l:
l has absolute value less than one and lies in the maximal ideal. If its cardinality
is l^d, cancellation identifies each successive uniformizer-ideal quotient with that
residue field, giving cardinality l^(d(n+1)) at level n. Its order is invertible on S
by the hypothesis on l, and hence on every corner. This verifies the coefficient
hypotheses of sbc-thm-adic-smooth-base-change, using
lem-weil-l-adic-extension-integers-dvr and lem-weil-valued-dvr-finite-quotients.
The lattice's complete-category membership supplies the compatible etale origins,
and its finite-level admissibility supplies bounded constructible origins. Apply the
adic theorem to this lattice. Its finite-level smooth base change applies
to every bounded constructible étale origin of the lattice reduction. The completed
pullback-reduction and direct-image/derived-limit comparisons identify the completed
integral mate with the derived inverse limit of these finite exchange maps, hence
make it invertible on the lattice. The operations are additive and A-linear, so raw
scalar localization gives the displayed natural transformation and preserves its
inverse. Naturality, followed by cancellation of the two inverse presentation maps,
gives transported exchange = exchange at K; applying the same equality to every
other admissible presentation proves independence.

For square-constructible admissibility, the four finite systems share one window.
Their canonical quotient-linear comparisons are the actual reductions of the four
completed integral outputs. Normalized constructible local effectivity supplies the
uniform stratified local models and bounded étale origins for the two X endpoints.
Lift each quotient normalization to its étale origin using full faithfulness on D+;
the normalization cocycle and faithfulness give the witness cocycle. Thus both integral
endpoints are in the published bounded constructible complete subcategory. Its full
inclusion remains fully faithful after tensoring Hom groups. The localized exchange
and its inverse are consequently an isomorphism of the rational constructible
endpoints. Composing their endpoint identifications with the given presentation gives
the equality required by SbcConstructibleExchangeRepresentation. -/
theorem eCoefficientSmoothBaseChange
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (_hX : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_hl : IsUnit (l : Γ(S, ⊤)))
    (K : PbcRationalConstructible l E T)
    (L : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K)
    (_hL : L.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl)) :
    IsIso ((sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L =
      (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (∀ L' : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K,
      L'.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) →
      sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L' =
        sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) ∧
    (L.IsSquareConstructiblyAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) sq →
      SbcConstructibleExchangeRepresentation l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) := by
  sorry

end WeilConjectures
