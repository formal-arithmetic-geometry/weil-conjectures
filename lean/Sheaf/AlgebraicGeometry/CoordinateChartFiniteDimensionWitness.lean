/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.KrullDimension.Zero
import WeilConjectures.RingTheory.PolynomialOriginRegularLocal
import WeilConjectures.RingTheory.Etale.LocalDimension
import Sheaf.AlgebraicGeometry.FibreStalkQuotient

/-!
# A finite local-dimension witness in an etale coordinate chart

Source: the nine-step coordinate-chart witness argument in the DAG; Stacks Project,
Tags 056G, 02GO, 03WT, 00E0, 00EU, 00OP, 07QP, 01HV and 0HA1
(blueprint: lem-pur-coordinate-chart-finite-dimension-witness).

The base is arbitrary. The structures over the base on `Y`, `T` and `Y ×[X] T`
are the ones induced by `i`, `e` and the pullback projections, respectively.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonempty simultaneous-coordinate chart has a point over a minimal base prime
where the support local rings have dimension zero and the ambient local rings have
dimension `b`. The affine open is `U = Spec Γ(S,U)`. Its prime `s` has residue field
`κ(s)`, canonically the fraction field of `Γ(S,U)/s`. `asFiber` denotes the unique
point above the displayed point. Thus genericity is asserted in the actual
scheme-theoretic affine-space fibre, and the last ring equivalence gives its ambient
local ring as `κ(s)(u₁,…,uₐ)[v₁,…,v_b]_(v₁,…,v_b)`.
Source: Stacks 056G and the extracted coordinate-model argument, steps 1--9
(blueprint: lem-pur-coordinate-chart-finite-dimension-witness).

Proof:
1. The cartesian square makes `g` etale by etale base change
   [lem-weil-pbc-etale-scheme-base-change], as is `Z → Y`. Choose an affine base open
   meeting `Z`. The image of `g` there is a nonempty open in affine space
   [lem-weil-pbc-etale-morphism-open-map].
2. For a prime `P` in this image choose a minimal base prime `s ⊆ P ∩ R`
   [lem-weil-pbc-prime-contains-minimal-prime]. The polynomial prime `s R[u] ⊆ P`
   lies in this open, since opens contain generizations. Lift it through `g` to `t`.
3. Reducing and localizing sends `s R[u]` to the zero prime of `κ(s)[u]`.
   This is the generic point, whose local ring is `K = Frac(κ(s)[u])`
   [def-weil-pbc-localization-at-prime, lem-weil-pbc-affine-open-stalk-localization].
4. The ambient image prime is `(v)` in `κ(s)[u,v]`. Its localization is `K[v]_(v)`:
   nonzero polynomials in `u` are inverted already; clearing the finitely many
   `u`-denominators constructs the inverse localization homomorphism.
5. The tangential field has dimension zero. The polynomial-origin lemma gives
   dimension `b` for the ambient local ring
   [lem-weil-pbc-polynomial-ring-origin-regular-local], including `b = 0`.
6. Base change makes both fibre chart maps etale. Affine stalk localization and
   [lem-sc-etale-local-dimension] give dimensions zero and `b` on the source fibres.
7. At a minimal base prime the maximal ideal of `R_s` consists of nilpotents
   [lem-weil-pbc-minimal-prime-reduced-localization-field]. Its extension to each
   of the four local rings is nil: a finite sum of nilpotent multiples is nilpotent
   by the multinomial expansion. No uniform nilpotence exponent is needed.
8. [lem-sbc-scheme-fibre-stalk-quotient] identifies each fibre stalk with the quotient
   by this nil ideal. Every prime contains it, so quotient and contraction identify
   all strict prime chains and preserve their dimension suprema.
9. Apply [lem-sc-etale-local-dimension] to `Z → Y` and `T → X`, using affine stalk
   localization, to get the two remaining local dimensions. The pullback equation
   identifies the two images in `X`. These are all the required witnesses. -/
theorem Scheme.Hom.exists_coordinate_chart_finite_dimension_witness
    {S X Y T : Scheme.{u}} (p : X ⟶ S) (i : Y ⟶ X) (e : T ⟶ X)
    [IsClosedImmersion i] [Etale e] (a b : ℕ)
    (h : T ⟶ AffineSpace (ULift.{u} (Fin (a + b))) S) [Etale h]
    (coordinatesOver :
      h ≫ (AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) = e ≫ p)
    (g : pullback i e ⟶ AffineSpace (ULift.{u} (Fin a)) S)
    (cartesian : IsPullback g (pullback.snd i e)
      (AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
        (fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k))
          (fun _ ↦ 0) j.down)) h)
    (nonemptySupport : Nonempty (pullback i e : Scheme.{u})) :
    ∃ (U : S.Opens) (hU : IsAffineOpen U) (s : PrimeSpectrum Γ(S, U))
        (t : (pullback i e : Scheme.{u})),
      s.asIdeal ∈ minimalPrimes Γ(S, U) ∧
      (pullback.fst i e ≫ i ≫ p) t = hU.fromSpec s ∧
      Nonempty (s.asIdeal.ResidueField ≃+* FractionRing (Γ(S, U) ⧸ s.asIdeal)) ∧
      IsGenericPoint
        ((AffineSpace (ULift.{u} (Fin a)) S ↘ S).asFiber (g t)) Set.univ ∧
      ringKrullDim ((pullback i e).presheaf.stalk t) = 0 ∧
      ringKrullDim (Y.presheaf.stalk ((pullback.fst i e) t)) = 0 ∧
      ringKrullDim (T.presheaf.stalk ((pullback.snd i e) t)) = (b : WithBot ℕ∞) ∧
      ringKrullDim (X.presheaf.stalk (i ((pullback.fst i e) t))) = (b : WithBot ℕ∞) ∧
      ringKrullDim ((pullback i e).presheaf.stalk t) =
        ringKrullDim (((pullback.fst i e ≫ i ≫ p).fiber
          ((pullback.fst i e ≫ i ≫ p) t)).presheaf.stalk
            ((pullback.fst i e ≫ i ≫ p).asFiber t)) ∧
      ringKrullDim (Y.presheaf.stalk ((pullback.fst i e) t)) =
        ringKrullDim (((i ≫ p).fiber ((i ≫ p) ((pullback.fst i e) t))).presheaf.stalk
          ((i ≫ p).asFiber ((pullback.fst i e) t))) ∧
      ringKrullDim (T.presheaf.stalk ((pullback.snd i e) t)) =
        ringKrullDim (((e ≫ p).fiber ((e ≫ p) ((pullback.snd i e) t))).presheaf.stalk
          ((e ≫ p).asFiber ((pullback.snd i e) t))) ∧
      ringKrullDim (X.presheaf.stalk (i ((pullback.fst i e) t))) =
        ringKrullDim ((p.fiber (p (i ((pullback.fst i e) t)))).presheaf.stalk
          (p.asFiber (i ((pullback.fst i e) t)))) ∧
      ∃ q : PrimeSpectrum
          (MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField))),
        q.asIdeal = Ideal.span (Set.range (MvPolynomial.X : Fin b →
          MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField)))) ∧
        Nonempty
          ((((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).fiber
              ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S)
                (h ((pullback.snd i e) t)))).presheaf.stalk
            ((AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S).asFiber
              (h ((pullback.snd i e) t)))) ≃+* Localization.AtPrime q.asIdeal) := by
  sorry

end AlgebraicGeometry
