module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality

/-! The valuative factorization step in the proof of Tag 0BF0. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/--
(blueprint: lem-sc-picard-locus-closed-valuative-factorization)

For a valuative commutative square for the Picard pullback locus, the generic
factorization forces a factorization over the valuation ring.  This is the
valuative argument of Stacks, More on Morphisms, Tag 0BF0, using the generic
fibre triviality result (Tag 0EX8) and the universal property of the locus.
No immersion or finiteness hypothesis on `j` is needed for this local step.

Proof: put `A = sq.R`, `K = sq.K`, and base change `f` along `sq.i₂`, obtaining
`p : X_A ⟶ Spec A` and the invertible pullback `L` of `E`. The hypotheses on
`p` persist under base change; properness also gives quasi-compactness and
quasi-separatedness, hence finite presentation. Geometric integrality gives
an integral, nonempty closed fibre and a nonempty generic fibre. The adjunction
unit hypothesis, applied to the generic map to `S`, identifies the canonical
structure-sheaf map on the generic fibre with an isomorphism. Its global
sections therefore identify `H⁰(X_K, O)` with `K`. Pullback composition and
the associativity isomorphism of fibre products identify these with the
corresponding objects for `p`.

The commutativity of `sq` gives the generic factorization `sq.i₁`. Apply `hj`
to that map to obtain a finite locally free module `N` over `Spec K` whose
pullback is `L_K`. Such an `N` corresponds to a finite-dimensional vector
space. Its dimension is one: the generic fibre is nonempty, and at any of
its points its pullback has rank one because `L_K` is invertible. Thus `N`
is isomorphic to `O_K`, and `L_K` is trivial. Apply
`generic_fibre_triviality_over_valuation_ring` (Tag 0EX8) to `p` and `L` to
make `L` trivial. The unit module `O_A` is finite locally free, and its
pullback is the unit module on `X_A`. Use this trivialization with `N = O_A`
in the reverse direction of `hj` at `sq.i₂` to obtain the desired `l`.
-/
theorem picard_valuative_factorization {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsInvertible]
    {Z : Scheme.{u}} (j : Z ⟶ S)
    (hj : ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ (h : T ⟶ Z), h ≫ j = g) ↔
          ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
            Nonempty (((Scheme.Modules.tensorPullback (pullback.fst f g)).obj E) ≅
              ((Scheme.Modules.tensorPullback (pullback.snd f g)).obj N)))
    [GeometricallyIntegral f] (sq : ValuativeCommSq j) :
    ∃ l : Spec (CommRingCat.of sq.R) ⟶ Z, l ≫ j = sq.i₂ := by
  sorry

end AlgebraicGeometry.Scheme
