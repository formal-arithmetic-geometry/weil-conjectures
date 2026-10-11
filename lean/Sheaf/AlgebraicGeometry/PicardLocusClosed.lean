/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Closedness of the invertible-module pullback locus

Source: Stacks Project, More on Morphisms, Lemma 37.33.4 (Tag 0BF0)
(blueprint: lem-sc-picard-locus-closed).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-sc-picard-locus-closed) Let `f : X ⟶ S` be flat, proper and locally of
finite presentation, with universally trivial structure-sheaf pushforward. For a finite
locally free invertible module `E`, let `j : Z ⟶ S` be the immersion of finite presentation
characterized by `picard_diagonal_locally_closed`. If the geometric fibres of `f` are integral,
then `j` is a closed immersion. This is the closedness assertion of Stacks Tag 0BF0; its proof
uses the valuative criterion and the valuation-ring triviality lemma
`lem-sc-picard-locus-closed-valuation-triviality`.

The proof follows Tag 0BF0. First, the characterization from
`lem-sc-picard-diagonal-locally-closed` makes `j` an immersion locally of finite presentation,
so it is quasi-compact. Apply the valuative closed-image criterion
`lem-sc-picard-locus-closed-valuation-criterion` to a valuation ring `A` with fraction field
`K` and a map `Spec A ⟶ S` whose generic point factors through `j`. Base change preserves the
flat, proper, finite-presentation, and integral-geometric-fibre hypotheses. The universal
pushforward condition gives `H⁰(X_K, O) = K`; the generic factorization and the universal
property make the pullback of `E` to `X_K` trivial. The valuation-ring triviality lemma
`lem-sc-picard-locus-closed-valuation-triviality` then makes its pullback to `X_A` trivial.
Taking the finite locally free module `O_A` in the universal property gives a factorization
`Spec A ⟶ Z`, so the image of `j` is closed by the criterion; an immersion with closed image
is a closed immersion. (blueprint: lem-sc-picard-locus-closed)
-/
theorem picard_locus_closed {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsInvertible]
    {Z : Scheme.{u}} (j : Z ⟶ S)
    (hj : IsImmersion j ∧ LocallyOfFinitePresentation j ∧ QuasiCompact j ∧
      QuasiSeparated j ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ (h : T ⟶ Z), h ≫ j = g) ↔
          ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
            Nonempty (((Scheme.Modules.tensorPullback (pullback.fst f g)).obj E) ≅
              ((Scheme.Modules.tensorPullback (pullback.snd f g)).obj N)))
    [GeometricallyIntegral f] : IsClosedImmersion j := by
  sorry

end AlgebraicGeometry.Scheme
