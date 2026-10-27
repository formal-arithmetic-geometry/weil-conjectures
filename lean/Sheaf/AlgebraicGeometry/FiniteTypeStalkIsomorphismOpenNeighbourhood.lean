module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Irreducible
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Localization.Away.Basic

/-! # A stalk isomorphism for a finite-type morphism spreads to an open immersion

Source: Stacks Project, Varieties, Tag 09NH, Lemma `lemma-local-isomorphism`
(blueprint: lem-trf-finite-type-stalk-isomorphism-open-neighbourhood).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite-type morphism to a reduced scheme with finitely many irreducible components
that induces an isomorphism on local rings at a point restricts to an open immersion on
some open neighbourhood of that point.

Source: Stacks Project, Varieties, Tag 09NH, Lemma `lemma-local-isomorphism`
(blueprint: lem-trf-finite-type-stalk-isomorphism-open-neighbourhood).

Proof plan, following the seven steps of the node and Tag 09NH:

1. Remove the finitely many target components not containing `x = g y`. Choose an affine
   open `Spec A` containing `x`, and a finite-type affine chart `Spec B` above it containing
   `y`. The ring `A` is reduced. Every component of `Spec A` comes from a target component
   meeting this open, hence contains `x`. Thus every minimal prime of `A` lies in the prime
   `p` of `x`. Use def-weil-irreducible-components, lem-sc-irreducible-components-cover,
   lem-sc-components-open-injection, lem-weil-pbc-affine-opens-basis,
   def-weil-finite-type-morphism, def-pc-reduced-scheme, and
   lem-weil-pbc-spec-irreducible-components-minimal-primes.

2. Write `q` for the prime of `y`, and `φ : A → B` for the chart map. Identify the given
   stalk map with the induced isomorphism `α : A_p → B_q`, using def-weil-affine-spectrum,
   lem-weil-pbc-affine-open-stalk-localization, and lem-weil-pbc-spec-map-stalk-localization.

3. The map `A → A_p` is injective: if `a/1 = 0`, some `s` outside `p` kills `a`. Every
   minimal prime lies in `p`, so primality puts `a` in every minimal prime. Every prime
   contains a minimal prime; the radical formula makes `a` nilpotent, hence zero. Use
   def-weil-pbc-localization-at-prime, lem-weil-pbc-prime-contains-minimal-prime,
   lem-weil-pbc-zero-locus-eq-iff-radical-eq, and def-pc-reduced-scheme.

4. Choose finitely many algebra generators `b_i` of `B`. Express their inverse images
   under `α` as fractions and take a common denominator `f` outside `p`. The zero-fraction
   criterion gives elements `g_i` outside `q` killing `φ(f)b_i - φ(a_i)`. Their product `h`
   kills every such difference and is outside `q`. Empty products are `1`. Use
   def-weil-pbc-localization-at-prime.

5. Put `C = B[1/(φ(f)h)]`. The universal-property map `β : A[1/f] → C` contains every `b_i`
   and therefore `h` in its image. Write `h = β(f'/f^N)`. Its image in `B_q` shows that
   `f'/1` is a unit in `A_p`, so `f'` is outside `p`. Use def-weil-ring-localization-away,
   lem-weil-pbc-localization-away-universal-property, and def-weil-pbc-localization-at-prime.

6. Extend to `γ : A[1/(ff')] → C`. It is surjective because its image contains `B`, the
   inverse of `φ(f)`, and `h⁻¹ = f^N/f'`. It is injective because its composite into `B_q`
   factors through the injection into `A_p` and then `α`; step 3 detects zero numerators.
   Use def-weil-ring-localization-away and lem-weil-pbc-localization-away-universal-property.

7. The principal open `D_B(φ(f)h)` contains `y`. Spectrum carries `γ` to an isomorphism of
   this open with `D_A(ff')`. Its composite into `X` is the original restriction of `g`,
   hence an open immersion. Use lem-weil-pbc-principal-localization-open-immersion,
   def-weil-affine-spectrum, and def-weil-open-immersion.
-/
theorem exists_isOpenImmersion_of_stalkMap_isIso_of_finiteType
    {Y X : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] [QuasiCompact g]
    [IsReduced X] (hcomponents : (irreducibleComponents X).Finite)
    (y : Y) (hstalk : IsIso (g.stalkMap y)) :
    ∃ V : Y.Opens, y ∈ V ∧ IsOpenImmersion (V.ι ≫ g) := by
  sorry

end AlgebraicGeometry
