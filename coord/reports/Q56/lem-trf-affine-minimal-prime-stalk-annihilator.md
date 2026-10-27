## Worker report

The module `Sheaf.AlgebraicGeometry.AffineMinimalPrimeStalkAnnihilator` states
`AlgebraicGeometry.exists_stalk_annihilator_of_minimal_prime`; its only proof is `sorry`.
No definitions, helper nodes, dependency repairs, or statement corrections are needed.
Only the item's `lean` field changes.

Hypothesis and conclusion correspondence:

- The arbitrary scheme is `{T : Scheme.{u}}`, with explicitly declared universe `u`.
- The open subset is `{U : T.Opens}`, with affine hypothesis `(hU : IsAffineOpen U)`.
- The point lying in this open is `(y : U)`; its underlying point in the scheme is `(y : T)`.
- The ring A = O_T(U) is `T.presheaf.obj (Opposite.op U)`.
- The canonical affine identification is Mathlib's `hU.isoSpec`, and the corresponding
  prime is `(hU.primeIdealOf y).asIdeal`. The latter definition is the image of `y` under
  `hU.isoSpec.hom`, not a separately chosen prime or isomorphism.
- Noetherianity of A alone is `[IsNoetherianRing (T.presheaf.obj (Opposite.op U))]`.
  There is no Noetherian hypothesis on all of T.
- Minimality is `hy : (hU.primeIdealOf y).asIdeal ∈ minimalPrimes
  (T.presheaf.obj (Opposite.op U))`. Mathlib defines this as minimality among prime
  ideals over the zero ideal, equivalently no strictly smaller prime ideal.
- The first conjunct is the existential `∃ w : T.presheaf.stalk (y : T), ...`.
  Its equality `(⊥ : Ideal (T.presheaf.stalk (y : T))).colon {w} =
  IsLocalRing.maximalIdeal (T.presheaf.stalk (y : T))` is exactly the asserted
  annihilator equality. `Submodule.mem_colon_singleton` identifies membership with
  `r • w ∈ ⊥`, i.e. `r * w = 0` for the ring acting on itself.
- The second conjunct `(y : T) ∈ associatedPoints T` records the final associated-point
  clause using exactly `def-sc-associated-points`' recorded declaration.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map` (scheme and affine-spectrum nodes). These are
  publicly imported through `Mathlib.AlgebraicGeometry.AffineScheme`, which also supplies
  `IsAffineOpen`, `IsAffineOpen.isoSpec`, and `IsAffineOpen.primeIdealOf`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, `isNoetherianRing_iff`.
- `Sheaf.AlgebraicGeometry.AssociatedPoints`: `AlgebraicGeometry.associatedPoints`,
  defined by `IsAssociatedPrime` of the stalk maximal ideal on the stalk itself.
- Proof import `Mathlib.RingTheory.Ideal.AssociatedPrime.Localization`:
  `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`, the
  recorded match of `lem-weil-pbc-noetherian-minimal-prime-associated`. Its specialization
  to the finite module A over itself is the node's algebraic annihilator witness.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen.fromSpec_app_self`,
  `IsAffineOpen.isOpenImmersion_fromSpec`, `IsAffineOpen.fromSpec_primeIdealOf`,
  `IsAffineOpen.isLocalization_stalk`; `Mathlib.AlgebraicGeometry.OpenImmersion`:
  the instance making an open immersion's stalk map an isomorphism; and
  `Mathlib.AlgebraicGeometry.Scheme`: `Scheme.Hom.germ_stalkMap`. These are the recorded
  matches of `lem-weil-pbc-affine-open-stalk-localization`; the proof uses its clause (c).
- Proof import `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  and `IsLocalization.AtPrime`, from `def-weil-pbc-localization-at-prime`.

Source verification: read `literature/stacks-project/divisors.tex`,
`definition-associated` (Tag 02OJ), `lemma-associated-affine-open` (Tag 02OK), especially
its forward implication; and `literature/stacks-project/algebra.tex`,
`lemma-ass-minimal-prime-support` (Tag 05BV), `lemma-associated-primes-localize`
(Tag 0310). The four proof steps are reproduced in the theorem docstring. The associated
points dependency's docstring cites 02OZ instead of 02OJ; its actual definition is usable
and has not been changed.

Edge cases checked mathematically before writing:

- Empty T or U: there is no `y : U`; the theorem is vacuous, without a nonempty assumption.
- A field: its unique prime is zero; the stalk is that field, and w = 1 has annihilator
  zero, its maximal ideal.
- Nonreduced A = k[e]/(e^2): the unique minimal prime is (e); w = e in its stalk
  has annihilator (e). No reducedness or domain hypothesis has been added.
- Reducible A = k[x,y]/(xy), at the minimal prime (x): y is inverted, x becomes zero,
  and the stalk is a field; w = 1 works. Multiple minimal primes are allowed.
- The zero section ring has empty spectrum, hence no point in an affine chart.
- The rest of T may be non-Noetherian: only the single section ring A is constrained.

Searches for an existing full statement (all via the prescribed wrapper except the
explicit project ripgrep searches):

- `leanfinder`: "A minimal prime of a Noetherian affine chart of a scheme gives a stalk
  element whose annihilator is the maximal ideal". Eight hits, including
  `IsAffineOpen.isLocalization_stalk`, `primeIdealOf_eq_map_closedPoint`,
  `primeIdealOf_genericPoint`, and Noetherian stalk instances; no full conclusion.
- `loogle`: `"associatedPoints"`. Zero hits.
- `grep`: `associatedPoints|associatedPoint|stalk.*annihilator|minimal.*stalk`, in
  `Mathlib/AlgebraicGeometry`. Zero hits.
- `leansearch`: "A minimal prime in a Noetherian affine chart gives a stalk element
  whose annihilator is the maximal ideal". Eight hits, including the algebraic
  minimal-prime associated-prime theorem and structure-sheaf stalk localization, but
  no full scheme statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `associatedPoints|stalk.*annihilator|minimal.*stalk|stalk.*minimal`: the recorded
  associated-point definition and results with different hypotheses or conclusions,
  including affine associated points of module sheaves, were found; no exact statement.
- `rg` for the item's blueprint id in `lean/WeilConjectures`: no hit.
- `rg` for `affine_minimal_prime_stalk_annihilator|exists_stalk_annihilator_of_minimal_prime`
  in both project source roots and `dag/lean_names_upstream.json`: no hit.

No statement dispute. All data and predicates are existing declarations.

## Second reading by Q56

The dispatcher brief requires this worker to deliver directly, prohibits starting other
agents, and assigns the independent reading to the maintainer. This section records my
own second pass, not a claim of an independent worker review.

Reread the node and the completed module together. The scheme/open/affine/point binders
render precisely T, U, and y in U. The sole Noetherian binder concerns the section ring,
and minimal-prime membership concerns the prime defined by the canonical chart.
The colon ideal is the full annihilator, with equality to the actual stalk maximal ideal,
not merely containment or equality of radicals. The concluding conjunct uses the recorded
associated-point definition on T. Universes and variables are explicitly bound; no extra
finiteness, reducedness, global Noetherianity, or nonemptiness occurs. All four proof steps
have sources and are in the docstring. No mismatch or correction was found.
