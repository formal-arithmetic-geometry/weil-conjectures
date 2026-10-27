## Worker report

The module `Sheaf.RingTheory.FormalSingularIdealPatching` states
`FormalSingularPatching.formal_singular_ideal_patching`, with its only theorem proof
`sorry`. Five transparent helpers write out the node's constructions:
`completion`, `completedLocalization`, `beta`, `alpha`, and `patchedIdeal`.
They have actual data, and introduce no new independent mathematical notion.

Source read: Rotthaus, *Komplettierung semilokaler quasiausgezeichneter Ringe*,
Theorem 3, pp.176–178, the displayed comparison diagram, construction of D and
Claims 1–3. The Cambridge PDF was downloaded to the sandbox and read as text.
The node isolates Nagata reducedness and regularity of the comparison maps from
the larger theorem's hypotheses. Its accepted six-step proof supplies the finite
minimal-component argument needed for the intersection assertion. No correction
of the node's mathematical statement was needed.

Hypothesis and clause correspondence:

- A commutative integral domain B is `(B : Type u) [CommRing B] [IsDomain B]`.
- Noetherianity is `[IsNoetherianRing B]`, and semilocality is
  `[Finite (MaximalSpectrum B)]`, the Mathlib convention for finitely many maximal ideals.
- The Nagata condition is `hNagata : IsNagataRing B`, the recorded upstream predicate.
- The Jacobson radical r is `Ideal.jacobson (⊥ : Ideal B)`; its definition is the
  intersection of all maximal ideals containing zero. The ideal J and its inclusion
  are `(J : Ideal B)` and `hJ : J ≤ Ideal.jacobson (⊥ : Ideal B)`.
- C is `completion B`, definitionally `AdicCompletion r B`, Mathlib's inverse limit.
- An eligible Q is `q : PrimeSpectrum (completion B)` with
  `¬ q.asIdeal.IsMaximal` and `J.map (algebraMap B (completion B)) ≤ q.asIdeal`.
- The contracted prime p is `PrimeSpectrum.comap (algebraMap B (completion B)) q`.
  Its prime ideal instance comes from `PrimeSpectrum`.
- U_p is `completedLocalization B p`; T_Q is
  `completedLocalization (completion B) q`. Both are exactly maximal-ideal
  completions of `Localization.AtPrime`, with no auxiliary ring choice.
- `beta B q` is localization followed by completion. `alpha B q` constructs the
  completed map directly from `Localization.localRingHom p.asIdeal q.asIdeal
  (algebraMap B C) rfl`. Locality sends powers of the maximal ideal into powers
  of the target maximal ideal. Quotient maps composed with the source evaluations
  are compatible, and `AdicCompletion.liftRingHom` assembles the canonical map.
- `hRegular` asserts `(alpha B q).IsRegular` for exactly the eligible q.
- `AlgebraicGeometry.absoluteSingularIdeal R` is the existing vanishing ideal of
  `{p | ¬ IsRegularLocalRing (Localization.AtPrime p.asIdeal)}`. By
  `PrimeSpectrum.vanishingIdeal`, this is precisely the intersection of singular
  prime ideals, with empty intersection top. The relative nonsmoothness ideal
  `Algebra.singularIdeal` is deliberately not used.
- `patchedIdeal B J` is the actual indexed infimum, over eligible q, of
  `Ideal.comap (beta B q) ((absoluteSingularIdeal U_p).map (alpha B q))`.
- The first conjunct is `patchedIdeal B J ≠ ⊥`; the second is its `IsRadical`.
  There is no properness requirement: the unit ideal is allowed.
- The third conjunct says `(patchedIdeal B J).map (beta B q) =
  (absoluteSingularIdeal U_p).map (alpha B q)` for each eligible q, rendering the
  precise equality D T_Q = s(U_p) T_Q.
- The final conjunct quantifies over every prime p of C whose localization is not
  regular local, asserts `p.asIdeal ≠ ⊥`, and asserts `patchedIdeal B J ≤ p.asIdeal`
  whenever some nonmaximal prime contains
  `p.asIdeal ⊔ J.map (algebraMap B C)`. Ideal supremum is ideal sum.
- There is no J-adic completeness, regularity of B, G-ring condition on B, closed
  singular-locus assumption, or independently selected comparison in the binders.

Dependency declarations used (their signatures and docstrings were read):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.NagataRing`: `IsNagataRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion` and
  its canonical ring/algebra map.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom`, and its local-homomorphism instance.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`; its underlying
  prime spectrum is the `PrimeSpectrum` used throughout the ring statement.
- `Sheaf.AlgebraicGeometry.IsRegularScheme` and
  `Mathlib.RingTheory.RegularLocalRing.Defs`: the ring clauses of the recorded
  regular-scheme node are `IsRegularLocalRing` and `IsRegularRing`.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular`.
- `Sheaf.AlgebraicGeometry.FormalCompletionGeometry`:
  `AlgebraicGeometry.absoluteSingularIdeal`. Its owning landed definition node
  `def-per-formal-completion-geometry` was added to stmt_deps.
- `Mathlib.RingTheory.AdicCompletion.Algebra`: `AdicCompletion.liftRingHom`
  constructs `alpha` in this module from its finite quotient maps.
- `Mathlib.RingTheory.LocalRing.RingHom.Basic`: locality of the induced map
  gives preservation of maximal ideals and their powers.
- `Mathlib.RingTheory.Jacobson.Ideal`: `Ideal.jacobson`.
- `Mathlib.RingTheory.Spectrum.Maximal.Basic`: `MaximalSpectrum`.

Every already stated proof dependency's module is imported without `public`,
including the audit-closed `Ideal.map_iInf_of_flat` in
`WeilConjectures.Mathlib.RingTheory.Flat.Equalizer`. The proof dependencies
`lem-per-complete-local-j2`, `lem-per-regular-map-singular-ideal`, and
`lem-per-semilocal-jacobson-completion-product` currently have no Lean record;
they are not used as assumptions or replaced by new axioms. The full six-step
proof and its dependency names are in the theorem docstring for stage 3.

Edge cases checked before writing: when the eligible family is empty the
indexed infimum is top, all localization equalities are vacuous, and the final
containment antecedent cannot hold. In particular a field with J = 0 is covered
(C is the field, all primes maximal, and D is top and nonzero). Empty singular
loci give top singular ideals. J = 0 imposes no artificial restriction on eligible
primes. A maximal singular prime is still covered by the nonzero assertion; it
cannot satisfy the nonmaximal-overprime antecedent. The zero ring is correctly
excluded by the domain hypothesis, not by a new assumption. The arbitrary
universe u is retained by completion, spectra and localization; no size equality
or restricted field-extension universe was introduced.

Searches actually run:

- msearch LeanFinder: `Patching singular locus ideals of completions of a Noetherian
  semilocal Nagata domain along regular completed localization maps`, then
  `Patching singular locus ideals along regular maps from local completions to
  completed localizations`. Returned relative smooth-locus/localization lemmas,
  not this theorem.
- msearch Loogle: `AdicCompletion.map, IsSemilocalRing, RingHom.IsRegular` (no
  useful joint match); `AdicCompletion.liftRingHom` (six universal-property and
  coordinate lemmas, not a patching theorem).
- msearch LeanSearch: `Noetherian semilocal completion singular ideal patching
  regular maps`: eight hits including semilocal local-to-global Noetherianity,
  flat completion, and completion lifts, no matching assertion.
- msearch grep: `absoluteSingularIdeal|semilocal|Semilocal|completionMap` in
  Mathlib RingTheory: semilocal-ring uses, no patching theorem.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `singularIdeal`, `singularLocus`, `absoluteSingularIdeal`, completion map names,
  and `LocalCompletion`: found the absolute singular ideal and the formerly imported completion helper.
  The return correctly identifies that helper as lacking definition-node ownership;
  the repaired alpha is now constructed directly in this item module. The relative
  `Algebra.singularIdeal` would be the wrong notion. No existing statement matches.
- Direct rg in Mathlib AdicCompletion, Localization/AtPrime, Jacobson and
  RegularLocalRing supplied the source signatures of the constructions used.

No new nodes, dependency repairs, statement disputes, or statement correction.
The initial scompile run passed both sandbox and library checks. Final imports
were then made explicit for each recorded statement dependency and rechecked.


## Repair of returned delivery eba09b0bbaf5

H2: removed the import of `Sheaf.TraceFormula.LocalMapCompletionApproximation`
and the theorem node `lem-trf-local-map-completion-approximation` from stmt_deps.
Chose the maintainer's explicitly permitted alternative: define alpha directly in
this item's own module. It now builds the local map on each quotient by a
maximal-ideal power, composes with evaluation, checks compatibility, and applies
`AdicCompletion.liftRingHom`. This supplies real canonical data without a choice
or an approximation-theorem dependency. The local construction cites Stacks 07ED
(lemma-formally-smooth-completion), read in `more-algebra.tex`, and Rotthaus's
comparison diagram. Proof terms establish only the construction's well-definedness;
no extra theorem is introduced or proved, and the only postponed theorem is the item.

Compared the retained sandbox with the returned head's contents and current main:
the returned module and report were retained, while main has no lean record on
this node and its original seven stmt_deps. The repaired delta keeps the existing
absolute-singular-ideal definition dependency and drops the erroneous theorem
edge. The mathematical statement and recorded theorem signature remain unchanged.
No new definition node or dependency module is needed for this authorized alternative.


Repair validation: source inspection showed `map_nonunit` is a root-level Mathlib
lemma, not in namespace `IsLocalRing`; corrected that reference after the first
repair compile. The final check retains the exact recorded theorem signature,
100-column lines, no approximation-module reference, and exactly one `sorry`.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
