## Worker report

The module `Sheaf.RingTheory.CompletedMaximalLocalizationsDetectZero` states
`ModuleCat.completedMaximalLocalizations_detect_zero`. Its only theorem proof is
`sorry`. No new notions, helper definitions, dependency modules, statement changes,
or extra axioms are introduced. Only the item's `lean` field changes.

The node and all seven statement-dependency records were read, and the recorded
Mathlib declarations and `ModuleCat.ordinaryDerivedExtendScalars` were read in full
with their docstrings. The relevant source statements were read locally in
`literature/stacks-project/algebra.tex`: Tag 00HN, label
`lemma-characterize-zero-local`, lines 4051ff; Tag 00MC,
`lemma-completion-faithfully-flat`, lines 22977ff; Tag 0316,
`lemma-completion-Noetherian-Noetherian`, lines 23065ff; Tag 05GG,
`lemma-hathat-finitely-generated`, lines 22645ff; and Tag 05GI,
`lemma-radical-completion`, lines 22734ff. The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
and its proof were read. This item is an auxiliary of its recorded semidualizing
conservativity branch, not the statement of that blueprint unit.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary commutative Noetherian ring is `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`. There is no `Nontrivial R` assumption.
- The ordinary, unbounded module derived category is
  `DerivedCategory (ModuleCat.{u} R)`. It uses the ordinary-module small-Hom
  derived-category instance supplied by the recorded change-of-rings interface.
  There is no boundedness, perfectness, or finite-generation binder on `K`.
- Each maximal ideal is quantified as `∀ (m : Ideal R) [m.IsMaximal]`. Its
  primality instance supplies `Localization.AtPrime m`, which is exactly
  `Localization m.primeCompl`, hence localization at `R \ m`.
- The extended ideal `m Rₘ` is `m.map (algebraMap R (Localization.AtPrime m))`.
  No choice of an ideal or of a localization map is made.
- The ring `Bₘ` is written out everywhere as
  `AdicCompletion (m.map (algebraMap R (Localization.AtPrime m)))
  (Localization.AtPrime m)`. This is the existing compatible-sequence
  construction. Mathlib indexes the quotients by all natural numbers; the
  zeroth quotient is zero and contributes a forced coordinate, so this is the
  same inverse limit as the node's `n ≥ 1` indexing.
- `IsNoetherianRing (Localization.AtPrime m)` and
  `IsLocalRing (Localization.AtPrime m)` assert the localization properties.
  `(m.map (algebraMap R (Localization.AtPrime m))).IsMaximal` identifies the
  extended ideal as its maximal ideal: a local ring has a unique maximal ideal,
  so maximality of this specified ideal is equivalent to equality with that
  unique ideal. This avoids a dependent local-ring instance binder.
- `Nontrivial Bₘ`, `IsNoetherianRing Bₘ`, and `IsLocalRing Bₘ` assert precisely
  the three stated completion properties.
- The next `.IsMaximal` conjunct is on the ideal
  `(m.map (algebraMap R Rₘ)).map (algebraMap Rₘ Bₘ)`. Together with
  `IsLocalRing Bₘ` it states that the maximal ideal is exactly `(m Rₘ) Bₘ`.
- `IsAdicComplete` is applied to that same extended ideal as an ideal of `Bₘ`,
  and to `Bₘ` as its module over itself. Completeness is thus for the specified
  extended ideal, not merely for an ideal acting from `Rₘ`.
- `Module.FaithfullyFlat Rₘ Bₘ` is faithful flatness of the canonical completion
  algebra map. `Module.Flat R Rₘ` and `Module.Flat R Bₘ` state flatness of the
  two canonical maps from `R`. These are exactly the module versions in the
  recorded flat and faithfully-flat ring-map nodes. The completion's `R`-algebra
  map is its localization algebra map followed by the completion algebra map,
  by `AdicCompletion.algebraMap_apply`.
- The second outer conjunct quantifies over every `K` in that ordinary derived
  category. `IsZero K ↔ ∀ (m : Ideal R) [m.IsMaximal], IsZero (...)` is exactly
  the vanishing equivalence, in both directions. The object inside the last
  `IsZero` is `(ordinaryDerivedExtendScalars (algebraMap R Bₘ)).obj K`.
  This uses the dependency's canonical universal left-derived functor with its
  K-flat computation counit; it is not an arbitrary supplied functor or map.

Statement dependencies used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, with the
  ordinary-module instance inherited from the next derived-change import.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, the module
  localization notion; its ring specialization is the quotient construction
  `Localization`, used through `Localization.AtPrime` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`.
- `Mathlib.RingTheory.AdicCompletion.Basic`, publicly through
  `Mathlib.RingTheory.AdicCompletion.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, the commutative ring structure and canonical algebra maps.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`.
- `Mathlib.RingTheory.RingHom.Flat`: `Module.Flat` / `RingHom.Flat`; the statement
  uses the module form for the canonical algebra structures.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.ordinaryDerivedExtendScalars`, built from
  `ModuleCat.OrdinaryDerivedChangeOfRings` and its existence theorem. Its full
  universal-pair signature, K-flat computation clause and chosen-functor
  definition were read.

Recorded proof-dependency modules are imported without `public` where they are
not also statement dependencies: localization Noetherianity and flatness,
`WeilConjectures.RingTheory.AdicCompletionNoetherian`, completion locality and
completeness, faithful flatness, flat transitivity, exact-functor descent,
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`, preservation of homology, and
maximal-ideal existence. The declaration docstring gives all seven DAG proof
steps, including the tensor identifications, annihilator argument, and zero-ring
case. No import cycle is introduced.

Edge cases checked before finalizing the statement:

- Zero ring: there are no maximal ideals, so the first outer conjunct and the
  right side of the equivalence are vacuous. Every unital module is zero,
  since `x = 1 • x = 0 • x = 0`, so every derived object is zero. No ring
  nontriviality assumption excludes this case.
- Field: the single maximal ideal is zero. Its localization is the field and
  its zero-adic completion is the field. The equivalence reduces to identity
  scalar extension detecting zero.
- General nonlocal ring: no claim is made that `R → Bₘ` is faithfully flat for
  one fixed `m`; only `Rₘ → Bₘ` is. All maximal ideals are quantified.
  For example, over `ℤ`, completion at one prime misses torsion at other primes.
- Arbitrarily unbounded `K` and cohomology modules of arbitrary generation:
  flatness gives the cohomology formula in each integer degree, and the
  annihilator/localization argument has no finite-generation requirement.
- The completion uses the extended ideal before any maximal-ideal
  identification, and the completion ideal in the completeness clause is the
  image under its actual canonical algebra map. There is no noncanonical
  ideal or scalar action.

Searches actually run:

- `msearch.py ... leanfinder "Completed maximal localizations jointly detect
  zero objects in the unbounded derived category of modules over a Noetherian
  ring"`: eight hits, including `DerivedCategory.isLE_iff`,
  `DerivedCategory.isGE_iff`, and bounded representative existence. None states
  the complete-local tests and joint zero detection.
- `msearch.py ... leansearch "Completed local rings at maximal ideals detect
  zero in the unbounded derived category"`: eight hits, including
  `isLocalRing_of_isAdicComplete_maximal` and
  `ideal_eq_bot_of_localization'`. These concern local ring properties or ideals,
  not this theorem about all derived objects.
- `msearch.py ... loogle "AdicCompletion, Module.FaithfullyFlat"`: zero hits.
- `msearch.py ... grep
  "(AdicCompletion|adicCompletion).*(FaithfullyFlat|faithfullyFlat)|completed.*detect.*zero"`:
  zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for completed/maximal zero
  detection and `ordinaryDerivedExtendScalars`: found the existing scalar
  extension interface and its consumers, but no theorem stating this item.
- `grep -rn` for the exact item id in `lean/WeilConjectures`: no hit.
- `rg` for the proposed declaration name in `dag/lean_names_upstream.json`,
  `lean/WeilConjectures`, and `lean/Sheaf`: no hit.

No statement is disputed. The inherited `source.place` mentions 00HN parts (2)
and (6); the actual zero-module argument is (1)--(2), as already recorded in the
node's proof and proof_origin. This metadata inaccuracy does not affect the
statement, and was not changed outside the authorized `lean` field.

Validation: `scompile.py NF lem-trf-completed-maximal-localizations-detect-zero
<file>` compiled the module in sandbox and library modes cleanly (2.5 s and
1.9 s respectively). All variables and the universe are explicit, and all lines
are at most 100 characters.

## Second reading by NF

A second pass in this worker session compared the completed file with the node;
no separate reader agent was started, as the dispatcher's brief prohibits it.
The maintainer's independent delivery review remains the independent review.

This pass checked both outer conjuncts separately. The first quantifies exactly
over maximal ideals and contains the localization's Noetherianity, localness and
specified maximal ideal, followed by the completion's nontriviality,
Noetherianity, localness, specified maximal ideal, completeness, faithful
flatness over the localization, and both flatness assertions from `R`. The
`.IsMaximal` clauses are on the explicit extended ideals; localness makes these
exact identifications of the unique maximal ideals, rather than mere existence
of some maximal ideal. In particular there is no missing maximal-ideal equality
hidden by notation.

The second conjunct uses `DerivedCategory (ModuleCat.{u} R)` with the exact
ordinary-module derived scalar extension from the recorded dependency. It
quantifies over every `K`, and then every maximal ideal, with `IsZero` on both
sides of the biconditional. No nonzero-ring, boundedness, or finiteness assumption
was found. `Bₘ` is the same explicit Mathlib completion in every occurrence, and
its canonical scalar map is used in the last object. No mismatches were found
and no statement correction was needed.
