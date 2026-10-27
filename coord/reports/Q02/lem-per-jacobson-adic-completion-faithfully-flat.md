## Worker report

The module `Sheaf.RingTheory.JacobsonAdicCompletionFaithfullyFlat` states
`AdicCompletion.faithfullyFlat_of_le_jacobson`. Its only theorem proof is `sorry`.
No definitions, auxiliary statements, dependency repairs, or new nodes are needed.
The item's node is copied unchanged except for its `lean` record.

Source checked directly: `literature/stacks-project/algebra.tex`,
`lemma-completion-faithfully-flat`, Tag 00MC, lines 22977 onward. The source's main
assertion is the general Jacobson-radical assertion; its subsequent local-ring
assertion is a corollary, not an additional hypothesis of this node.

Every hypothesis and clause is rendered as follows:

- A commutative ring `R` is `(R : Type u) [CommRing R]`, for an explicitly declared
  arbitrary universe `u`.
- Noetherianity is `[IsNoetherianRing R]`, the declaration recorded by
  `def-weil-pbc-noetherian-ring`.
- The ideal is `(I : Ideal R)`.
- The inclusion in the intersection of all maximal ideals is
  `(hI : I ≤ (⊥ : Ideal R).jacobson)`. `Ideal.jacobson` is the infimum of maximal
  ideals containing its argument; at bottom this is exactly the Jacobson radical
  of the ring.
- The completed ring is `AdicCompletion I R`, the declaration recorded by
  `def-weil-pbc-adic-completion`, with the ring and algebra instances supplied by
  `Mathlib.RingTheory.AdicCompletion.Algebra`. Its data are compatible families in
  `R / (I^n • ⊤)`. On the regular module, `I^n • ⊤ = I^n`. The coordinate at `n = 0`
  lies in the singleton quotient `R / R`, so including zero does not change the
  positive-index inverse limit in the node.
- The canonical ring homomorphism is encoded by the canonical `Algebra R
  (AdicCompletion I R)` instance. Reading that instance and
  `AdicCompletion.algebraMap_apply` confirms that it sends `r` to the family of
  residue classes of `r`. No arbitrary map or algebra structure is quantified over.
- Faithful flatness of that map is the conclusion
  `Module.FaithfullyFlat R (AdicCompletion I R)`, using
  `def-weil-pbc-faithfully-flat-ring-map`. This is equivalent to faithful flatness
  of the canonical algebra map by `RingHom.faithfullyFlat_algebraMap_iff`, and
  follows the project's FAITHFULLY FLAT RING MAPS convention in `coord/STATE.md`.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, defined as
  `IsNoetherian R R`, and its ideal-finite-generation interpretation.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, the compatible-family
  construction, and `AdicCompletion.of`, the canonical map.
- `Mathlib.RingTheory.AdicCompletion.Algebra`: the `CommRing` and `Algebra`
  instances, `AdicCompletion.algebraMap_apply`, and `AdicCompletion.evalOneₐ`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`, defined
  as flatness together with proper maximal-ideal multiples, and the generated
  criterion `Module.faithfullyFlat_iff` (the recorded proof-dependency match).
- `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`:
  `AdicCompletion.flat_of_isNoetherian` (the other proof-dependency match),
  imported as a proof-only dependency.
- `Mathlib.RingTheory.Jacobson.Ideal`: `Ideal.jacobson` and `Ideal.jacobson_bot`,
  available through the public import of the recorded completion dependency.

All three statement dependencies are Mathlib leaves, with usable recorded
interfaces. The maximal-ideal proof criterion's module is already a public
statement dependency. The declaration docstring carries all three proof steps:
Noetherian completion flatness; projection to `R/I` and then `R/m` to show `m`
extends properly; and the flatness/proper-maximal-ideal criterion.

Edge cases checked mathematically before writing:

- `R = 0`: no `Nontrivial R` or maximal-ideal-existence assumption is imposed;
  the completion is zero and faithful flatness holds in the zero-module category.
- `I = 0`: the positive quotients are `R`, the completion map is the identity
  under the canonical identification, and the conclusion holds.
- Nilpotent `I`: the quotients stabilize to `R`, giving the same conclusion.
- A nonlocal product of Noetherian local rings with an ideal inside its Jacobson
  radical is allowed; there is no local-ring or maximal-ideal binder.
- `I = ⊤` is allowed only in the zero ring under the inclusion hypothesis.
- The inclusion is essential: for `R = ℤ` and `I = (2)`, the completion is `ℤ₂`
  and the proper maximal ideal `(3)` extends to the unit ideal. Thus flatness alone
  would not give the stated conclusion, and the inclusion is not hollow.

Searches for an existing declaration (all run for Q02 and this item):

- `msearch.py`, LeanFinder: "The completion of a Noetherian commutative ring along
  an ideal contained in the Jacobson radical is faithfully flat". Eight hits:
  `AdicCompletion.flat_of_isNoetherian`, `AdicCompletion.map_injective`,
  `IsHausdorff.of_le_jacobson`, finite-module tensor/completion comparison results,
  and `IsAdicComplete.le_jacobson_bot`; none states the full conclusion.
- `msearch.py`, Loogle: `"AdicCompletion", "FaithfullyFlat"`. Zero hits.
- `msearch.py`, LeanSearch: "The adic completion of a Noetherian ring is faithfully
  flat when the ideal lies in the Jacobson radical". Eight hits give completion,
  its ring/algebra/module structures, ordinary flatness, complete implies
  Jacobson-contained, and henselianity, not this theorem.
- `msearch.py`, grep, `RingTheory/AdicCompletion`:
  `faithfullyFlat|faithfully_flat|FaithfullyFlat`. Zero hits.
- `rg` in Mathlib's completion directory for faithful-flatness and Jacobson names:
  Jacobson-separatedness and completeness facts only, no faithful-flatness result.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for completion/faithful-flatness
  phrases and declaration patterns: local-completion specializations, pair
  henselization results, and localization/completion-product results occur;
  none states completion along every Jacobson-contained ideal of a Noetherian ring.
  The nearby `FlatCompletion` and `FlatCompletionUniversallyInjective` modules
  were opened and concern different assertions.
- `rg` for this exact node id in `lean/WeilConjectures`: no match.
- `rg` for `faithfullyFlat_of_le_jacobson` in Mathlib, both library roots, and
  `dag/lean_names_upstream.json`: no match; the new declaration name is unused.

No statement dispute or source fault was found. Compilation with the prescribed
`scompile.py` passed in both sandbox mode (1.4 seconds) and library mode
(1.6 seconds), with no errors or unexpected warnings.

## Second reading by Q02

I reopened the node and the completed module for a separate self-check. No other
agent was started, as required by the dispatcher brief; the maintainer supplies
the independent delivery review. Reading the signature afresh gives exactly a
commutative Noetherian ring, an ideal, its inclusion in the Jacobson radical,
and faithful flatness of the canonical completion algebra. In particular, the
signature neither assumes locality nor quantifies over an arbitrary algebra
structure. The positive-index convention, zero-ring case, and the interpretation
of `Module.FaithfullyFlat` agree with the node and its recorded dependencies.
There are no extra conclusions and no missing hypotheses. No change was needed
after this reading.
