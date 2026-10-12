## What changed

Replaced the sole `sorry` in `Sheaf.RingTheory.CompleteLocalGRing` with a compiling
proof of the unchanged theorem `isGRing_of_isNoetherianRing_of_isAdicComplete`.
The proof applies `isGRing_iff_pairsOfPrimes`, installs the local and complete
structure of each prime quotient using `quotient_complete_local`, obtains its
finite regular subring using `complete_local_domain_finite_over_regular`, and
combines the two new generic-formal-fibre lemmas. The exact fraction field in the
criterion is supplied by Mathlib's `IsFractionRing (S ⧸ q) q.ResidueField` instance.
Noetherianity is the first conjunct of the resulting geometric regularity.

Added two statement modules with separate DAG nodes: generic formal fibres of the
regular power-series model, and ascent from a finite Noetherian subring to any
chosen fraction field. The first isolates original steps 5--7. The second isolates
step 4 and the fraction-field identification required to use the existing ascent
statement. They are independent parts of the argument: neither says the G-ring
condition, neither quantifies over prime quotients of an arbitrary complete local
ring, and the finite-ascent statement does not assume locality or completeness.
Updated the original node's proof, proof_deps and proof_origin to the Lean route.

Read Stacks 07PS and 07PP on their official tag pages, since the literature sources
are not installed in this clone. Searches were run through msearch (recorded in
searches.jsonl), along with repository and Mathlib searches. LeanSearch returned
HTTP 500 and is recorded as unavailable; Loogle, LeanFinder and grep ran. No
matching theorem was found. All three modules compile together without warnings.

## Proved and sorry left

Closed one original hole:
`isGRing_of_isNoetherianRing_of_isAdicComplete`
(node `lem-weil-pbc-complete-local-g-ring`). There are no sorries in the item module.

Added exactly two holes, each the complete proof of one public theorem:

- `isGeometricallyRegular_genericFormalFiber_of_regular_powerSeries`, in
  `Sheaf.RingTheory.RegularPowerSeriesGenericFormalFiber`, node
  `lem-weil-pbc-regular-power-series-generic-formal-fibre`.
- `isGeometricallyRegular_genericFormalFiber_of_finite_subring`, in
  `Sheaf.RingTheory.FiniteSubringGenericFormalFiber`, node
  `lem-weil-pbc-finite-subring-generic-formal-fibre`.

This delivery is a decomposition: one upper hole closed, two lower holes added,
net -1 before any whole-closure deduplication. It is not a proof free of sorries.
The imported pairs-of-primes, complete-quotient and regular-subring declarations
remain unproved in the base library and were used as the stage-3 brief requires;
this delivery adds no holes to them. No definition, axiom, target signature or
existing intermediate signature changed.

## No longer needed

Removed these direct proof imports from the item module:

- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` / `pqf-def-quasifinite`:
  scheme quasi-finiteness is not the ring-map condition used by 07PP. The new
  finite-ascent node uses `def-weil-pbc-ring-map-quasi-finite-at-prime` instead.
- `Sheaf.RingTheory.AdicCompletionNoetherian` /
  `lem-weil-pbc-adic-completion-noetherian`.
- `Sheaf.RingTheory.FibreRingNoetherian` /
  `lem-weil-pbc-fibre-ring-noetherian`.
- `Sheaf.RingTheory.CompletionRegularLocal` /
  `lem-weil-pbc-completion-regular-local`.
- `Sheaf.RingTheory.RegularLocalLocalization` /
  `lem-weil-pbc-regular-local-localization`.
- `Sheaf.RingTheory.FormalFibreQuasiFiniteAscent` /
  `lem-weil-pbc-formal-fibre-quasi-finite-ascent`.
- `Sheaf.RingTheory.PowerSeriesPolynomialFormalFiber` /
  `lem-weil-pbc-helper-g-ring-char-p`.

The item no longer separately uses completion or fibre Noetherianity: it extracts
Noetherianity from geometric regularity. Localization, regular completion,
positive-characteristic power-series fibres and quasi-finite ascent are retained
in the two new nodes' proof dependencies, rather than discarded mathematically.
The regular-model node obtains fibre Noetherianity by regularity of its localization.
The localization-base-change and localization-of-regular-ring nodes are now
explicitly named there. No claim is made that a removed direct import is globally
unreached by the other project modules. No unit statement or realized unit step
was bypassed; this node is below the realized nodes of `sk-thm-p1`.

The remaining old `proof_deps` entries removed from the item node are:

- `lem-weil-pbc-local-completion-local-ring`: quotient locality is supplied by Mathlib's
  quotient instance; locality of prime-localization completions is built into the new
  statement signatures.
- `def-weil-pbc-adically-complete-ring`, `def-weil-pbc-noetherian-ring`,
  `def-weil-pbc-g-ring`, and `def-weil-pbc-localization-at-prime`: these remain notions
  used by the item and its statement dependencies, rather than separate proof steps.
- `def-weil-pbc-finite-purely-inseparable-extension` and `def-weil-regular-scheme`:
  the new regular-model node handles the regularity and characteristic argument;
  pure inseparability is also retained in the finite-ascent node's proof plan.

## Where the brief, the DAG or earlier work was wrong

The old route still named scheme quasi-finiteness (`pqf-def-quasifinite`), although
its ring-map ascent dependency was corrected in stage 2 to use the isolated point
of a fibre spectrum. The finite-subring intermediate uses that corrected notion.

The maximal-ideal criterion is not an available shortcut: its comparison step
already depends on the present complete-local G-ring theorem. It would be circular.
The chosen pairs-of-primes and regular-subring dependencies pass the import-cycle
checks. The new-node graph has no path back to the original item.

Edge cases checked mathematically: a field and zero variables in the regular-model
statement; a Cohen ring with zero variables (mixed characteristic); P = 0 and
P maximal; identity subring extension; a finite extension of domains with multiple
primes above a contraction; either choice of isomorphic fraction field; and a
possible zero generic fibre. The finite-ascent result only assumes a domain and
module finiteness, not flatness or a unique prime over the contraction. The
regular-model result retains the field-or-Cohen presentation: regularity alone in
positive characteristic would be insufficient. The full target still handles
non-domain S through each prime quotient, including rings with nilpotents.

## New nodes

`lem-weil-pbc-regular-power-series-generic-formal-fibre` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-power-series-generic-formal-fibre.json`
and is stated in `lean/Sheaf/RingTheory/RegularPowerSeriesGenericFormalFiber.lean`.
It isolates the characteristic split in the last two paragraphs of Stacks 07PS,
using 0AFS, 07NY, and 07PR with m = 0. Its docstring and node give the full argument,
including elimination of the Cohen-ring presentation in positive characteristic.

`lem-weil-pbc-finite-subring-generic-formal-fibre` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-subring-generic-formal-fibre.json`
and is stated in `lean/Sheaf/RingTheory/FiniteSubringGenericFormalFiber.lean`.
It isolates the second paragraph of 07PS using 07PP(1), with finite implies
quasi-finite and the fraction-field transport spelled out. It is independent of
the characteristic argument in the other new node.

No change records were necessary: all existing signatures and public imports
are unchanged. Both nodes inherit the item's chapter, unit and blueprint ancestor;
blueprint searches for generic formal fibres, regular complete rings, finite
subrings and power series found no duplicate statement.

## Second reading by P2

1. Compared the item module with the repository version by diff and checked its declaration
   signature byte for byte. It is unchanged; the diff changes only plain proof imports and
   the proof body. No definition or target statement changes. The two new modules each contain
   one genuinely smaller part of the argument, rather than a restatement of the G-ring theorem.

2. Compiled all three files in dependency order using `lcompile.py --all`, without errors or
   warnings. Inspected every proof and searched for prohibited constructs. The only two sorries
   are the complete proofs of the public theorems listed above. Scratch copies with
   `#print axioms` for each of the three declarations show only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The original theorem therefore remains dependent on open
   dependencies: this is a decomposition, not a sorry-free proof. There is no definition or
   arbitrary data construction in this delivery. The existential regular subring is eliminated
   inside a proposition proof, not used to define data.

3. Read both new theorem signatures, docstrings, and matching node records against the official
   Stacks pages [07PS](https://stacks.math.columbia.edu/tag/07PS),
   [07PP](https://stacks.math.columbia.edu/tag/07PP), and
   [07PR](https://stacks.math.columbia.edu/tag/07PR). The finite-subring statement needs neither
   flatness nor a unique prime above the contraction: module finiteness gives quasi-finiteness
   at every prime, and 07PP(1) handles the selected prime. The arbitrary fraction field is
   transported as an A-algebra, preserving both geometric regularity and Noetherianity.
   Checked identity extensions, fields, zero and maximal primes, multiple primes above a
   contraction, and alternative fraction fields. The model statement retains the field-or-Cohen
   presentation; regularity alone was not substituted. Checked zero variables over fields
   and Cohen rings, and the characteristic-zero argument excluding the Cohen case in positive
   characteristic. Both statements are true and strictly parts of the original argument.
   Repeated msearch with different wording: LeanFinder returned only smooth-localization
   results; Loogle `IsFractionRing, RingEquiv` found the fraction-field transport equivalences,
   but no geometric-regularity theorem; grep found quasi-finite algebra APIs. Also searched
   both source roots, including the DVR and polynomial formal-fibre statements; none supplies
   either complete intermediate statement. The transport and characteristic split would require
   substantive further formalization, so neither hole was closed in a few-minute attempt.

4. Read the top-level reduction and checked the imports against its used declarations. All
   added imports there are plain proof imports. The new modules' public imports supply their
   signature definitions and classes. The pairs-of-primes criterion and regular-subring route
   are retained, and no circular use of the maximal-ideal criterion was introduced. Compared
   every removed old proof dependency with the report; completed the missing entries under
   `## No longer needed`. Read `dag/units/sk-thm-p1.json`: the item is below its realized
   statements and steps, none of which is bypassed. No global module-pruning claim is made.

5. Compared the existing node's fields with the repository: only `proof`, `proof_deps`, and
   `proof_origin` differ, and they describe the actual Lean reduction. Checked the new nodes'
   statements and Lean records against their signatures, proof-dependency unions against
   their steps, and the required source, search, created, chapter, unit, and blueprint fields.
   They match their declarations and the source argument. Existing dependency nodes were read,
   including their formal-fibre ascent and power-series helper declarations.

Second reading changed only this report: completed the old-proof-dependency pruning list and
recorded the independent checks. No Lean declaration, statement, proof, import, or node needed
repair. Closed one original hole and added two lower holes as reported above; net -1 before
whole-closure deduplication.
