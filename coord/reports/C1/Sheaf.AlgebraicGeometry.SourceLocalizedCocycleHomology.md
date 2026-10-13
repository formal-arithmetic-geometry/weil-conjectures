## What changed

Proved `AlgebraicGeometry.Etale.sourceLocalizedCocycleHomology` in
`lean/Sheaf/AlgebraicGeometry/SourceLocalizedCocycleHomology.lean` without changing
its signature, definitions, visibility, or imports. A theorem-local
`backward.defeqAttrib.useBackward` option enables elaboration of the categorical
rewrites, matching the options of the underlying Mathlib lemmas. The proof first expresses
free-generator evaluation as evaluation of a composite sheaf morphism. It computes
the inverse bounded-below Hom comparison and localization of a cocycle, cancels
the bounded-below shift comparison, and uses naturality of the homology shift to
move the transport along `r.inv` to the end. Mathlib's
`DerivedCategory.shiftMap_homologyFunctor_map_Q` then reduces to ordinary complex
homology. The single-source homology isomorphism removes the source single complex;
its induced cycle map is the lift of the degree-zero component of the shifted chain
map. `CochainComplex.liftCycles_shift_homologyπ_assoc` unshifts this cycle, and
`Cochain.rightShift_v` together with `Cochain.fromSingleMk_v` recovers `f`.

The existing node's proof already describes exactly this route, with the same
proof dependencies, so no node change or new node is needed. The unit's realized
statement and steps are unaffected. All work is confined to the assigned sandbox.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.sourceLocalizedCocycleHomology`
(node `lem-weil-pbc-source-localized-cocycle-homology`). This is a complete proof,
not a decomposition. No holes added and no `sorry` remains in the delivered module.
`sourceCocycleHomologySection` is unchanged.

The proof uses no restriction to nonnegative degrees, no extra hypothesis on `f`,
and no stalk or strict-henselization comparison. It therefore retains the original
integer-degree, zero-cycle, and boundary cases.

## No longer needed

None. The sole public import
`Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison` is required by both
the statement and the proof. Its exported definitions and the canonical germ-map
definitions are the planned dependencies. No proof import was added. No node or
module of the existing proof plan was bypassed or pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The stated dependencies supply
constructions rather than a ready-made compatibility lemma, so their definitions
must be computed explicitly. A broad unfolding experiment exceeded the local
single-file limit; the final proof uses bounded unfolding and explicit categorical
rewrites instead.

The three prescribed searches were run through `msearch.py`: Lean Finder found
`CochainComplex.liftCycles_shift_homologyπ` and related Hom-complex homology lemmas;
Loogle's `"liftCycles", "single"` query returned no hits; grep found shift-map
infrastructure. Repository and Mathlib searches found the localization,
single-homology, and shift lemmas used above. No new search record or new axiom
was introduced.


## Second reading by C1

1. **Interface: PASS.** Diffed the only delivered module against the repository.
   The existing theorem signature and the complete body of
   `sourceCocycleHomologySection` are byte-for-byte unchanged. The imports,
   visibility, universes, assumptions and docstrings are unchanged. The only
   changes are the proof and a theorem-local backward-defeq elaboration option;
   no change record is required. No other module or node is delivered.
2. **Proof: PASS.** Compiled the complete module with `lcompile.py`, without
   errors or warnings. Scanned for prohibited declarations and kernel bypasses:
   none; no `sorry` remains, including in definitions. A scratch copy prints
   axioms for both public declarations: exactly `propext`, `Classical.choice`,
   and `Quot.sound`; no `sorryAx` or other axiom.
   The calculation cancels the inclusion shift isomorphism, applies naturality
   along `r.inv`, uses Mathlib's localization-to-homology comparison, identifies
   the single source with its degree-zero cycles, then unshifts the cycle back
   to `f`. Every equality retains arbitrary integer `n` and the stated cycle
   hypothesis. No arbitrary data is chosen from an unproved existence theorem.
3. **Split statements: PASS (none).** No new declarations, nodes or holes were
   added. The one original hole is closed by a calculation, not renamed or
   restated. Zero cycles, boundaries and negative degrees require no extra
   assumption: the calculation uses the canonical cycle quotient and integer
   shift lemmas throughout.
4. **Route and pruning: PASS.** Read both planned dependency nodes and their
   relevant constructions. Repository searches by localization, cocycle,
   single-complex homology and cycle maps, plus independent Mathlib grep via
   `msearch.py`, found general shift and single-homology tools already used by
   the proof, but no existing public theorem replacing this compatibility
   calculation. The sole public import provides definitions appearing in the
   signature and is required. Both old proof dependencies remain used, so
   `No longer needed: None` is complete. The unit `sk-prop-h2` has empty
   `realized` entries in the existing repository; this delivery changes none
   of them and bypasses no unit statement or proof step.
5. **DAG: PASS.** The existing node's proof describes this very calculation:
   localization of the cocycle, single-source homology, homology shifts,
   natural transport along `r.inv`, and free-generator evaluation. Its
   `proof_deps` name exactly the two constructions used, and `proof_origin`
   records an explicit compatibility calculation by an agent. No new node
   fields or source changes are needed.

Second reading changed only this report: documented the theorem-local
elaboration option and added the five review verdicts. The Lean proof was
retained unchanged.
