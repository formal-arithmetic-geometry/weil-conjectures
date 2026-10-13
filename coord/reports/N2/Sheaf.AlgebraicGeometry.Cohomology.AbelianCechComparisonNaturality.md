## What changed

Replaced the original `abelianCechComparison_naturality` sorry with the actual
resolution-lift argument, keeping its signature and docstring byte for byte.
Added real degreewise section and Cech total cochain maps, proved their alpha
and beta augmentation squares, and proved the section-cycle existence and
section-homology-to-Ext injectivity lemmas in six new modules (one per result).
All additional imports of the original module are proof-only. No existing
statement, definition or public import was changed; no change record is needed.

The restart recompiled all seven modules, removed the unnecessary file-wide
elaboration option, and corrected the two definition-node signature records to
match the delivery parser (which omits the `noncomputable` modifier). The previous
second-reading text was removed; the independent reader supplies that section.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.Modules.abelianCechComparison_naturality` (1 of 1).
Also proved `abelianCechAlpha_square`, `abelianCechBeta_square`,
`abelianCech_ext_section_cycle`, and `abelianCech_ext_section_injective`.
The new definitions `abelianCechSectionsMap` and `abelianCechTotalMap` are actual
functorial constructions. Holes added: none. Holes left in delivered modules:
none. An earlier attempt's unresolved `abelianCechComparison_naturality_apply`
and its new node were removed, rather than delivered as a restatement.
This closes one original hole without adding a lower hole; it is not a decomposition.
The existing section-augmentation quasi-isomorphism and its imported
prerequisites remain the inherited proof dependencies. Independent `#print axioms` checks show that every delivered declaration,
including naturality, uses only propext, Classical.choice and Quot.sound;
none depends on sorryAx.

## No longer needed

No original proof dependency or original import was pruned: construction and
`lem-pc-abelian-cech-alpha-quasi-iso` remain used. The undelivered pointwise Aux
module and node were discarded. Identical sandbox copies of Construction and
AlphaQuasiIso were removed from the delivery. Pruned library modules: none. The direct Mathlib Injective.Resolution import
is needed for the chosen `injectiveResolution`; removing it was tested and
produced an unknown-identifier error, so it is retained.

## Where the brief, the DAG or earlier work was wrong

The first worker's pointwise helper was equivalent to the entire naturality
target, with extensionality as the only reduction. Its earlier second-reading
claim that this was a strictly smaller statement was wrong. It was replaced
by genuine, fully proved steps of the original augmentation-square plan.

Searches found Mathlib resolution descent, extMk_surjective,
extMk_comp_mk0, extMk_eq_zero_iff, liftCycles_i, the total-map summand formula,
and additive adjunction evaluation. No specialized naturality proof exists
in Mathlib or the upstream Cech module. LeanSearch was unavailable (HTTP 500);
its actual requests are logged, and LeanFinder, Loogle and source grep ran.
The existing `abelianCechExtSectionIso_exists` is still a sorry and asserts
existence of an isomorphism with selected representatives, not the all-pairs
injectivity lemma used here. We avoid adding that hole to this proof's closure
by proving the needed representative and injectivity facts directly.

The literature route was checked against Stacks Tags 01EQ and 01FD. The
coefficient-functoriality verification omitted in 01EQ is now implemented.

## New nodes

`def-pc-abelian-cech-sections-map` records the real degreewise global-section
map in `AbelianCechSectionsMap.lean`.

`def-pc-abelian-cech-total-map` records the real Cech/flip/total map in
`AbelianCechTotalMap.lean`.

`lem-pc-abelian-cech-alpha-square` records the proved restriction square in
`AbelianCechAlphaNaturality.lean`.

`lem-pc-abelian-cech-beta-square` records the proved coefficient square in
`AbelianCechBetaNaturality.lean`.

`lem-pc-ext-section-cycle` records the proved adjunction cycle lift in
`AbelianCechExtSectionCycle.lean`.

`lem-pc-ext-section-injective` records the proved boundary/Ext cancellation
in `AbelianCechExtSectionInjective.lean`.

All new node JSON files are under `dag/nodes/sec-picard-framework/`.
Change records: none.

## Second reading by N2

1. PASS: Diffed the original module against the repository. The existing
   signature, docstring, visibility, and public import are byte-for-byte
   unchanged; only proof-only imports and the proof body were added. The six
   other delivered modules are new. No statement or definition was changed,
   and no change record or forced adaptation is needed.
2. PASS: Independently compiled all seven modules through lcompile.py in
   import order, with no errors or warnings. Scanned the sources for sorry
   and forbidden declarations/attributes: none. A scratch copy printed axioms
   for all seven public declarations: precisely propext, Classical.choice,
   and Quot.sound, with no sorryAx. The section and total maps are actual
   functor maps; no arbitrary witness of an unproved existence theorem is
   used to construct data.
3. PASS: No unresolved statement is split off. Read all four helper proofs
   and both definitions. The augmentation squares hold for any open family;
   the cycle lift uses the kernel universal property; the Ext injectivity
   proof separately handles degree zero (no incoming boundary) and positive
   degree (a boundary preimage). Empty spaces, zero coefficients, empty and
   infinite open families introduce no extra assumption. Independent
   LeanFinder search for evaluation-at-one cocycles/boundaries and Loogle
   search for InjectiveResolution.extMk_eq_zero_iff, plus source searches in
   lean/ and Mathlib, found generic APIs already used, not an exact duplicate.
   Read AbelianCechExtSectionIso_exists and the comparison core: their open
   existence assertions do not replace the proved all-representative lemmas.
4. PASS: The original hole is closed by a genuine resolution lift, alpha/beta
   squares, Ext representatives, and cancellation. No lower hole replaces
   it. Each direct import supplies a declaration needed by a signature,
   construction or proof; additional imports in the original are private
   to its proof. Both old proof dependencies are still used, so the report's
   empty pruning list is complete. Read sk-thm-picard-rr.json: this item is
   below its unit-level route, and no realized statement or step is bypassed
   or changed.
5. PASS: Read every delivered node and compared the existing node with its
   repository version: only proof, proof_deps, and proof_origin differ.
   Dependencies equal the union of the steps' uses and follow the actual
   Lean argument. New nodes include the required source, searches, origin,
   creation, blueprint, chapter/unit, and exact Lean signature records.

Second reading changed only this report: recorded the independent checks and
replaced the provisional inherited-axiom wording with the measured axiom
result. No Lean or DAG repair was necessary.
