## What changed

Reduced `AlgebraicGeometry.formalComparison_completed_affine_model` to two strictly
smaller intermediate statements, preserving its entire signature and existing docstring.
The proof specializes the generic affine realization to the formal completion of
`f_*F`, destructures its witnesses, proves their restriction invertible using the
second lemma and packages the same witnesses with their commuting square.

Added proof-only imports of `Sheaf.AlgebraicGeometry.FormalAffineMorphismRealization`
and `Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineRestrictionIso` to the
item. Added one theorem per new module, with complete proof-in-words docstrings,
sources, and corresponding nodes. Updated only `proof`, `proof_deps`, and
`proof_origin` in the item's node. No existing definitions, statements, or public
imports changed; no forced adaptations are needed.

The first intermediate lemma is generic in both formal systems and their morphism:
it requires no proper morphism, exceptional ideal, beta, kappa, or comparison
equations, and asserts no exceptional-locus invertibility. The second supplies no
coherent objects, map, or limit isomorphisms: it takes all of these as inputs and
uses a commuting-square hypothesis to prove only restriction invertibility. It
therefore cannot produce the target's existential model without the first lemma.
The target contains a complete Lean proof combining these distinct parts.

The second reader proved the generic realization theorem from the existing natural
affine limit model, finite presentations and the tilde/Gamma unit. Its added imports
are proof-only. The existing affine limit model still has a deferred proof.

Validation: `lcompile.py --all` compiled all three modules without errors or warnings.
No data definitions, axioms, private holes, or new global instances are introduced.
Existential witnesses are eliminated inside a theorem proof; no data is selected
from an unproved existence theorem for use in a definition.

Edge cases: on an empty affine or when J(U) is the unit ideal, R is the zero ring
and the evaluated formal systems and coherent models vanish. For J=0 the generic
realization is the ordinary affine coherent/finite-module correspondence. For K=0,
the proper morphism is globally an isomorphism and the canonical comparison is
invertible. For K the unit ideal, the restriction is to the empty complement and
invertibility is automatic. Zero source/target systems are covered by the same
construction. Arbitrary B-linear limit isomorphisms in the second lemma are valid:
finite R-modules are adically complete and a B-linear map is R-linear by reduction
modulo every ideal power, density of B and separatedness. The square is essential;
invertibility of a freely chosen c is not asserted.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.formalComparison_completed_affine_model`
(node `lem-weil-pbc-formal-comparison-completed-affine-model`). No sorry remains in
the item's module.

New declaration proved: `AlgebraicGeometry.formal_affine_morphism_realization`
(`lem-weil-pbc-formal-affine-morphism-realization`), by the second reader. Its proof
uses `AlgebraicGeometry.coherentFormalModule_affine_limit_model`, which is already
in the library and still deferred; no new hole is added by the realization module.

One hole added, in its own public named theorem with proof exactly `:= by sorry`:

- `AlgebraicGeometry.formalComparison_completed_affine_restriction_isIso`
  (`lem-weil-pbc-formal-comparison-completed-affine-restriction-iso`).

This is a decomposition, not a sorry-free mathematical proof: one original upper
hole closed, one strictly smaller lower hole added (net 0 in the delivered sources).
The additional realization theorem has no local hole but rests on the existing
affine-limit-model hole. These source counts are not a claim of positive progress
in the targets' import closure; the maintainer's pinned ledger determines that.

## No longer needed

No original Lean import was removed. No whole module is claimed to leave the
targets' import closure. In particular the affine equivalence, formal functions,
tensor pullback and full faithfulness remain needed in the two smaller arguments.

All twelve old direct `proof_deps` are replaced at the item by the two new nodes:

- `lem-weil-pbc-theorem-formal-functions`
- `lem-weil-pbc-coherent-formal-modules-affine`
- `lem-weil-pbc-formal-systems-pullback`
- `lem-weil-pbc-adic-completion-noetherian`
- `lem-weil-pbc-noetherian-completion-flat`
- `lem-weil-pbc-adic-completion-mod-power`
- `lem-pc-flat-base-change-cohom`
- `def-pc-module-pullback`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `pqf-lem-coherent-ft-locnoeth`
- `lem-weil-pbc-formal-completion-fully-faithful-proper`
- `lem-pc-coherent-hi`

Eleven remain below the new restriction node. The exception is
`lem-pc-flat-base-change-cohom` (`Scheme.Modules.finrankH_pullback` in
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`), replaced by the existing
`lem-weil-pbc-flat-base-change-resolution-iso` and
`lem-weil-pbc-flat-base-change-map-sections`. No whole module is claimed pruned.

The realization node now uses `lem-weil-pbc-formal-affine-limit-model`,
`lem-weil-pbc-adic-completion-noetherian`, `pqf-lem-coherent-ft-locnoeth` and
`lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-sc-noetherian-finite-module-finite-presentation`. Its previous direct generic
restriction/equivalence plan is subsumed by the existing natural limit model.

No annihilation theorem or support-radical theorem is imported into this item;
they belong above this coherent comparison construction.

## Where the brief, the DAG or earlier work was wrong

The original plan's `lem-pc-flat-base-change-cohom` Lean declaration has field-base
and dimension restrictions and does not state the completed-ring pushforward/map
comparison required here. Existing canonical flat-base-change statements now
provide the relevant plan interfaces; the new restriction-isomorphism node names
them. The first generic realization requires affine restriction, the natural
limit cones of the affine equivalence and tilde coherence, but no formal-functions
comparison for a proper morphism. The original plan mixed that generic construction
with the geometric invertibility argument.

The new generic realization is implied by Stacks 087W plus affine tilde coherence
(01XZ); the restriction claim follows the completed-base adjunction argument in
088B. The item is not among `dag/units/sk-thm-p1.json`'s realized statement or step
nodes. No unit statement, step, or chapter route is bypassed.

Searches ran using msearch: LeanFinder, Loogle, Mathlib grep and LeanSearch. They
found limit-of-affine-scheme, completion tensor-product, and ordinary adjunction
lemmas, but no exact statement. LeanSearch returned HTTP 500 and is recorded as
unavailable, not absence evidence. Local searches of both library roots found the
original target and its caller but no replacement. Whole-blueprint searches for
`affine formal` and `formal` found no duplicate of either new statement.

## New nodes

`lem-weil-pbc-formal-affine-morphism-realization` states realization of any formal
morphism on an affine open by a coherent sheaf map over its completed coordinate
ring, with the naturally commuting affine-limit square. Its new module is
`lean/Sheaf/AlgebraicGeometry/FormalAffineMorphismRealization.lean`.

`lem-weil-pbc-formal-comparison-completed-affine-restriction-iso` states only the
exceptional-locus invertibility of a supplied coherent realization of the canonical
comparison. Its new module is
`lean/Sheaf/AlgebraicGeometry/FormalComparisonCompletedAffineRestrictionIso.lean`.

No change records are required; no existing interface changed.

## Second reading by J2

1. PASS: Compared every delivered module with the repository. The item differs
   only in two plain proof imports and its proof body. Its existing declaration
   signature and docstring are byte-for-byte unchanged. Both other modules are
   new. No existing definition, public import, target statement or visibility
   changed; no change record or forced adaptation is needed.
2. PASS: Compiled all three modules with lcompile.py. The only remaining local
   sorry is the public named restriction theorem, with source and complete proof
   docstring. There are no definitions, unsafe features, axioms or private holes
   in this delivery. Scratch-copy #print axioms checks allow only the three
   standard axioms and sorryAx from deferred statements. Witnesses are eliminated
   inside proofs, with concrete tilde constructions; no global data definition
   chooses an arbitrary witness of unproved existence.
3. PASS: Read both new statements clause by clause and their sources, Stacks
   [087W](https://stacks.math.columbia.edu/tag/087W) and
   [088B](https://stacks.math.columbia.edu/tag/088B). Checked empty U, J=0,
   J=unit, K=0, K=unit, zero systems, arbitrary section isomorphisms and arbitrary
   adjunction. The restriction square is essential, and B-linear conjugacies are
   R-linear by ideal-power continuity and separatedness. Each statement is a
   strictly smaller part of the original argument, not a renamed restatement.
   Independent msearch LeanFinder/Loogle/grep queries used completed-scalar
   linearity, compatible inverse systems and restriction of scalars; rg of both
   library roots found the existing natural affine limit model. Used that result
   to close the realization hole instead of duplicating its deferred proof.
4. PASS after repair: Preserved the top-down existential construction and
   restriction argument. All added proof dependencies use plain imports; the
   statements' original public imports remain. Removed an unnecessary candidate
   FiniteDescent import before delivery. Listed all twelve replaced old direct
   dependencies and distinguished them from globally pruned modules (none).
   Read dag/units/sk-thm-p1.json realized: this item realizes no protected unit
   statement or step, and no unit/chapter route is changed.
5. PASS after repair: Existing-node changes are only proof, proof_deps and
   proof_origin. New nodes have source, complete statements, statement/proof
   dependencies, search records, created/blueprint/chapter/unit metadata, and
   verbatim Lean signatures. Rewrote the realization node to match its actual
   proof through the existing affine-limit-model declaration. The restriction
   node records the still-deferred geometric argument.

Changed: proved formal_affine_morphism_realization, added its five proof-only
imports, updated its proof metadata, clarified continuity and arbitrary-adjunction
points in the restriction proof-in-words, corrected hole accounting, and completed
No longer needed. The item proof itself needed no repair.

Validation evidence: final import-order compilation succeeded (36.3 s, 3.4 s,
3.7 s). Each scratch-copy axiom check succeeded and printed exactly
`[propext, sorryAx, Classical.choice, Quot.sound]`. Scratch copies are kept under
`scratchpad/`, outside the delivered Lean source tree.
