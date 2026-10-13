## What changed

The existing component-extension signature and docstring are unchanged. Its proof
combines a compatible-leg existence theorem and a uniqueness theorem. These are
strict logical parts of the original unique-existence statement, in separate new
modules; neither merely renames the full target. No definition or existing public
interface was changed, so no change record or forced adaptation is needed.

Removed the three unused proof imports from the target: localization colimit,
finite-data descent, and unit refinement. The uniqueness module now imports the
statement vocabulary directly instead of publicly importing the existence module,
whose theorem its statement and planned proof do not need.

## Proved and sorry left

Upper hole closed by decomposition:
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension`.
Its assembly proof contains no sorry but depends on the two new theorem holes below.
This is a decomposition, not a completed proof of the original mathematics.

Holes added (two), each with a complete source proof in its docstring:

- `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_exists`:
  node `new-lem-sbc-etale-triples-prime-localization-component-extension-exists`.
- `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_unique`:
  node `new-lem-sbc-etale-triples-prime-localization-component-extension-unique`.

No other holes added, no data definitions introduced. Of the original one theorem,
zero is proved without sorryAx; one is reduced to two strict substatements. Textual
hole accounting for the delivered declarations is 1 closed minus 2 added = -1;
this is not a claim about the pinned whole-library or import-closure ledger.

## No longer needed

Removed imports from the target module:

- `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`
- `Sheaf.Paper.EtaleFiniteDataDescent`
- `Sheaf.RingTheory.EtaleResidueTripleUnitRefinement`

The target's old proof_deps are all replaced by the two new nodes:
`lem-weil-pbc-localization-colimit-principal-localizations`,
`lem-weil-pbc-limit-affine-transition`, `lem-weil-pbc-etale-finite-data-descent`,
`lem-weil-pbc-limit-affine-stage`, `lem-weil-pbc-etale-composition-cancellation`,
`def-weil-pbc-etale-residue-triples`, `lem-weil-pbc-etale-triple-unit-refinement`.
These remain mathematical dependencies of the new substatements' documented proofs.
No mathematical module is claimed globally unreachable from TargetsCheck.
The new uniqueness module no longer imports the new existence module.

## Where the brief, the DAG or earlier work was wrong

The first worker left the two new docstrings without their source and complete
natural-language proofs. Their node statements were not self-contained; their
proof plans did not distinguish existence from uniqueness. The target node still
carried its old descent steps although proof_deps had been changed to the new
assembly lemmas. The report omitted the hole arithmetic and called the upper
hole closed without making clear that its mathematics remains open. These faults
are repaired. Neither new theorem was closed in this reading: a pointed affine
model descent construction is still needed even for uniqueness.

## New nodes

`new-lem-sbc-etale-triples-prime-localization-component-extension-exists` states only
existence of a compatible ring map. Its proof plan constructs a pointed affine
model, inverts denominators using unit refinement and cocone naturality, and
checks arbitrary compatible legs by finite-presentation morphism descent.

`new-lem-sbc-etale-triples-prime-localization-component-extension-unique` asserts
only equality of two compatible maps. It needs descent of a pointed affine model
and localization extensionality, but no extension existence or descent of arbitrary
arrows. Both new statements have their own Lean modules and complete node records.

## Second reading by U2

1. PASS. Compared the existing module with the repository using diff, and compared
   the text from its theorem header through the conclusion byte for byte. The
   signature, visibility, hypotheses, conclusion and existing docstring are
   unchanged. All other delivered modules are new. No definitions were changed.
2. PASS with declared holes. All three files compile locally via lcompile.py.
   Each new sorry is the whole proof of its public named theorem with a matching
   node. There are no axioms, unsafe/opaque declarations, foreign implementations,
   hollow definitions or arbitrary witness data. A scratch copy of each module
   checks its theorem with #print axioms; only standard axioms and the declared
   sorryAx dependency are permitted. The delivery's own per-declaration probe is
   also required to pass before delivery.
3. PASS after repair. Both split statements are strictly weaker logical parts of
   unique existence, with no extra target hypotheses. Tested the identity local
   triple, a field base with p = 0, V = the zero ring, and the impossibility of a
   zero pointed ring mapping to a field. For a field base, the local triple can
   be transported to a global triple, and compatibility with its identity map
   forces the leg, illustrating both parts. General existence follows from the
   documented affine-model/unit-refinement construction; uniqueness follows by
   restricting to that model, without assuming its map is injective. Searches
   using new LeanFinder queries, Loogle localization extensionality, and rg in
   Mathlib, Sheaf and the upstream tree found generic localization and affine-limit
   tools but no noncircular theorem of either exact statement. Downstream cocone
   and comparison results depend on this item and cannot supply a shorter route.
4. PASS after pruning. Kept the correct seven-line assembly proof. Removed unused
   target proof imports and the public existence import from the new uniqueness
   module. Listed every old proof dependency replaced at the target; lower plans
   retain the same mathematical route. sk-prop-input-spreading.realized was read
   and is unchanged; no unit or chapter step is bypassed.
5. PASS after repair. The target node now records precisely the two assembly
   steps and their dependency union. The new nodes now have self-contained
   statements, distinct complete proof plans, exact multiline Lean signatures,
   sources per step and the required origin/search/creation/blueprint fields.
   Every proof_deps list equals the union of its steps' uses.

Changed in the second reading: supplied complete source docstrings and node proof
plans; corrected target proof metadata; pruned unused imports; replaced the new
uniqueness module's public existence import with its direct statement imports;
corrected reporting and hole accounting. No proof body or existing signature changed.
