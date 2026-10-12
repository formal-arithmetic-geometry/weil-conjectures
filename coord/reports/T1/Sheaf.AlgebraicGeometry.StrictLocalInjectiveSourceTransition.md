## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.strictLocalInjectiveSourceIso_transition`
by a real composition of two separate naturality squares. Added two proof-only imports,
`Sheaf.AlgebraicGeometry.SourceDerivedSectionsNaturality` and
`Sheaf.AlgebraicGeometry.SourceStageSectionsNaturality`. The former treats derived Hom
and free-generator evaluation on an arbitrary site; the latter treats stage restriction
already on chain complexes, without injectivity or a derived object. Naturality of
`DerivedCategory.homologyFunctorFactors.inv` supplies the final square.

Removed the first worker's identical core theorem and its node. The existing comparison
module in the sandbox is byte for byte identical to the repository: it is compiled only
to provide the local dependency artifact. No existing signature, definition or visibility
is changed. Repaired the new nodes' missing fields and made the original node's proof
and dependencies describe the actual reduction.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.strictLocalInjectiveSourceIso_transition`
(node `lem-weil-pbc-strict-local-injective-source-transition`).

Added two holes, each a named public theorem with a source and full written proof:
- `AlgebraicGeometry.Etale.sourceDerivedSections_naturality`
  (node `lem-weil-pbc-source-derived-sections-naturality`).
- `AlgebraicGeometry.Etale.sourceStageSectionsIso_naturality`
  (node `lem-weil-pbc-source-stage-sections-naturality`).

This is a decomposition, not a sorry-free proof or net progress: one hole closed and two
added, an unadjusted net of minus one. There is no sorry in the assigned module and no
sorry in a definition. Both smaller statements still require formal proofs; neither
merely restates the assigned theorem. The deleted
`AlgebraicGeometry.Etale.strictLocalInjectiveSourceIso_transition_core` did restate it
and is not included or counted. The global ledger determines closure figures.

## No longer needed

No import removed and no module claimed pruned. The old direct proof dependencies
`lem-weil-pbc-etale-inverse-image-restriction` and
`lem-weil-pbc-injective-sections-pullback-comparison` are no longer direct dependencies
of the transition proof: the stage naturality subargument and the imported comparison
construction still use their infrastructure transitively. They are not claimed pruned
from the targets' import closure. The original comparison and canonical germs nodes
remain direct dependencies; the two new naturality nodes replace the omitted direct edges.

## Where the brief, the DAG or earlier work was wrong

The first worker's core theorem had exactly the original hypotheses and conclusion,
and the wrapper merely applied it. This was a restatement rather than a reduction.
The report incorrectly said the two naturality imports were retained, though they were
absent and unused. The new nodes lacked required signatures, search records, creation
and blueprint metadata. These faults have been repaired.

The unit recorded for this item, `sk-prop-h2`, has empty realization lists; its fixed
Kummer route does not designate this transition node as a step. This delivery changes
only the local injective-complex computation below the unit level and keeps the
comparison construction and the two parts of the original node's planned argument.
No unit or chapter route is changed. [Stacks Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8) and
[Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9) were checked directly;
03S2 concerns étale restriction and its extension-by-zero adjoint.

## New nodes

`lem-weil-pbc-source-derived-sections-naturality` isolates naturality of the derived
Hom, Hom-complex cohomology, and free-generator evaluation comparisons, for any site
and any K-injective representative. It is independent of the stage geometry.

`lem-weil-pbc-source-stage-sections-naturality` isolates the chain-level stage-sections
restriction equation, for any complex. It is independent of derived localization,
boundedness, K-injectivity, and the integer cohomology degree.

No change record is needed because all existing signatures and definitions are unchanged.

## Second reading by T1

1. Compared every delivered existing module with its repository source. The original
   theorem signature is byte for byte unchanged. The comparison module is identical.
   New imports are plain proof-only imports. No definition, hypothesis, conclusion,
   public dependency or target statement is changed. Verdict: pass after repairs.
2. Inspected every delivered declaration for prohibited constructs and hollow data.
   Only the two named split-off theorems contain sorry. Compiled the delivery locally
   in dependency order and checked declaration axioms through scratch probes and the
   delivery tool. Only propext, Classical.choice, Quot.sound and inherited sorryAx are
   permitted. The scratch probe showed exactly these four axioms for the transition
   and the two smaller statements; the comparison definition itself uses only the
   three standard axioms and no sorryAx. The transition compiled in 31.4 seconds
   after normalization. Verdict: pass, with the two declared inherited holes.
3. Checked both smaller statements and their complete docstring arguments, including
   identity arrows, zero complexes, negative degrees, and no unnecessary injectivity
   assumption for the chain-level statement. They are true subarguments of the explicit
   comparison and are each strictly smaller than the item. Searched Mathlib with
   LeanFinder, Loogle, grep, and a recorded unavailable LeanSearch attempt; additionally
   searched the library's Hom-complex and object-cohomology modules. Related results
   concern different sheaf-of-modules or nonnegative resolution comparisons; none
   directly states these equations. Verdict: two valid remaining subproblems.
4. Checked the comparison definition and node plan from the top downward. Kept the
   explicit comparison, used generic functoriality for composition, and inspected
   `dag/units/sk-prop-h2.json` realization lists. No alternate unit route or module
   pruning is asserted. Verdict: route preserved; imports used by signatures or proof.
5. Repaired both new nodes with all required fields, precise statements, verbatim Lean
   signatures, source, written proofs, searches and matching dependencies. Updated the
   existing node to the two-square reduction with proof_deps equal to step uses.
   Verdict: DAG agrees with Lean.

Second reading changed: removed the duplicate core/wrapper decomposition, wrote the
actual reduction from the two smaller naturality statements, added their proof-only
imports, repaired all node metadata, and rewrote the inaccurate report. No statement
or definition change.

Validation: the delivery dry run compiled all four modules in dependency order, ran
the axiom probe and passed preflight. Its review class is CODEX because the delivery
adds two modules with public statements and two nodes. No public import or existing
statement changed. The global ledger and build remain the maintainer’s checks.
