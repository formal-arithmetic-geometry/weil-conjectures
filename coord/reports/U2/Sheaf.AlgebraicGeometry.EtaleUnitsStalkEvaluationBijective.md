## What changed

The target proof combines separate injectivity and surjectivity component theorems.
The two components are stated as named intermediate theorems and retain `sorry`, while
`etale_units_stalk_evaluation_bijective` is proved by pairing them. Proof-only imports
of the two component modules were added.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_bijective` (one
of one original holes), by combining the injectivity and surjectivity components.

Added holes:
- `AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_injective`, node
  `lem-sc-etale-units-stalk-evaluation-injective`.
- `AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_surjective`, node
  `lem-sc-etale-units-stalk-evaluation-surjective`.

This is a decomposition: one hole closed, two added, net -1. The target proof
still depends on `sorryAx`; neither component is proved. No hole is inside a
definition and no data is chosen from an unproved existence theorem.

## No longer needed

No imports or modules are pruned. All three original public imports supply names
in the statements; the two new imports are private to the target proof.

The old parent `proof_deps` are no longer direct proof dependencies:
`def-sc-galois-units-cohomology`, `def-sc-gm-torsor`,
`def-weil-pbc-geometric-stalks`, and
`lem-weil-pbc-finite-separable-extension-etale`. All four remain dependencies of
the component nodes (and the definitions also remain parent statement
dependencies), so none is globally discarded. The parent's direct proof
dependencies now name precisely the two components.

## Where the brief, the DAG or earlier work was wrong

The blueprint proof requires substantial finite separable neighbourhood and colimit
arguments not available in the current library. The target was therefore decomposed into
its strict injectivity and surjectivity clauses; the target statement and unit route are
unchanged.

## New nodes

`lem-sc-etale-units-stalk-evaluation-surjective` and
`lem-sc-etale-units-stalk-evaluation-injective` in `dag/nodes/sec-curve-estimates/`, with
modules `Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluationSurjective` and
`Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluationInjective`.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged. The target proof compiles and pairs the two component
results in the order required by `Function.Bijective`. The component statements are strictly
weaker injectivity and surjectivity clauses, each matching its named theorem and node; both
remaining `sorry`s are named public declarations with complete proof descriptions. All three
modules compile in sandbox import order, and the original unit route is preserved.

## Second reading by U2

1. Compared the existing target module with the repository using `diff -u`.
   Its declaration signature is byte for byte unchanged; only two proof-only
   imports and the proof body differ. The components are new declarations,
   each with the same evaluation hypothesis and only its indicated conclusion.
   No existing definition, statement, visibility, or public import is changed.
   No change record is required. Verdict: pass.
2. All three modules compile in local sandbox import order. Separate scratch
   `#print axioms` checks report only `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx` for the target and both components. The two named public
   components are the only remaining holes. No forbidden declaration or hollow
   definition occurs. Verdict: valid reduction, still conditional on two holes.
3. Checked the component arguments against Stacks Example 03QV (2) and the
   original target's proof plan. Expanded both docstrings to complete proofs:
   finite separable neighbourhoods, equality in a common refinement, and
   injectivity of the field embeddings are explicit. Checked algebraically
   closed fields (all finite separable subextensions are the base field), finite
   fields, and imperfect fields (only separable subextensions are used). The
   inverse of a nonzero field element already belongs to K(a). Each clause is
   strictly weaker than bijectivity, and both are needed. Repeated searches with
   different terms through leanfinder, loogle and grep, and searched both local
   library roots: generic filtered-colimit lemmas are available, but neither
   component theorem is. Higher units-stalk equivalences depend on this item and
   cannot shorten the proof without a cycle. Closing either component requires
   formalizing the remaining geometric comparison, beyond a quick repair.
   Verdict: true, strictly partial statements; decomposition, not net progress.
4. The target pairs the two actual clauses in the order Function.Bijective
   requires. Each retained public import supplies signature vocabulary and each
   new proof import supplies one component. No shorter existing comparison was
   found. The four old parent proof dependencies are all listed above and
   retained below the components. Read `dag/units/sk-thm-br.json` and its
   blueprint `_section.md`: the Brauer-injection/Tsen route is unchanged; its
   existing empty realized fields are not bypassed or edited. Verdict: pass,
   no pruning claimed.
5. Repaired both new nodes' natural-language statements, which incorrectly
   claimed bijectivity, to say injectivity and surjectivity respectively.
   Recorded the Lean signatures verbatim and added the repeated search results.
   Added the existing parent node with its proof and proof_deps matching the Lean
   pairing. New nodes retain their source, complete proof steps, statement
   dependencies, creation record, blueprint link, chapter, unit and Lean record.
   Verdict: DAG and Lean agree after repair.

Second reading changed the two component proof docstrings, their node statements,
proof descriptions, verbatim signature records and search records, the parent's
proof dependency record, the report's hole accounting, and excess blank lines.
The Lean proof and all declaration signatures were retained.
