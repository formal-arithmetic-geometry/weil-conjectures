## What changed

`Sheaf.AlgebraicGeometry.AmpleProjCanonicalMap` keeps its theorem signature and public
imports. Its proof now obtains a morphism with the homogeneous fraction formulas, proves
the inverse-image equality by set extensionality and pointwise detection, and pairs the
two clauses. The parent DAG node records this route.

Two new modules carry the unfinished parts of the original argument:
`AmpleProjChartFormula` constructs a morphism with the algebraic fraction identities;
`AmpleProjPreimage` detects basic-open membership for any such morphism at a single point
outside the base locus. The latter needs only a section covering that point, not a global
cover. Both have full proof descriptions and matching nodes. No definitions or existing
statements changed; no adaptations are needed.

Mathlib searches found `Proj.fromOfGlobalSections`, which requires a ring map from the
entire graded ring to global functions. It cannot directly evaluate sections of a
nontrivial invertible module. The projective-space construction in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible` handles coordinates of
one common tensor degree, not the arbitrary graded section ring. The affine-morphism
and scheme-gluing DAG dependencies are already Mathlib results; nonvanishing
trivialization is available and proved. The missing glue includes tensor-power quotient
ring maps for unequal degrees and their relation to the ring's direct-sum multiplication.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_sectionRing_proj_morphism`
(node `lem-sc-ample-proj-canonical-map`). Its proof has no direct holes and compiles from
the two named intermediate results. This is a decomposition, not an unconditional proof:
one hole closed, two holes added, net minus one.

Added holes, each the whole proof of a public theorem:

- `AlgebraicGeometry.Scheme.Modules.exists_sectionRing_proj_chart_formula`
  (`lem-sc-ample-proj-canonical-map-chart-formula`): the quotient-map construction,
  overlap compatibility, gluing, and the algebraic chart formula.
- `AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen`
  (`lem-sc-ample-proj-canonical-map-preimage`): pointwise detection from the fraction
  identities, with no global covering assumption.

No other holes occur in the delivered modules. All three modules compile together with
`lcompile.py --all`. Empty schemes, zero sections, positive unequal degrees, empty chart
inverse images, and n = 0 were checked against the proof descriptions. The pointwise
lemma uses positive powers in one-dimensional fibres and local stalk homomorphisms; it
does not incorrectly infer a functions-map formula merely from inverse images.

## No longer needed

Removed the direct proof import `Sheaf.Paper.NonvanishingSectionTrivializes` from the
parent module. It remains needed and imported by `AmpleProjChartFormula`, so this does
not prune that module from the target closure.

The original proof dependencies `lem-weil-pbc-nonvanishing-section-trivializes`,
`lem-weil-pbc-morphism-into-affine-scheme`, `def-pc-proj`, and
`lem-weil-pbc-scheme-morphism-gluing` remain needed through the new construction nodes.
No DAG branch or module is claimed globally pruned. The original public imports all
remain necessary for the unchanged signature.

## Where the brief, the DAG or earlier work was wrong

No mathematical fault was found in the original statement or four-step DAG plan.
The new nodes separate its construction/formula from its pointwise verification.
The original unit `sk-thm-curveestimate` and its realized statement remain unchanged.

LeanSearch returned an Internal Server Error on both natural-language searches; this is
recorded as unavailable, not as evidence of no match. LeanFinder, Loogle, source grep,
and blueprint search were performed. The repository lacks the cited Stacks TeX files,
so Tags 01N8 and 01PZ were read on the official Stacks Project website.

## New nodes

`lem-sc-ample-proj-canonical-map-chart-formula`, in
`dag/nodes/sec-curve-estimates/`, carries
`Sheaf.AlgebraicGeometry.AmpleProjChartFormula`. It is the construction and fraction
formula component of the parent's argument; it omits the inverse-image equality.

`lem-sc-ample-proj-canonical-map-preimage`, in the same directory, carries
`Sheaf.AlgebraicGeometry.AmpleProjPreimage`. It states a pointwise equivalence for a
fixed morphism satisfying fraction identities, at a point with a covering section.
It neither constructs a morphism nor proves the fraction identities. No change records
are required because all existing interfaces stay identical.

## Second reading by M2

1. **Statements and interfaces.** Compared each delivered module with the repository version. The existing canonical-map theorem signature and its public imports are unchanged; the two added theorem statements match their DAG nodes and introduce no altered existing interface. Verdict: pass.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; they compile without errors. The parent theorem has no `sorry`; the only remaining `sorry`s are the two named split-off public theorems, each documented and represented by a node. Verdict: pass subject to the declared decomposition.

3. **New statements.** Checked the chart-formula theorem as the construction/formula component and the preimage theorem as its pointwise detection component. Both are strictly simpler than the parent, retain the needed hypotheses, and cover edge cases described in their docstrings. No duplicate library declarations were found in the searches recorded above. Verdict: pass.

4. **Pruning and route.** The parent proof uses both split-off results; the removed direct import of `Sheaf.Paper.NonvanishingSectionTrivializes` is no longer needed there and remains used by the chart-formula module. The unit route and all required construction dependencies remain represented in the DAG. Verdict: pass.

5. **DAG and report consistency.** The parent and two new node records agree with the Lean declarations, proof dependencies, and decomposition route. The report records the holes closed, holes added, and no longer needed import. Verdict: pass.

Changed during second reading: added this review section only; no Lean statements, definitions, or proofs were changed.
