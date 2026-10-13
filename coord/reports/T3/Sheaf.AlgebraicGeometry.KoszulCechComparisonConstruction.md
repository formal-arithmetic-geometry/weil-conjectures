## What changed

Proved `AlgebraicGeometry.koszulCechHomDiagram_exists` directly in
`Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction`: construct linear precomposition,
use Mathlib `HomComplex.δ_ofHom_comp`, reuse the existing transition laws,
and prove the functor laws. The repair adds the proof-only
`import all Sheaf.AlgebraicGeometry.KoszulOpenSystem` alongside its existing public
import, allowing direct use of the private `koszulOpenTransition_id` and
`koszulOpenTransition_comp` theorems. All four duplicate local helpers
(`koszulCechDiagonal_zero`, `koszulCechDiagonal_comp`, `koszulCechTransition_id`,
and `koszulCechTransition_comp`) are removed.

Reduced `AlgebraicGeometry.koszulCechCocone_exists` to the adjacent differential identity
in the new proof-only import `Sheaf.AlgebraicGeometry.KoszulCechLocalizedDifferential`.
The new module constructs scalar division from Mathlib's proved principal-open
invertibility and constructs the degree maps as actual linear maps. The original
module constructs the chain maps, proves their denominator formula by the inverse law,
proves the ordered-wedge power-transition formula, proves compatibility by scalar
cancellation, and assembles and transports the cocone. This is a reduction to a strictly
smaller differential identity, not an existence statement under another name.

All existing public declarations, signatures, visibility and definitions are unchanged.
The existing node's proof fields now describe the actual Lean route. No forced
adaptations or interface changes are needed. Both modules compile cleanly with
`lcompile.py --all` in import order.

## Proved and sorry left

Closed original holes:

- `AlgebraicGeometry.koszulCechHomDiagram_exists`: proved directly, with no new hole
  needed for the diagram construction.
- `AlgebraicGeometry.koszulCechCocone_exists`: complete Lean proof from the one new
  adjacent differential lemma; counted as a decomposition, not an independent proof
  of the whole localization calculation.

The original module has no `sorry` left. One hole is added:
`AlgebraicGeometry.koszulCechLocalizedDegreeMap_comm`, node
`lem-sc-koszul-cech-localized-differential`, in
`Sheaf.AlgebraicGeometry.KoszulCechLocalizedDifferential`.
Its proof is exactly `by sorry`, with the source and the complete coordinate argument
in its docstring. There are no holes in any definition or private helper.
Net for this delivery: two original holes closed, one smaller hole added.
Existing holes in dependencies, such as the principal Čech construction, remain
outside this delivery; no claim of an axiom-free target proof is made.

## No longer needed

Pruned the four duplicate private helpers listed above. No modules or DAG nodes
are pruned and no import is removed. All four original public imports are required by the original signatures and
definitions. There were no proof-dependency imports to remove and the original node
had no proof dependencies to prune. No unit realization is bypassed: the unit's
`realized.statement` and `realized.steps` lists are empty for this construction.
The older additive `AffineKoszulHomAlternatingCech` statement supplies neither the
specified sheaf-valued fraction formula nor the differential identity and is not
imported. No downstream isomorphism, stage lifting or stage kernel theorem is imported.

## Where the brief, the DAG or earlier work was wrong

The construction node is a definition node with an empty `proof` and `proof_deps`,
rather than a numbered proof plan with dependency theorems. The two existing docstrings
provide the construction plan; the new node makes its remaining differential calculation
an explicit work item. The scalar division and degree-map data are now genuine
constructions using proved Mathlib invertibility.

The returned delivery duplicated four lemmas already proved privately in
`KoszulOpenSystem`. The earlier claim that they could not be reused was wrong:
Lean's proof-only `import all` makes them available. The repaired proof directly
rewrites with the existing transition identity and composition theorems, and
removes both local transition lemmas and their two diagonal helpers.
No other module is adapted and no existing public signature or visibility changes.

Source checked: [Stacks 08D0](https://stacks.math.columbia.edu/tag/08D0) for fraction
maps and power transitions, and [Stacks 08D1](https://stacks.math.columbia.edu/tag/08D1)
for the totalization sign. Edge cases: r=0 yields no nonempty coordinates; singleton
subsets have no incoming horizontal term; zero or nilpotent products have empty
principal opens; no quasi-coherence or boundedness assumption is introduced.
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable.
LeanFinder found `δ_v` and other component tools, and Loogle found the exterior-map
formula; no service supplied the whole localized differential identity.

## New nodes

`lem-sc-koszul-cech-localized-differential` states only commutation with the adjacent
differential for a fixed exponent and explicitly constructed degree maps. It contains
no diagram, no colimit, no cocone and no compatibility between exponents. The vector
parameter is pinned to the existing increasing wedge by equality, avoiding a duplicate
basis definition. Its source is Stacks 08D0–08D1, and the searches are recorded in
`searches.jsonl`. The proof explains both differential summands, denominator cancellation,
ordered deletion positions, sign identities, and the empty and singleton cases.
There are no change records because no existing interface is changed.


## Second reading by T3

1. Compared the entire existing module with the repository using `diff -u`.
   Verdict: every existing declaration signature, visibility, definition body and
   docstring is unchanged. Only proofs, two proof-only imports, private helpers and
   a local elaborator option were added. No interface change record is required.
2. Recompiled both delivered modules locally in import order: clean, 6.9 and 8.2
   seconds. Compiled scratch copies with `#print axioms` for every public theorem
   and definition. The diagram theorem and all new constructed data use only
   `propext`, `Classical.choice`, `Quot.sound`; the cocone and comparisons also use
   the reported `sorryAx`. Exactly one source `sorry` remains, the public named
   `koszulCechLocalizedDegreeMap_comm`; no forbidden declaration or hollow data.
   Verdict: one direct proof and one genuine decomposition, net one hole closed.
3. Read the new differential theorem, its complete docstring proof, its node, the
   actual negative Koszul-tail differential, Mathlib `HomComplex.δ_v`, and the
   explicit `principalCechDifferentialValue`. Checked the two summands separately:
   writing S(p,n)=p*(n-p)+p*(p-1)/2, the vertical exponent difference is p and,
   for p≥1, S(p,n+1)+n-S(p-1,n)=2*n. Thus the deletion coefficients agree with
   the horizontal alternating signs. The p=0 row has no deletion term; r=0 has
   no components; empty principal opens cause no invertibility exception.
   Scalar division uses Mathlib's proved invertibility, not a chosen unproved
   witness. Verdict: true, strictly smaller, and sufficient without additional
   hypotheses. Repeated LeanFinder and Loogle searches with different queries
   (recorded in searches.jsonl), and searched the library using `rg`. Read
   `AffineKoszulHomAlternatingCech`: its existential target does not specify the
   differential or fraction map and cannot discharge this identity. No duplicate
   or short whole proof found. Checked source Tags [08D0](https://stacks.math.columbia.edu/tag/08D0)
   and [08D1](https://stacks.math.columbia.edu/tag/08D1); the concrete signs above
   were checked against Lean's definitions rather than inferred from conventions.
4. Read the proof from both original holes downward. Precomposition directly uses
   Mathlib and the existing private transition laws via proof-only `import all`;
   the cocone explicitly proves its denominator formula, wedge transitions,
   exponent compatibility and transport naturality. No renamed existence hole.
   All imports serve existing interfaces or these proofs. Original proof_deps
   was empty, so there are no old dependencies omitted from No longer needed.
   The unit sk-thm-picard-duality has empty realized statement/step lists and no
   realization is bypassed. Verdict: pruning and route checks pass.
5. Compared the existing node diff and read the new node in full. Only allowed
   proof fields changed in the existing node; the new node has the matching Lean
   signature, source, proof, searches, origin, creation, blueprint, chapter/unit
   and Lean records. Its proof dependencies match the constructions used.
   Verdict: DAG and Lean agree.

Changes by this second reading: appended this independent review and recorded
additional search evidence. No Lean proof repair or additional split was needed.
The remaining coordinate differential proof is substantial and was left explicitly
as the one reported work item.
