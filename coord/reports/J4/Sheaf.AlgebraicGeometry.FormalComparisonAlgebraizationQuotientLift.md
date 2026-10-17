## What changed

Proved `AlgebraicGeometry.formalComparison_algebraization_quotient_lift` with its
existing signature unchanged. The proof constructs the coherent algebraization
from `coherentFormalModules_affine`, completeness, and the tilde construction;
then lifts the formal isomorphism through fully faithful proper completion and
checks its actual quotient projections.

The second reading removed the copied quotient-comparison namespace and the
inlined duplicate coherence/projection arguments. It instead imports
`WeilConjectures.AlgebraicGeometry.FormalSystemsPullback` with proof-only
`import all`, using the existing `completionPullbackIso`, `powerQuotientIso`,
`powerQuotientIso_π`, and `coherent_pullback` directly. This addresses the earlier
duplicate-declaration return by reusing its named existing proofs. The main
algebraization argument is retained.

Removed the redundant public Mathlib tilde import and redundant private
adic-completion algebra import. Added the proof-only upstream tilde import for
its module APIs. The public import removal is recorded in
`coord/changes/J4-quotient-lift-tilde-proof-import.md`. No other module is adapted.
Updated the item's DAG proof and proof origin to describe the actual Lean route.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.formalComparison_algebraization_quotient_lift`
(node `lem-weil-pbc-formal-comparison-algebraization-quotient-lift`).
Added 0 holes; 0 split off. No `sorry` remains in the delivered module and no
new module or node is added. A scratch copy's `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed direct imports `Mathlib.AlgebraicGeometry.Modules.Tilde` and
`Mathlib.RingTheory.AdicCompletion.Algebra`: they are already supplied by
proof dependencies, and no statement needs the tilde API. Replaced
`import all Sheaf.AlgebraicGeometry.FormalSystemsPullback` (a compatibility
re-export) with `import all WeilConjectures.AlgebraicGeometry.FormalSystemsPullback`
to access the actual existing private canonical-comparison declarations.

Relative to the first worker's sandbox, removed direct imports
`Sheaf.AlgebraicGeometry.ModulePullbackIdealPowerProductImage` and
`Sheaf.AlgebraicGeometry.ModulePullbackFiniteType`, all four copied private
quotient-comparison declarations, and the local duplicate arguments. The
upstream formal-systems module supplies these results instead.

No old `proof_deps` node is pruned: all six remain used, including
`lem-weil-pbc-formal-systems-pullback`. No claim is made that a module has become
unreachable from the targets. The earlier sandbox's proposed pruning of that
node is withdrawn; its needed canonical comparison is reused directly.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery was returned for duplicate coherence and quotient-map
helper statements. The first repair inlined those facts but retained a copied
canonical quotient-comparison construction. The second reading verified that
`import all` of the upstream implementation exposes the existing private
helpers; the wrapper import did not name their defining module. Reusing them
eliminates the duplication and keeps the original dependency route.

No target statement, existing declaration signature, definition, or unit route
has changed. The original DAG plan was mathematically sound; its implementation
now cites the precise existing comparison and lifting operations.

## Second reading by J4

1. Compared the delivered file with the repository using `diff` and checked the
   existing theorem signature byte for byte through `:= by`: identical. The only
   existing public-interface edit is removal of the redundant tilde import, with
   its change record. The sole direct consumer,
   `Sheaf.AlgebraicGeometry.FormalComparisonCompleteBaseAlgebraization`, already
   publicly imports tilde. Compiled that unchanged consumer against the repaired
   item in a scratch overlay. Verdict: no accidental statement or definition
   change and no forced adaptation.
2. Compiled the delivered module without errors or warnings. Scanned for `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and `sorryAx`: none.
   Compiled a fresh scratch copy with `#print axioms` for the main theorem:
   exactly `propext`, `Classical.choice`, `Quot.sound`. There are no new definitions
   or data selected from unproved existence. The affine equivalence has limit
   cones determining its module up to isomorphism; the tilde object is constructed
   explicitly, and `preimageIso` lifts the specified isomorphism uniquely.
   Verdict: complete proof with the permitted axioms.
3. No statement is split off and no new theorem or node is introduced. Checked
   the existing helpers in the upstream formal-systems source rather than
   reproducing them. The quotient comparison is its canonical cokernel
   comparison and its projection identity, not an arbitrary isomorphism. The
   construction handles `n = 0` (positive level 1), the zero module, the zero ring,
   and the zero ideal without additional hypotheses or cancellations of elements.
   Verdict: no new holes, hidden weakening, or duplicate statement.
4. Read Stacks `coherent.tex`, labels `lemma-inverse-systems-affine` (087W),
   `lemma-inverse-systems-pullback` (0887), `lemma-fully-faithful` (0883), and the
   final complete-base paragraph of `lemma-inverse-systems-push-pull` (088B).
   Noetherian completeness gives finite coherent A₀ by affine algebraization;
   properness supplies Noetherian Z and full faithfulness for its completion.
   The formal isomorphism is the canonical pullback comparison followed by
   pullback of e inverse and β. Evaluating the completion of b and applying
   `cokernel.π_desc` proves the exact displayed projection equation. Searched
   upstream and Sheaf sources for quotient/pullback and completion comparison
   APIs; replaced the copied construction with the existing helpers. Imports
   are restricted to statement needs and directly used proof dependencies.
   Read `dag/units/sk-thm-p1.json`, including `realized`: none of its statement or
   step nodes is bypassed; this remains the complete-base subargument of 088B.
   Verdict: original route preserved, shorter implementation, pruning list complete.
5. Compared the sandbox node with the repository node: only `proof` and
   `proof_origin` differ. The six original `proof_deps` are unchanged and equal
   the union of the proof steps' `uses`. Step 1 records affine algebraization and
   coherence; step 2 records the reused formal pullback comparison and proper
   completion; step 3 records evaluation and the quotient-map equation. No new
   node needs a source/search/Lean record. Verdict: DAG agrees with the final code.

Second-reading changes: replaced all copied quotient comparison helpers and the
inlined duplicates with existing upstream helpers; removed redundant tilde and
lower-level pullback imports; restored the formal-systems proof dependency;
updated the proof description, import-change record, and this report. The main
theorem's signature and mathematical argument remain unchanged.
