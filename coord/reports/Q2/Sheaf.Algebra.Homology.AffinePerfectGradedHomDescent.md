## What changed

Proved `CochainComplex.affine_perfect_gradedHom_descent` in
`Sheaf.Algebra.Homology.AffinePerfectGradedHomDescent`, without changing its signature.
Replaced the proof import of `Sheaf.Algebra.FinitePresentationColimit` with
`Sheaf.Algebra.Homology.BoundedGradedMapColimitDescent`.
Constructed a zero-differential complex with terms `K₀.X (m - 1)`, applied bounded
component descent, and enlarged the resulting stage above the requested `i`.
The two proved private scalar-extension coherence helpers reuse the argument in
BoundedGradedMapColimitDescent. The final family uses the equality `n = m - 1`
forced by the up-shape relation. Updated the existing node's proof route accordingly.
A declaration-scoped unused-variable linter setting preserves the original unused
existential binder name `hij` without a compiler warning.

## Proved and sorry left

Closed one hole: `CochainComplex.affine_perfect_gradedHom_descent`
(node `lem-pc-affine-perfect-graded-hom-descent`).
No sorry remains in the delivered module, and no new holes were added.
The proof uses the existing bounded graded descent declaration, whose downstream
proof obligations remain separate project items. Both private helpers are proved.
This is a proof from existing project declarations, not a new decomposition.

## No longer needed

Removed direct import `Sheaf.Algebra.FinitePresentationColimit`.
The delivered proof no longer directly uses
`lem-pc-fp-module-map-descent-affine` or
`lem-pc-filtered-colimit-commrings-elementwise`; its sole non-elementary dependency
is `lem-pc-bounded-graded-map-colimit-descent`.
These old dependencies may remain needed elsewhere and indirectly in the bounded
component argument; no claim of global unreachability is made.
No public imports were removed or changed.

## Where the brief, the DAG or earlier work was wrong

The original component-by-component route was valid but duplicated the existing
bounded graded descent machinery. A zero-differential target complex with reindexed
terms allows that machinery to be reused without any differential assumption.
The locally compiled snapshot did not yet contain FinitePresentationMapCanonical,
so the final proof imports the available existing bounded graded descent interface
instead. The proof works with directed preorders as stated, and does not add
antisymmetry, a nonempty interval, or a bound on the target complex.

## Second reading by Q2

1. Compared the sole delivered module with the repository version and checked the
   existing theorem signature byte for byte up to `:= by`: identical. No public
   imports, definitions, or existing visibility changed; no change record is needed.
2. Compiled locally without errors or warnings (7.3 seconds). Scanned the module:
   no sorry, axiom, unsafe, opaque, implemented_by, or extern. A scratch copy's
   `#print axioms` reports propext, Classical.choice, Quot.sound for each private
   helper, and these plus sorryAx for affine_perfect_gradedHom_descent, inherited
   from existing imported obligations. There is no new unproved data construction:
   Q has explicitly zero differentials and w is chosen from a locally proved lift.
3. No statements or holes were split off. Checked the reduction for empty support,
   zero source terms, arbitrary target differentials, and directed preorders without
   antisymmetry. Q keeps precisely the target terms at degree m-1; the relation
   n+1=m uniquely fixes n and proof irrelevance handles relation witnesses.
4. Read bounded component descent and adjacent-family descent, searched the library
   with scalar-extension/coherence terminology, and ran an independent LeanFinder
   search for composition of scalar extension. The Mathlib associativity theorem
   found is already used. GradedScalarExtensionCoherence has a suitable public
   transport theorem in the source, but its object file is absent from the permitted
   compiled snapshot (confirmed by launcher compilation). Retained the correctly
   proved private calculation rather than import an unavailable declaration.
   All public imports serve the unchanged statement; the replacement plain import
   serves the proof. Both original proof dependencies removed from the direct route
   are listed above. The unit sk-thm-picard-semicon's realized arrays are empty; no
   realized unit statement or step is bypassed or edited by this local reduction.
5. Compared the delivered node against the repository node: only proof, proof_deps,
   and proof_origin changed. Its three steps match Q, stage enlargement, and the
   final degree transport. The sole non-elementary project dependency matches the
   bounded descent declaration actually used. No new nodes or statement changes.

Verdict: pass. Second reading added this report and documented the axiom check and
unavailable public coherence shortcut; the verified Lean proof and node are unchanged.
