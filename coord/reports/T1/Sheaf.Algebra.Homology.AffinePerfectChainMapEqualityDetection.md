## What changed

Replaced the proof of `CochainComplex.affine_perfect_chainMap_equality_detection`
with componentwise equality descent at a common initial stage, finite-set induction,
zero-source extensionality outside the support, and scalar-extension associativity.
The existing public theorem signature, visibility, and public imports are unchanged.
Added only proved private helpers for the associativity calculation, preservation of
finite presentation, upward propagation, and finite aggregation. The associativity
and propagation proofs follow the private calculations in
`GradedScalarExtensionCoherence` and `FiniteChainSquaresColimitDescent`; their private
visibility prevents importing these helpers, and the new composition helper also
handles arbitrary final rings rather than only the colimit.

Replaced the proof-only import of `Sheaf.Algebra.FinitePresentationColimit` with
`Sheaf.Algebra.Homology.PreorderModuleMapEqualityDescent` and added the proof-only
interval import `Mathlib.Data.Int.Interval`. Updated the existing node's proof and
proof dependencies to record this route. No new modules, statements, or nodes.

Read the sources online because this clone has no Stacks source files:
[Tag 05N7](https://stacks.math.columbia.edu/tag/05N7), clause (3), and
[Tag 09RE](https://stacks.math.columbia.edu/tag/09RE), affine case (1).
LeanFinder returned fixed-ring module-colimit and ring-map results, Loogle found
`ModuleCat.extendScalars_assoc` and the composition comparisons, and the logged
grep confirmed those Mathlib lemmas. Local library search found the existing
preorder equality descent theorem.

## Proved and sorry left

Closed the one original hole with a locally compiled proof:
`CochainComplex.affine_perfect_chainMap_equality_detection`
(node `lem-pc-affine-perfect-chain-map-equality-detection`). The proof compiles in the
sandbox and passes the stage-3 dry run. No holes added or split off; no `sorry`
remains in the delivered source. This is a proof from existing
statements, not a new decomposition. Its import closure still uses the existing
finite-presentation descent theory; no claim is made that the target closure is
axiom-free.

The scalar-extension helpers and complete aggregation argument compile against
the existing preorder equality descent theorem; the placeholder used during
initial exploration has been removed.

## No longer needed

Removed the direct proof-only import `Sheaf.Algebra.FinitePresentationColimit`.
Its node `lem-pc-fp-module-map-descent-affine` remains transitively needed through
`lem-pc-preorder-module-map-equality-descent`; it is not a globally pruned module.
The direct proof dependency `lem-pc-filtered-colimit-commrings-elementwise` is no
longer needed by this module's argument. Elementwise colimit theory remains below
the existing finite-presentation descent dependencies. No global pruning claimed.
Neither `GradedScalarExtensionCoherence` nor `FiniteChainSquaresColimitDescent` is
imported: their public theorems are not used. No unit statement or step is bypassed;
this item's unit has no populated `realized` statement or step entries.

## Where the brief, the DAG or earlier work was wrong

The planned finite-presentation theorem requires a partial order, whereas this
item permits preorders. The already-stated and already-proved
`ModuleCat.eventually_equal_maps_of_directed_preorder_colimit` supplies precisely
this interface, so no new statement or changed hypothesis is needed.

The source includes the preorder equality descent dependency. Its object was
absent from the shared build during earlier retries, so those attempts stopped
before proof checking. The dependency source is unchanged from the project
library; after compiling that existing dependency, the retained proof compiled
cleanly and the mandatory dry run completed successfully on 2026-10-13:
`deliver3.py T1 Sheaf.Algebra.Homology.AffinePerfectChainMapEqualityDetection --no-push`
printed `OK (dry run)`. No dependency declaration or signature was changed, and
nothing was pushed.


## Second reading by T1

1. PASS. Compared the complete delivered module with the repository using `diff`;
   independently checked that the original public theorem signature is byte for byte
   identical. No definitions, public imports, visibility, or target statements changed.
   Only private proved helpers, the main proof, and proof-only imports changed.
2. PASS. Compiled the delivered module using `lcompile.py` (7.0 seconds, no warnings).
   Compiled a scratch copy with `#print axioms` for all five private helpers and the
   main theorem. Helpers use only `propext`, `Classical.choice`, and `Quot.sound`;
   the main theorem additionally uses existing dependency `sorryAx`. No forbidden
   declarations, data choices from unproved existence statements, or source `sorry`
   occur in the delivered module. A probe without the sandbox overlay confirmed that
   the shared cache lacks `PreorderModuleMapEqualityDescent.olean`; the successful
   checks use the existing sandbox compilation of that unchanged library dependency,
   as the first worker reported. No dependency source is included in this delivery.
3. PASS. No statements were split off, and no new public statements or nodes were
   added. Read all private helper proofs and the existing preorder equality theorem.
   Finite-set induction handles the empty interval (including a > b), zero source
   terms, and repeated or mutually comparable indices without antisymmetry.
   Scalar-extension composition is proved from Mathlib associativity and naturality;
   no arbitrary witness is used to define data.
4. PASS. Read the proof from the main theorem downward and searched the library for
   scalar-extension composition/coherence and finite aggregation alternatives.
   Existing matching calculations are private; no public theorem supplies a shorter
   complete chain-map equality argument. The existing preorder equality theorem is
   used directly. Imports supply the displayed statement or the actual proof;
   the two removed old direct proof dependencies are accounted for under
   `No longer needed` (finite-presentation descent remains transitively required).
   Checked `dag/units/sk-thm-picard-semicon.json`: its realized statement and step
   entries are empty, and the proof bypasses no realized unit step.
5. PASS. Compared the old and delivered node JSON. Only `proof`, `proof_deps`,
   and `proof_origin` changed. Their steps match common-stage transport, the existing
   preorder component-equality descent theorem, finite aggregation, zero-source
   extensionality, and the final associativity identifications in Lean. The node's
   statement, Lean signature, source, chapter, and unit remain unchanged.

Second reading changed only this report: removed the stale “full compile pending”
qualification and recorded the five review verdicts and explicit axiom checks.
No repair to the Lean proof or DAG was necessary. Closed hole:
`CochainComplex.affine_perfect_chainMap_equality_detection`; added holes: none.
