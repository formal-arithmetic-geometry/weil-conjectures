## What changed

Proved `AlgebraicGeometry.tensorHomUncurry_descent_natural` from naturality on images of
actual chain maps. Its signature, public visibility, and existing docstring are unchanged.
Added proof-only imports of `CanonicalTensorHomUncurryChainNaturality` and Mathlib's
`DerivedCategory.Fractions`. The public differential import remains necessary for the
statement. Two proved private helpers implement arrow representation and categorical
transport; neither has a hole. The unit and chapter route is unchanged.

For each arbitrary derived arrow, `derived_arrow_rep` chooses complex representatives
and applies `DerivedCategory.right_fac`, absorbing its denominator into a source
isomorphism. `naturality_transport` proves the functorial input identity, applies the
isomorphism hypothesis twice, uses tensor interchange, and cancels endpoint isomorphisms.
This is a genuine extension argument from chain maps to arbitrary derived arrows.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.tensorHomUncurry_descent_natural`
(node `lem-pc-tensor-hom-uncurry-descent-naturality`). No sorry remains in the assigned module.

Added one hole: `AlgebraicGeometry.tensorHomUncurry_chain_natural`
(node `lem-pc-tensor-hom-uncurry-chain-naturality`), in the new module
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality`.
This restricts the variable maps to actual chain maps and keeps the input derived
morphism arbitrary. The remaining task is the component calculation on resolutions;
the extension from chain maps to arbitrary derived arrows has been completed.
This is a decomposition, with one hole closed and one added (net zero), not an
axiom-free completion of the mathematical naturality theorem.

Edge cases checked against the new statement: identity chain maps reduce to the identity
functor/tensor laws; zero maps and zero complexes satisfy the same component equation;
no boundedness hypothesis occurs. Arbitrary chosen derived-category objects are covered
by endpoint isomorphisms, without assuming that Q is literally surjective on objects.
The categorical transport proof requires no additivity or bijectivity of t.

## No longer needed

No module is globally pruned, and no original import was removed. The following old
proof dependencies are no longer direct proof dependencies of the assigned node:
`lem-pc-tensor-hom-uncurry-differential`, `lem-pc-kflat-resolution`,
`lem-pur-hom-kflat-into-kinjective`, `lem-weil-pbc-kinjective-hom-derived`,
`def-pur-hom-complex`, and `lem-pc-sheaf-modules-tensor-closed`.
All six remain dependencies of the new chain-naturality node; the differential module
also remains the public import required to express the assigned theorem's signature. The assigned
node now directly depends on that node and on the existing Mathlib right-fraction,
calculus-of-fractions, and derived-category nodes. No unit statement or step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original node grouped the component calculation and
roof transport in a single step. Mathlib's `DerivedCategory.right_fac` allows the latter
to be proved entirely categorically, without additional sheaf-specific lemmas.
The first compile failed because the freshly landed differential module was absent
from the shared compiled cache; it arrived during the session, and compilation resumed.
The source TeX files are absent on this machine; the three cited Stacks tags were read
online. LeanSearch returned Internal Server Error; LeanFinder, Loogle, and source grep
were also attempted and recorded in searches.jsonl. The blueprint search found no
existing node for the narrower normalized chain-map naturality statement.

## New nodes

`lem-pc-tensor-hom-uncurry-chain-naturality` states only the naturality calculation for
Q-images of actual chain maps. Its hypotheses are the existing normalization and
isomorphism-transport hypotheses; its source is Stacks 08DJ, 0A90, and 0A96.
Its docstring and DAG proof specify the resolution, component, homotopy, and comparison
steps. It belongs to the original chapter and unit. No statement, definition,
change record, or forced adaptation of another existing module is introduced.

## Second reading by W3

1. Interface: PASS. Compared the entire existing module with the repository using
   diff and checked its existing theorem signature byte for byte by extraction.
   Only proof imports, private proved helpers, and the proof body were added.
   No existing statement, definition, visibility, or docstring changed; no change
   record is required. The other delivered module is new.
2. Proof and axioms: PASS as a decomposition. Both delivered modules compiled locally
   in import order with lcompile.py, without errors or warnings. A scratch copy with
   four #print axioms commands shows only propext, Classical.choice, and Quot.sound
   for derived_arrow_rep and naturality_transport. The two public naturality theorems
   additionally depend on sorryAx, as expected from the explicitly reported remaining
   chain-naturality hole and open upstream statements. There is exactly one textual
   sorry, the whole proof of the new named public theorem. There are no forbidden
   declarations, hidden holes, or new definitions choosing data from unproved existence.
3. Split statement: PASS. Its assumptions are the original assumptions; only variable
   arrows are restricted to images of chain maps, while the input f remains arbitrary.
   This isolates the component/resolution calculation, and the original proof performs
   actual roof representation and categorical transport rather than merely applying a
   renamed copy of itself. Identity variable maps reduce by functor and tensor identity
   laws; zero maps and zero complexes agree with the component calculation. The
   K-injective Hom argument uses K-flat L after replacement, not arbitrary original L.
   Read the natural-language proof and node against Stacks 08DJ, 0A90, and 0A96 online.
   Repeated searches with different wording using LeanFinder, Loogle, msearch grep,
   and rg on both source roots found no matching normalized naturality theorem.
   MonoidalClosed.uncurry_natural_left proves ordinary closed-category uncurrying
   naturality but does not identify this family's representative normalization.
   Closing the remaining component/resolution calculation is not a few-minute task.
4. Route and pruning: PASS after report repair. Fractions.right_fac supplies the
   shortest direct arrow-representation route found. The generic transport helper
   uses only functor composition, tensor composition, and cancellation of isomorphisms.
   The public differential import is needed by both signatures; the chain theorem and
   Fractions imports in the assigned module are proof-only. No import is unused.
   Checked the unit sk-thm-picard-duality and its realized fields: they are unchanged,
   and the original component/resolution route is retained in the new node. Explicitly
   listed all six old direct proof dependencies moved to the new node under No longer
   needed; none is claimed to be globally pruned.
5. DAG: PASS. Compared the existing node with its repository version: only proof,
   proof_deps, and proof_origin changed. Their steps match the chain theorem invocation,
   right-fraction representation, and transport helpers. The new node includes source,
   full statement, proof steps and their dependency union, searches, provenance,
   blueprint ancestry, chapter/unit, split status, and the verbatim Lean statement.

Second reading changed only report.md: completed the direct-dependency pruning account
and recorded this independent review. The Lean proof and node files required no repair.
