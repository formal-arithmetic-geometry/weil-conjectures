## What changed

Added `Sheaf.RingTheory.PolynomialGRingRegularComparison` with the strictly lower-level
comparison construction as a named theorem with `sorry`. Completed
`exists_polynomial_flat_local_regular_completion_comparison` by applying that construction,
the complete-local polynomial formal-fibre theorem, Noetherian fibre theorem, and regular
composition. Updated the item's proof and proof dependencies to match the route.

## Proved and sorry left

Closed the item's one hole in `exists_polynomial_flat_local_regular_completion_comparison`
by a complete Lean proof from named statements. Added one lower hole: this is a
decomposition, with net zero holes, rather than a sorry-free proof of the construction.
The new lower-level theorem `exists_polynomial_regular_local_comparison` remains a named
`sorry`, with node `lem-weil-pbc-polynomial-g-ring-regular-comparison`.

## No longer needed

The item's proof no longer directly imports or depends on `RegularBaseChange`,
`LocalizationRegular`, or `RegularThroughLocalization`; those are encapsulated by the new
lower-level comparison theorem. The old proof dependency `def-weil-pbc-g-ring` is also no longer used directly by
the proof, although it remains a statement dependency and the new construction uses it.
These are removals from the item's direct dependency list, not claims that their modules
leave the target import closure. No module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan did not provide a single Lean statement for the lengthy
construction of the comparison localization. That construction was split into the new
strictly smaller node above; the remaining composition is fully checked by Lean.

## New nodes

`lem-weil-pbc-polynomial-g-ring-regular-comparison`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-polynomial-g-ring-regular-comparison.json`,
states only the bottom map of the square. It does not assert any regularity after
completion. The source was read in the available local copy of More on Algebra,
label `proposition-finite-type-over-G-ring`, lines 12552–12605. The remaining proof
uses `Polynomial.completeLocalFormalFibres` to obtain the right vertical map and
`RingHom.IsRegular.comp_of_fiber_noetherian` to compose them. The new statement was
checked for the zero ring (no maximal ideal Q, hence vacuous), fields (S can be the
field, with its zero-adic completeness), and a contraction p that is not maximal in
R (localizing at p is necessary and retained). No target or existing signature changes.
The unit's realized nodes are retained. No change records are needed.


## Second reading by X2

1. Compared every delivered module with the repository. The existing declaration's
   signature is byte for byte unchanged; only its proof and plain proof imports changed.
   The other module is new. No definitions or target statements changed, so no change
   record is required. Verdict: pass.
2. Both modules compile with the launcher in import order, without errors or warnings.
   The item has no remaining sorry. The only added sorry is the named
   `exists_polynomial_regular_local_comparison`, with its node and sourced proof docstring.
   No forbidden declarations or hollow definitions occur. Explicit axiom checks on both
   declarations show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The composition uses genuine declared regularity results, not a renamed copy of the
   original conclusion. Verdict: pass as a decomposition, with net zero holes.
3. Read the source proof at `/home/ubuntu/c1-stacks-review/more-algebra.tex`,
   lines 12552–12605. The new theorem constructs the bottom regular local map and omits
   regularity after completion, which the item's proof obtains separately. It is true
   and strictly a part of the argument. Zero rings are vacuous; for fields the completion
   is the field and the comparison can be the identity. For a nonmaximal contraction p,
   coefficient localization is essential and is retained. Fresh leanfinder, loogle, and
   grep searches, together with rg of Sheaf and the upstream root, found no duplicate.
   The maximal-ideal G-ring comparison needs regular completion maps for the polynomial
   ring itself, precisely what this route is establishing, so it is no shortcut.
   Verdict: pass; the remaining construction cannot be closed in a few minutes.
4. Read downward from the item through its four composition/Noetherian dependencies
   and the split theorem's localization/base-change route. Public imports serve the
   signatures; the item's additional imports serve its proof. All old direct proof
   dependencies absent from the new proof are now listed under No longer needed.
   This does not claim target-closure pruning. The `sk-thm-p1` realized statement and
   steps are unchanged and none is bypassed by this below-unit decomposition.
   Verdict: pass.
5. Checked both node statements against Lean, proof step uses against proof_deps,
   sources and proof_origin, and all required new-node fields. The new node records
   the construction while the item records formal-fibre regularity and composition.
   The existing node's lean statement is semantically unchanged (JSON escaping only).
   Verdict: pass.

Changes in this reading: clarified why coefficient localization preserves maximality,
why the completed coefficient ring is complete at its own maximal ideal, and the
successive-localization identification in the new theorem's docstring; clarified the
same completeness step in its node; added independent search records; completed and
qualified the direct-dependency removal report. No Lean proof or signature needed repair.
