## What changed

Replaced the sorry in `CochainComplex.exists_bounded_graded_map_of_directed_colimit` with a complete
Lean proof assembling single-module-map lifts at one common stage. The existing statement,
visibility, public imports, and docstring are unchanged.

Added `Sheaf.Algebra.FinitePresentationMapCanonical`, stating the missing single-map preorder
descent interface with canonical comparisons at one stage. The original proof-only import of
`Sheaf.Algebra.FinitePresentationColimit` is replaced by this module. Added proof-only imports
`Mathlib.Data.Int.Interval` and `Mathlib.Data.Finset.Order` for the finite interval and its directed
upper bound.

The assembly compares the complex and module isomorphisms degreewise using
`HomologicalComplex.eqToHom_f` and the component formulas for `NatIso.mapHomologicalComplex`. It
inserts i₀ into the finite set of stage indices, chooses an upper bound by `Finset.exists_le`, and
transports a lift for each degree in the interval. The private proved helper `ModuleCat.transport`
evaluates `extendScalars_assoc`, takes inverses, and applies naturality. The private proved helper
`ModuleCat.transportComparisons` incorporates the ring and cocone equalities by equality transport.
Both helpers have complete proofs and preserve every existing signature. Outside the interval it
selects zero and proves the required equality by `Functor.map_isZero` and `IsZero.eq_of_src`. This
handles b<a without a separate lemma.

Both modules compile locally without warnings using lcompile.py. The new lemma was checked against
zero source, zero target, zero rings, zero generators/relations, non-injective ring transitions, and
distinct mutually comparable preorder indices. Its argument uses finite presentations and finite
coefficient equations, so none of these cases requires an additional hypothesis. This is a
decomposition, not a claim that the remaining algebraic lifting problem has been proved.

## Proved and sorry left

Closed the item's one original hole: `CochainComplex.exists_bounded_graded_map_of_directed_colimit`
(node `lem-pc-bounded-graded-map-colimit-descent`). There is no sorry in the item now.

Added one hole: `ModuleCat.finitePresentation_map_directedColimit` (node `lem-pc-fp-module-map-
canonical-preorder`), in `Sheaf.Algebra.FinitePresentationMapCanonical`. Its proof is exactly `by
sorry`; its docstring and node carry the finite-presentation coefficient proof.

This is one upper hole closed and one strictly smaller single-map hole split off, with a fully
checked finite-family assembly. No definition or private helper has a hole. No signatures of
existing declarations changed.

## No longer needed

Removed the proof import `Sheaf.Algebra.FinitePresentationColimit`. The bundled object/map/equality
descent theorem `ModuleCat.finitePresentation_descent_directedColimit` and its node `lem-pc-fp-
module-map-descent-affine` are no longer dependencies of this proof. The object and equality clauses
were never needed for this graded-map existence item. Other library users may still need that
module; this is pruning of this proof route, not a claim that the entire library no longer reaches
it.

The parent node no longer directly depends on `lem-pc-filtered-colimit-commrings-elementwise`; that
Mathlib leaf remains a planned dependency of the new single-map node. The new node also uses the
existing Mathlib leaves `lem-weil-pbc-tensor-right-exact` and `lem-weil-pbc-tensor-finite-product`.
No other imports, nodes, or modules have been pruned.

## Where the brief, the DAG or earlier work was wrong

The previously imported finite-presentation descent declaration requires `PartialOrder I`, whereas
this item has only `Preorder I`. Its chosen comparison isomorphisms are characterized on pure
tensors, whereas this item requires the specific canonical complex scalar-extension comparisons.
Consequently it is not a directly applicable single-map interface under the item's unchanged
hypotheses. The new theorem isolates this algebraic/interface gap, instead of assuming antisymmetry
or changing the item. Extension of a lift to later stages is proved completely in the private
helpers, rather than included in the remaining hole.

Read Stacks Tags 05N7 (2) and 09RE, affine case (1), online. The complete coefficient argument in
the new node/docstring spells out the preorder version: lift generator images and relation
witnesses, make finitely many coefficient equations true at a stage, and use the canonical pure-
tensor comparison. Searches of Mathlib and both library roots found no exact matching interface.
LeanSearch returned an internal server error; this is recorded as unavailable, not as a negative
search result.

The unit `sk-thm-picard-semicon` has empty `realized` arrays in its record. No unit statement or
unit step is bypassed: this remains the bounded finite-degree map descent step of Tag 09RE. No unit
or chapter record changed. The local blueprint source files named in the unit are absent; the unit
record and Stacks sources were read instead.

## New nodes

`lem-pc-fp-module-map-canonical-preorder` is one map between two finitely presented modules over one
initial ring, with one stage admitting a canonical lift. It contains no complexes, interval, zero-
outside-interval hypothesis, simultaneous family, or chain equations. It is strictly a part of the
original finite-family argument, whose nontrivial assembly is now proved in Lean. Later-stage
compatibility is proved in the item. Its source is Algebra Tag 05N7 (2), used in Perfect Tag 09RE,
affine case (1). Its node is in `dag/nodes/sec-picard-framework/lem-pc-fp-module-map-canonical-
preorder.json` and its module is `lean/Sheaf/Algebra/FinitePresentationMapCanonical.lean`.

Updated the parent's proof, proof_deps, and proof_origin to match the Lean proof. No
statement/definition changes, forced adaptations, or change records are needed.

## Second reading by W3

1. **Statements and accidental changes.** Compared the delivered bounded-map module and its
repository version. The existing theorem signature is byte-for-byte unchanged; the only changes
are proof text, proof-only imports, and the recorded proof route. The new
`ModuleCat.finitePresentation_map_directedColimit` statement is a separate, narrower map-lifting
interface and does not alter an existing declaration.

2. **Proof and trust basis.** Compiled both sandbox modules with `lcompile.py --all`; compilation
is clean. The bounded-map theorem has only the permitted `sorryAx` from the explicitly split-off
single-map theorem. The private transport helpers have only `propext`, `Classical.choice`, and
`Quot.sound`; there are no axioms, unsafe/opaque declarations, or sorry in definitions.

3. **Split statement.** Checked the new theorem against Stacks Tag 05N7, including zero modules,
zero maps, empty intervals, and preorders with distinct mutually comparable indices. Its hypotheses
and conclusion describe one map between two finitely presented modules at one stage, strictly less
than the original bounded family, and its docstring gives the finite-presentation coefficient proof.
The matching DAG node records the source, proof plan, declaration, and split status. Searches found
no existing library or Mathlib declaration with this interface.

4. **Pruning and route.** The proof uses the new single-map theorem, finite interval/Finset
utilities, and the two local transport helpers. The old `Sheaf.Algebra.FinitePresentationColimit`
import and its bundled object/equality descent theorem are unused and removed from this module.
The common-stage finite-family assembly remains explicit, and no unit statement or step is bypassed;
the unit record's realized arrays were already empty.

5. **DAG agreement.** Updated only the bounded-map node's `proof`, `proof_deps`, and
`proof_origin`; these match the Lean proof. The new node's Lean record matches its module and
verbatim theorem signature. No statement-change or adaptation record is needed.

I changed the report only by adding this second-reading record; no Lean declarations or statements
were changed during review.
