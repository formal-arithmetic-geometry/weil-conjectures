## What changed

Proved `AlgebraicGeometry.Scheme.GaloisCover.exists_connected_subgroup_quotient` in
`Sheaf.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient`, with its original signature.
Added one proof-only import, `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`.
The source library already constructs finite etale quotient cocones and identifies their
geometric fibres with orbit sets. Restrict the action to H, use that quotient, prove the
restricted action is simply transitive, and construct cH with exactly the same total space.
Connectedness follows from the surjective quotient map. The fibre count follows by proving
that a finite G-torsor has |G| points in each separably closed geometric fibre, counting
fibres in a tower, and cancelling |H| using `Subgroup.index_mul_card`.

Four private helpers are completely proved: `torsor_action_injective`,
`singleObj_orbit_eqvGen`, `torsor_card_geometricFiber`, and `card_geometricFiber_comp`.
The DAG copy records this route and its two used dependency nodes.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.GaloisCover.exists_connected_subgroup_quotient`
(node `lem-weil-pbc-connected-torsor-subgroup-quotient`): 1 of 1 original sorries removed.
No sorry remains in the item, and no new sorry or module is introduced.
Local and server single-file compilation pass without warnings. `#print axioms` reports
only `propext`, `Classical.choice`, and `Quot.sound`. The required `deliver3.py --no-push`
dry run prints OK: the preflight passes except for the intentionally pending second reading.
Nothing was pushed.

## No longer needed

The former proof dependencies `thm-galois-fundamental` and `thm-galois-lc-etale`, namely
`Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence` and
`Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`, are not needed
by this theorem. The current repository version imports both as proof dependencies; this delivery removes
both proof-only imports.
Their FLC sheaf comparison, fundamental-group topology, monodromy surjectivity, and
comparison of different geometric fibre functors are bypassed below the unit level.
`lem-galois-geometric-fibre` remains needed for lifting a separably closed point.
The three public imports serve the unchanged statement and are preserved. The redundant
proof-only import `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` is also removed;
Basic already imports it publicly. This removal does not prune
`lem-galois-geometric-fibre`, which remains a proof dependency.
Removed the trial proof import `WeilConjectures.Mathlib.AlgebraicGeometry.Limits`:
its coproduct factorization lemma is already available through Basic.
This is pruning for this item only; other targets may still need the two omitted modules.

## Where the brief, the DAG or earlier work was wrong

The old plan did not mention the source library's existing quotient construction:
`Scheme.FiniteEtale.quotientCocone`, `fiber_quotientCocone`, and
`surjective_of_surjective_fiber` in FundamentalGroup.GaloisCategory, with
`isIso_sigmaDesc_of_existsUnique` in FundamentalGroup.Basic. These make it unnecessary
to use the two sorry-containing Galois/FLC equivalence modules.
No statement or definition is corrected, and no unit statement or step is bypassed.
The item is not a unit realization; the curve calculations and locally constant reduction
route of sk-thm-p1 remain intact. The used tool node `lem-fet-galois-category` is already
Lean-closed in the source library, from unit sk-prop-h2.
The construction and cardinal argument work for H=1, H=Q, and Q=1: the only cancellation
is of |H|, positive because every group contains its identity.
The search service LeanSearch was unavailable (HTTP 500), recorded as unavailable;
LeanFinder found abstract quotient-lifting lemmas, Loogle found the index API, and the
Mathlib grep had no scheme-torsor quotient hit. Repository searches found the concrete
source quotient implementation used here.


## Second reading by U2

1. **Unchanged interfaces: PASS.** Compared the sole delivered module with the current
   repository file using `diff`; independently compared the existing theorem signature
   byte for byte through `:=`. It is identical. No definition, public import, instance,
   or existing docstring changes. The only added declarations are four proved private
   helpers. No change record is required.
2. **Proof and trust: PASS.** Independently compiled the module using `lcompile.py`
   (3.2 seconds, no warnings). Compiled a scratch copy with `#print axioms` for all
   four helpers and the public theorem: only `propext`, `Classical.choice`, and
   `Quot.sound`; no `sorryAx`. Scanned the module: no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or kernel-check bypass. Read the torsor isomorphism argument,
   orbit induction, dependent-sum equivalence, and positive-cardinality cancellation.
3. **Split statements: PASS (none).** There are no split-off statements, new public
   statements, new nodes, or residual sorries. The private helpers are fully proved.
   Their arguments also cover singleton groups, the trivial and full subgroups, and
   empty intermediate fibre sums; a group has positive cardinality when finite.
   Repository searches found no general GaloisCover quotient or geometric-fibre tower
   count to replace this argument. The existing EtaleTorsor freeness lemma is for
   additive commutative groups, whereas this item permits noncommutative Q.
4. **Route and pruning: PASS.** Read the upstream quotient cocone, its fibre orbit
   theorem, surjectivity criterion, and `isIso_sigmaDesc_of_existsUnique`. The proof
   uses these existing results directly, then counts fibres without comparing different
   fibre functors. Independently checked `Subgroup.index_mul_card` through Loogle.
   The only added import is proof-only Basic; it supplies the quotient and torsor
   criterion. All three public imports support the statement. Read
   `dag/units/sk-thm-p1.json`: this node realizes neither its statement nor a step;
   its curve calculations and locally constant reduction route remain intact.
   Both old proof dependencies no longer used are listed under No longer needed.
5. **DAG agreement: PASS.** Compared the node JSON with the repository: only proof,
   proof_deps, and proof_origin change. Statement, stmt_deps, blueprint, unit,
   chapter, and lean record agree exactly. The dependencies equal the union of
   step uses. Read the Lean records for the finite-etale Galois-category and
   geometric-fibre nodes; both are already proved upstream. The new four-step
   argument records the quotient, restricted torsor, torsor cardinality, and
   fibre-tower cancellation actually used in Lean.

Second reading changed the report's import accounting to match the current repository:
FiberEquivalence and LocallyConstantEquivalence are removed proof imports, and the
redundant direct FiberDegree import is removed while its node remains needed. No Lean
proof or DAG repair was necessary.
