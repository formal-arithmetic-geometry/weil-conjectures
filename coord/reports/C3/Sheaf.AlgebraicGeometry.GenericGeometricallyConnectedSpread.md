## What changed

Replaced the original hole in
`AlgebraicGeometry.exists_open_geometricallyConnected_fibres_of_generic`
by a complete Lean proof using the new proof-only import
`Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread`.
The original theorem's signature and public imports are unchanged.

The private, fully proved `finite_closed_cover_paths` establishes the connected
intersection graph of any finite closed cover of a connected space by nonempty
sets. The main proof transports its paths along preserved edges, uses Mathlib's
connected-union theorem, and descends connectedness along a surjective continuous
scheme map. It also derives that the index type is nonempty from generic
connectedness, rather than adding that hypothesis.

The remaining geometric theorem applies to EVERY finite type family on an
irreducible base, including families with disconnected or empty generic fibre.
Its conclusion supplies generic component sets and auxiliary fibre component
sets, their covers and intersection edges. It contains neither the original
connectedness hypothesis nor connectedness of a whole special fibre. Thus the
parent requires the proved graph argument and surjective descent, not a projection
of a hidden target conclusion.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_open_geometricallyConnected_fibres_of_generic`
(node `lem-sbc-generic-geometrically-connected-spread`). Its proof now compiles
without any local holes. The private `finite_closed_cover_paths` is fully proved.

Added exactly one hole:
`AlgebraicGeometry.exists_open_generic_fibre_incidence_spread`
(node `lem-sbc-generic-fibre-incidence-spread`). Its proof is exactly `:= by sorry`
in the new module, with its source and complete geometric argument in its
docstring and node. There are no other sorries in the delivery. This is a
DECOMPOSITION: one original hole closed, one geometric hole added, net zero.
The original theorem still depends on that hole; this is not an axiom-free proof
of the target's import closure.

## No longer needed

No imports, existing nodes or existing modules are pruned: the original node had
no named proof dependencies. The route does not need the source's additional
shrinking to remove pairs with empty generic intersection. Only preservation
of nonempty generic intersections is used; extra special intersections are harmless.
No duplicate of Mathlib's fibrewise characterization is introduced.

## Where the brief, the DAG or earlier work was wrong

The existing node's proof is a single large geometric argument with no named
proof dependencies, so there are no planned lower declarations to import.
The earlier attempt's component package included the whole target conclusion
as a conjunct and was not a reduction. That attempt also duplicated an existing
Mathlib characterization. Both faults are absent here.

An earlier second-reading comment also incorrectly treated dependence on a named
sorry theorem as itself disallowed. Stage 3 explicitly permits such dependence;
the real issue was that the earlier statement merely repackaged the target.
The present remaining theorem is the independent geometric incidence part,
and the connected-graph and descent portions are actual Lean proofs.

Checked the source at Stacks Tags 055G, 0551, 054Y, 0559, 052A and 054W.
The ring-theoretic source-library generic connectedness/irreducibility theorems
need noetherian affine hypotheses (and, for connectedness, a point), which the
unchanged target does not assume. No such hypothesis is silently added.

Edge cases for the new statement: empty generic fibre uses an empty index type
and Tag 054W; a disconnected generic fibre still has a finite component cover
but need not have a connected intersection graph; a single component gives a
one-vertex graph; components not split over a test field are handled by the
auxiliary common field and the surjective map p. Reduction of a nonreduced base
transfers opens through a homeomorphism; openness is applied to the original
finite étale model, not incorrectly to its reduction morphism.
The unit record `sk-prop-normal-form` has empty realized lists; its statement
and slicing route remain untouched.

## New nodes

`lem-sbc-generic-fibre-incidence-spread`, in
`dag/nodes/sec-smooth-base-change/`, matches the single new module
`Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread` and the named geometric
hole. It records finite generic component covers and their persistent intersection
edges on auxiliary fibres, without any connectedness hypothesis on the family.
Three search kinds were run with msearch.py: LeanSearch was unavailable,
LeanFinder returned only general scheme and finite-type results, and Mathlib grep
found no incidence-spreading theorem. No interface change or forced adaptation
was needed, and there is no change record.

## Second reading by C3

1. Compared the delivered item module with the repository version. The public theorem signature is byte-for-byte unchanged; the only interface change is the separately declared split-off theorem in the new module, recorded by its node. No target statement or existing definition was altered.

2. Compiled both delivered modules with `lcompile.py --all`. They compile without errors or warnings. The item theorem and private helper contain no `sorry`; the sole remaining `sorry` is the named split theorem, and there are no axioms, unsafe declarations, opaque definitions, or hollow definitions in the delivery.

3. Read the split-off incidence statement and its docstring and checked its edge cases: empty generic fibre permits an empty finite index type, disconnected generic fibres are allowed, and the conclusion only preserves generic intersection edges. It is strictly weaker than the parent target and is the geometric input the parent proof consumes; its DAG node matches the Lean declaration and records the source and proof plan.

4. Checked the proof route against the DAG. The finite closed-cover path argument, connected union, and surjective connectedness descent are proved directly in Lean. The parent imports the incidence module only for the split theorem, and the unit route is retained. No old proof dependency is unused and no import can be pruned.

5. Checked declaration names and searched the library and Mathlib for an existing incidence-spreading result; none duplicates the new theorem. The DAG proof, `proof_deps`, `proof_origin`, and node metadata agree with the delivered files. The only change made in this second reading is this report section; no code or node repair was needed.
