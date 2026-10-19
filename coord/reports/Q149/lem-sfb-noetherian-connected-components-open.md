## Worker report

Q149 records an exact existing match for
`lem-sfb-noetherian-connected-components-open`. No Lean module is written and no
statement, dependency, proof, or other node field changes. The previous incomplete
attachment already named these declarations; this delivery completes its stage-2
module, primary declaration, verbatim signature, author, date and existing fields.
There is no maintenance repair note for this item.

The existing source is `WeilConjectures/Mathlib/Topology/NoetherianSpace.lean`,
lines 50–62 in the slopmaster2 reference checkout. I read its module documentation,
the complete proofs and signatures, and their shared variable context:

```lean
variable {α : Type*} [TopologicalSpace α]
namespace TopologicalSpace.NoetherianSpace
variable [NoetherianSpace α]
instance finite_connectedComponents : Finite (ConnectedComponents α) := by
  -- Existing complete upstream proof.
theorem isOpen_connectedComponent (x : α) : IsOpen (connectedComponent x) :=
  ConnectedComponents.discreteTopology_iff.mp inferInstance x
```

The primary record's signature is verbatim from the instance, up to `:=`.
The two entries of `lean.declarations` are needed together; neither alone is
claimed to cover the full statement.

Clause-by-clause correspondence:

- A topological space is the arbitrary-universe parameter `α` with
  `[TopologicalSpace α]`. There is no scheme, separation or nonemptiness assumption.
- Stabilization of ascending chains of opens is `[NoetherianSpace α]`.
  Mathlib.Topology.NoetherianSpace defines it as `WellFoundedGT (Opens α)`,
  the standard ACC condition (using classical equivalence of the chain forms).
- The dependency `def-weil-connected-scheme` is the Mathlib leaf `ConnectedSpace`
  in Mathlib.Topology.Connected.Basic. I read its definition, which extends
  `PreconnectedSpace` with `Nonempty α`, and `connectedSpace_iff_clopen` in
  Mathlib.Topology.Connected.Clopen. These give precisely nonemptiness and the
  absence of a nontrivial clopen partition. The source module imports those
  definitions transitively via Mathlib.Topology.Connected.LocallyConnected.
- A component is Mathlib `connectedComponent x`, defined as the union of all
  preconnected subsets containing `x`. It contains `x` and is connected by
  `isConnected_connectedComponent`; `IsConnected.subset_connectedComponent`
  supplies maximality. Every maximal nonempty connected subset has a point and
  is therefore such a component. Thus no empty component is counted.
- Finiteness is exactly
  `TopologicalSpace.NoetherianSpace.finite_connectedComponents :
  Finite (ConnectedComponents α)`. Mathlib.Topology.Connected.Clopen defines
  `ConnectedComponents α` as the quotient of points by equality of their
  connected components; it indexes exactly the distinct components.
- Openness of each component is exactly
  `TopologicalSpace.NoetherianSpace.isOpen_connectedComponent (x : α) :
  IsOpen (connectedComponent x)` for every point `x`.
- The empty space is included because no `[Nonempty α]` occurs.
  `ConnectedComponents.isEmpty_iff_isEmpty` in
  Mathlib.Topology.Connected.Clopen explicitly identifies the empty quotient
  with the empty original space. Openness is then vacuous and finiteness holds
  for the empty type.

Source checked locally: Stacks topology.tex, tags 04MF
(`lemma-locally-Noetherian-locally-connected`), 04ME (`lemma-locally-connected`),
and 0052 (`lemma-Noetherian`). The first two give openness; 0052 gives finite
irreducible components. Each irreducible component lies in a connected component,
which yields finiteness of connected components, as in the existing upstream
proof. No proof is newly written in this stage-2 delivery.

Edge cases checked mathematically: the empty space has zero components; a point
has one open component; a finite discrete space has singleton open components;
the Sierpiński space has one component and needs no Hausdorff hypothesis;
two intersecting irreducible closed pieces lie in one connected component.
An infinite discrete space fails the ACC hypothesis, so is not a counterexample.
The arbitrary source universe does not exclude large topological spaces.

Searches performed with msearch.py for this group and item:

- LeanFinder, `A Noetherian topological space has finitely many connected components
  and each connected component is open`: eight hits, including finite irreducible
  components and NoetherianSpace; no single Mathlib declaration with both clauses.
- Loogle, `TopologicalSpace.NoetherianSpace, ConnectedComponents`: zero hits.
- Mathlib grep, `finite_connectedComponents|isOpen_connectedComponent|NoetherianSpace`
  in Topology/Connected: eight hits; openness assumes LocallyConnectedSpace and
  generic finite-component lemmas require other hypotheses.
- LeanSearch, `A Noetherian topological space has finitely many open connected
  components`: eight hits; finite irreducible components, ConnectedComponents,
  and compact locally connected finiteness, but no exact combined Mathlib match.
- Source rg, `finite_connectedComponents|isOpen_connectedComponent`, in
  WeilConjectures: exact declarations at NoetherianSpace.lean:50 and :61,
  alongside specialized consumers. Source search for the node id has no hits.
- Project rg in lean/Sheaf for the same names: no exact duplicate statement;
  occurrences of general openness in other modules are consumers. DAG search
  finds the item's own candidates and attachment, plus its monodromy consumer.

No new nodes, unusable dependencies, statement corrections or disputed statements
were found. Validation uses deliver2.py's generated existing-declaration probe
through scompile.py and its server preflight; no delivered Lean file needs a
separate compile.

## Second reading by Q149

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
