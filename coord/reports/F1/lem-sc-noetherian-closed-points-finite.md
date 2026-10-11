## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints` states
`AlgebraicGeometry.finite_of_isClosed_of_closed_points`, with proof `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- “X is a scheme”: `(X : Scheme.{u})`, with the universe explicitly declared.
- “X is Noetherian”: `[IsLocallyNoetherian X] [CompactSpace X]`. Mathlib's
  `AlgebraicGeometry.IsNoetherian` extends exactly these two classes, so these
  binders are equivalent to the original hypothesis, not merely topological
  Noetherianity. They directly use both recorded statement dependencies.
- “E is a subset of X”: `(E : Set X)`.
- “E is closed”: `(hE : IsClosed E)` in the ambient scheme topology.
- “Every point of E is closed in X”: `(hpoints : ∀ x ∈ E, IsClosed ({x} : Set X))`.
  This explicitly means closed in the ambient space, not just the subspace E.
- “E is finite”: `E.Finite` (set finiteness, with no chosen enumeration).

Dependencies read and used:
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`, module
  `Mathlib.AlgebraicGeometry.Noetherian`, full class signature and docstring read.
  Also read its existing affine-cover equivalences and open-immersion permanence
  theorem; these validate using the class for the node's affine-cover formulation.
- `def-weil-pbc-quasi-compact-scheme` is a Mathlib leaf: `CompactSpace`, module
  `Mathlib.Topology.Defs.Filter`, full signature and docstring read. It asserts
  compactness without a Hausdorff condition. The single direct Noetherian import
  already brings this declaration into scope.

Edge cases checked before writing: empty X (necessarily empty E), empty E,
a singleton closed point, and any finite discrete Noetherian scheme all satisfy
the intended conclusion. E equal to a positive-dimensional integral curve fails
the closed-point hypothesis because its generic point is not closed. Infinite
sets of closed points on an affine curve need not be closed; the closed-subset
hypothesis is essential. No nonemptiness, field, dimension, reducedness,
separatedness, or characteristic assumption is added.

Searches (executed via `/home/ubuntu/weil-launcher/msearch.py`, recorded in
`searches.jsonl`):
- LeanSearch: “A closed subset of a Noetherian scheme whose points are all closed
  is finite”: service unavailable, Internal Server Error; no result used.
- LeanFinder: the same query: eight hits, including
  `finite_irreducibleComponents_of_isNoetherian`, `IsNoetherian.noetherianSpace`,
  and `NoetherianSpace.exists_finite_set_isClosed_irreducible`; none states this
  theorem.
- Loogle: `IsClosed, Set.Finite, IsNoetherian`: zero hits.
- Mathlib grep: `finite.*closed|closed.*finite|IsNoetherian|LocallyNoetherian`
  in AlgebraicGeometry; and `finite.*closed|closed.*finite|finite_of` in
  Topology/NoetherianSpace.lean. The latter has finite-component decomposition
  and finiteness of Hausdorff Noetherian spaces, not the item's statement.
- `rg` in WeilConjectures and lean/Sheaf for finite/closed-point combinations;
  no exact match. Read the related full statements in
  `WeilConjectures/Mathlib/Topology/KrullDimension.lean`: the finite-complement
  theorem requires irreducibility and dimension at most one, and the
  zero-dimensional theorem requires a dimension hypothesis, so neither records
  exactly this node. No occurrence of the node id in WeilConjectures.
- Name collision search in Mathlib, WeilConjectures, lean/Sheaf, and
  `dag/lean_names_upstream.json`: no existing declaration with the chosen name.

Source verification: the local Stacks TeX files are absent on this machine;
read https://stacks.math.columbia.edu/tag/0BA8 (finite irreducible components) and
https://stacks.math.columbia.edu/tag/01IS (generic points of irreducible closed
subsets). The docstring records all three DAG proof steps and their dependencies.
The node's source prose mentions Kolmogorovness, but its actual proof correctly
uses sobriety; Kolmogorovness alone would not suffice for the generic-point step.
No change to the statement is needed, and there is no STATEMENT-DISPUTED finding.

## Second reading by F1

The node introduces a scheme `X`, a Noetherian hypothesis, a subset `E ⊆ X`,
closedness of `E`, the hypothesis that every point of `E` is closed in `X`, and
the conclusion that `E` is finite.  The Lean declaration renders these items as
`(X : Scheme.{u})`, `[IsLocallyNoetherian X] [CompactSpace X]`,
`(E : Set X)`, `(hE : IsClosed E)`,
`(hpoints : ∀ x ∈ E, IsClosed ({x} : Set X))`, and `E.Finite`, respectively.
The two class binders are exactly the node's recorded dependencies for a
Noetherian scheme (local Noetherianity and quasi-compactness); no Hausdorff,
separated, reduced, characteristic, field, dimension, or nonemptiness
hypothesis is added.  The singleton closedness is in the ambient scheme
topology, as required, and the quantifier order is unchanged.  The universe
`u` is bound explicitly and does not exclude any scheme case.

Edge cases checked are `E = ∅`, empty `X`, a singleton closed point, finite
discrete Noetherian schemes, and `n = 0` (not present in this statement).
Positive-dimensional integral schemes fail the point hypothesis at the generic
point, while an infinite set of closed points need not be closed; thus the
closed-subset and point hypotheses are both substantive.  No characteristic or
zero-object issue arises.

I searched LeanSearch, LeanFinder/Loogle, Mathlib, `WeilConjectures`, and the
project's `lean/Sheaf` tree for this theorem and for colliding definitions.
LeanSearch was unavailable; the other searches found only component-finiteness
and unrelated Noetherian results.  The recorded dependencies
`AlgebraicGeometry.IsLocallyNoetherian` and `CompactSpace` were read at their
declarations and are used directly.  No existing declaration matches the
node, so the module is retained.

No mismatch was found.  The worker module and node `lean.statement` already
match verbatim; the proof remains `sorry` as required for stage 2.  Compilation
with `scompile.py` succeeds.
