## What changed

Completed `Sheaf.AlgebraicGeometry.EtaleGeometricFibreCompactSections` from the retained
attempt, preserving the theorem statement and all public imports. The proof establishes
finiteness, the canonical scheme coproduct isomorphism, proper support of every section,
invertibility of the actual restriction-and-germ map, and the precise graph-extension formula.
Private proved helpers handle module-valued unit/germ compatibility, finite coproduct
coordinates, single-summand values, point transport, and clopen extension by zero.

The shorter route first makes the geometric fibre finite over the algebraically closed field.
It then uses the existing module-valued finite-discrete-scheme stalk theorem and closed-support
API, avoiding the general normal-base decomposition and abelian-to-module conversions.
Updated the existing DAG node's proof, proof_deps, proof_origin and obsolete tool_uses.
No definition, public signature, visibility, target, or consumer was changed.
The completed module compiles cleanly through `lcompile.py` in 9.0 seconds, with no
errors or warnings (2026-10-19).

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.etaleGeometricFibreCompactSections`
(node `lem-sfb-etale-geometric-fibre-compact-sections`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. All six private helpers are proved.
`#print axioms AlgebraicGeometry.etaleGeometricFibreCompactSections` reports exactly
`[propext, Classical.choice, Quot.sound]`; the axiom-check copy compiled cleanly in
10.7 seconds. Import-direction checks passed for both new dependency paths.

The empty fibre is handled by the same empty coproduct/product and coverage arguments.
The zero section and zero coefficient ring are allowed; proper support is established for
all sections without any nonvanishing assumption. Graph extension tests arbitrary
algebraically closed geometric-point fields, as in the unchanged conclusion.

## No longer needed

Removed these proof imports and their proof-dependency nodes:

- `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`
  (`lem-weil-pbc-etale-sheaf-clopen-product`): direct module-valued disjoint-cover gluing
  and the existing finite-discrete stalk theorem suffice.
- `Sheaf.AlgebraicGeometry.GeometricPointCohomology`
  (`lem-weil-pbc-geometric-point-cohomology`): no higher cohomology calculation is needed;
  use `Etale.isIso_piLift_toPresheafFiber` directly with module coefficients.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: its separate interface is unused;
  the statement and proof use `pointSmallEtale.sheafFiber` from the retained public imports.
  The geometric-stalk node stays as a dependency of the actual calculation.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
  (`lem-weil-pbc-reduced-induced-closed-subscheme`): the closed-support API already supplies
  the exact vanishing-ideal subscheme; no uniqueness comparison is required.
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage`
  (`lem-weil-pbc-closed-subset-proper-over-base-union-preimage`): compose the closed support
  immersion directly with the finite, hence proper, fibre morphism.
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
  (`lem-weil-pbc-inverse-image-stalk-germ`): its abelian-only theorem is replaced by the
  private proved module-valued compatibility calculation using the canonical comparison.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`
  (`sbc-lem-etale-over-normal`): the general normal-base decomposition is unnecessary;
  finiteness over an Artinian field spectrum and canonical point lifts give the decomposition.

Removed the six obsolete top-level tool_uses entries corresponding to the discarded theorem
nodes above. The unit's adjunction/localization route and all its realized steps are preserved;
this only changes the implementation of its finite geometric-fibre tool. No module is withdrawn.
These are dependencies pruned from this proof, not claims that other target branches never use them.

## Where the brief, the DAG or earlier work was wrong

The interrupted sandbox was close to a complete proof but its coordinate comparison did not
compile: the subtype's decidable equality and `Classical.decEq` instantiate the direct-sum
comparison differently. Their equality by `Subsingleton.elim` repairs this without changing
any data or interface. The original plan was mathematically valid but longer than necessary:
finite-over-field properness removes the support-union argument, and a module-valued source
API removes the abelian coefficient comparisons. No disputed statement or new node.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
