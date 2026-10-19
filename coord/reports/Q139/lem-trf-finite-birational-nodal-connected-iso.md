## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso` states
`AlgebraicGeometry.isIso_of_finite_birational_nodal_connected`, with exactly one
postponed theorem proof (`sorry`). A new definition node records an existing canonical map. The mathematical node
statement and proof are unchanged. Its statement dependencies gain `def-trf-completed-local-scalar-map`, which owns
`AlgebraicGeometry.Scheme.Hom.completedLocalScalarMap` through an `existing: true`
record on the unchanged published module. The theorem node
`lem-trf-nodal-point-etale-locality` is not a statement dependency.

Clause-by-clause correspondence:

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Two k-schemes: `{X Y : Scheme.{u}}` with `[X.Over (Spec (.of k))]` and
  `[Y.Over (Spec (.of k))]`. The maps to the base are Mathlib's canonical `↘` maps.
- Reducedness: `[IsReduced X] [IsReduced Y]`, precisely the dependency's sectionwise
  definition, equivalent to its stalkwise definition.
- Finite type over k: `LocallyOfFiniteType` and `QuasiCompact` on each structure
  morphism separately. Both parts of finite type are present for both schemes.
- Pure dimension one: `hXdim : X.IsPureDimension 1` and
  `hYdim : Y.IsPureDimension 1`, using the landed definition on the subspace of
  every irreducible component, rather than dimension of the whole scheme alone.
- Nodal target: `hnodal` quantifies over `y : Y`, assumes `y ∈ closedPoints Y`
  and `y ∉ (Y ↘ Spec (.of k)).smoothLocus`, and gives `Nonempty (@AlgEquiv k ...)`.
  Its left ring is `AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
  (Y.presheaf.stalk y)`. Its right ring is `MvPowerSeries (Fin 2) k` modulo the ideal
  spanned by `X 0 * X 1`. The explicitly supplied left algebra structure is
  `((Y ↘ Spec (.of k)).completedLocalScalarMap y).toAlgebra`; the right one is
  the standard quotient k-algebra. Thus the equivalence respects the prescribed
  k-scalars, and is not merely a ring isomorphism. Local finite presentation needed
  by `smoothLocus` is inferred from local finite type over the Noetherian field.
- Finite surjective morphism: `(f : X ⟶ Y) [IsFinite f] [Surjective f]`.
  No compatibility with the separately supplied X/k structure is imposed: the
  node does not explicitly require it, and the assertion holds without it.
- Open meeting every component: `(U : Y.Opens)` and `hmeets` saying
  `∀ Z : Set Y, Z ∈ irreducibleComponents Y → (Z ∩ (U : Set Y)).Nonempty`.
- Isomorphism above U: `hUiso : IsIso (f ∣_ U)`, the actual restricted morphism
  from the inverse image open to U, not an arbitrary isomorphism of those schemes.
  Supplying the witnessing U as a binder is equivalent to assuming its existence.
- Every geometric fibre connected: `hconnected` quantifies over every `y : Y`
  and applies `ConnectedSpace` to `pullback f` along
  `Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
  (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y`.
  This is exactly the recorded geometric-fibre dependency, including nonemptiness.
- Conclusion: `IsIso f`.
- No connectedness, separatedness or properness assumption is imposed on X or Y.
  All universes and variables are explicitly bound (`set_option autoImplicit false`).

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `AlgebraicGeometry.Scheme.Hom.smoothLocus` (the latter gives pointwise smoothness).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`;
  `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `AlgebraicGeometry.IsIntegralHom`
  was read as the companion definition (not needed in the signature).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`; `Mathlib.AlgebraicGeometry.Fiber` supplies
  the scheme fibre APIs used to describe the canonical geometric base point.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion` and
  its ring/algebra structures.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.AlgebraicGeometry.NodalPointEtaleLocality`:
  `Scheme.Hom.completedLocalScalarMap`, read in full including its source docstring.

Proof-plan imports are ordinary imports: `WeilConjectures.AlgebraicGeometry.Regular`
(`Scheme.normalization_properties`, `isIntegrallyClosed_stalk_of_smooth`, and its
normalization import), `Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso`
(`isIso_of_finite_birational_normal`), and
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`Algebra.IsIntegral.of_finite`).
The Noetherian consequences are in the public `Mathlib.AlgebraicGeometry.Noetherian`.
The upstream Regular source was read through `scompile.py --source`, since its live
normalization-properties signature is newer than the local record. The ordinary-point
delta/branch node has no recorded module yet; its future import is left to the
maintainer, as required for an unstated proof dependency. It is not a statement prerequisite.
The theorem docstring gives all five proof steps, with every proof dependency named.

Edge cases checked before writing:

- X = Y = empty is allowed: pure dimension and the quantified closed-point and fibre
  conditions are vacuous, U may be empty, and the empty morphism is an isomorphism.
- An empty source over nonempty target fails surjectivity and connected geometric fibres.
- The identity of any allowed nodal curve satisfies the criterion with U = Y.
- Disconnected unions are allowed; every component must meet U. No connectedness of
  the ambient curves is inferred from connectedness of their separate fibres.
- The normalization of a node has two points over its node; its geometric fibre is
  disconnected, so this familiar non-isomorphism does not meet the hypotheses.
- A cusp normalization illustrates why nodality is necessary.
- Adding an isolated source point over a target node is excluded by pure dimension one.
- The definition permits nonseparated/nonproper curves and self-nodes, and works in
  positive characteristic as well as characteristic zero. No finite-field or perfect-field
  binder is added. A common universe u is arbitrary and retains empty and reducible cases.

Searches for an exact existing statement (all via the prescribed wrappers/read-only trees):

- `msearch.py ... leanfinder "A finite birational morphism to a nodal curve with
  connected geometric fibres is an isomorphism"`: eight hits, including relative
  normalization's `instIsIsoToNormalizationOfIsIntegralHom`, finiteness of isomorphisms,
  and `isIso_of_isClosedImmersion_of_surjective`; none state the nodal criterion.
  Relative normalization identifies the source with a relative normalization, not
  the original target; the closed immersion theorem has a different hypothesis.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom,
  AlgebraicGeometry.IsFinite, CategoryTheory.IsIso"`: zero hits.
- `msearch.py ... leansearch "finite birational nodal curve connected geometric
  fibres isomorphism"`: eight hits on finite morphisms, finite/discrete fibres,
  relative normalization and closed immersions; no matching theorem.
- `msearch.py ... grep "nodal|seminormal|finite.*birational|connected.*fibr"
  AlgebraicGeometry`: zero hits.
- `rg` in upstream `WeilConjectures` for nodal/seminormal/finite-birational names:
  normalization birationality and incidental nodal cohomology mentions only.
  The prescribed node-id grep there has no match.
- `rg` in `lean/Sheaf` for the combined finite-birational/nodal criterion and
  `completedLocalScalarMap`: the consumer's proof-plan mention, and the existing
  scalar-map helper in NodalPointEtaleLocality. No existing theorem duplicates this item.

Primary source read: Temkin's arXiv v3 HTML,
https://arxiv.org/html/0707.3953v3#A2 , Appendix B, especially the ordinary-point
normalization description and absence of nontrivial bijective finite modifications.
The author's linked PDF timed out; the arXiv v3 text and PDF were available.
The local archival PDF remains absent; no repository literature file was modified.
No mathematical statement dispute or correction was needed. The definition-node ownership
repair requested in return H2 is documented below.

Validation: prescribed `scompile.py Q139 lem-trf-finite-birational-nodal-connected-iso`
compiled this file as both sandbox and library module, respectively 2.7 s and 2.8 s,
with exit code zero and no compiler diagnostics. The Lean module remains byte-identical to the returned delivery. The item differs from
the current base only in its lean record and the addition of the new definition dependency.

## Second reading by Q139

I reopened the node and completed module and separately read the signature against
all clauses above. This was a self-review: the dispatcher explicitly forbids starting
other agents; the maintainer supplies the independent review after delivery.
The main mismatch to guard against was using a ring equivalence where the node says
k-algebra equivalence; the written signature uses the canonical completed-local
scalar map and an explicit `AlgEquiv`. I also verified that the nodal condition is
restricted to closed nonsmooth points, that both finite-type hypotheses include
quasi-compactness, that both schemes have pure dimension one, and that U meets
individual components rather than merely being nonempty. The fibre expression is
exactly the canonical algebraic-closure pullback in the dependency record. No
separatedness, properness, connectedness of X/Y, integral-scheme or k-linearity
assumption slipped into the signature. The five-step proof docstring matches the
DAG's component, normalization, delta, connected-fibre and affine-local steps.
No change was required by this second reading.


## New nodes

`def-trf-completed-local-scalar-map` owns the canonical map from a field k into
the maximal-ideal completion of the stalk of a k-scheme at any point. It records
the existing `AlgebraicGeometry.Scheme.Hom.completedLocalScalarMap` in
`Sheaf.AlgebraicGeometry.NodalPointEtaleLocality`, with `existing: true`; no module
is added or modified for this node. Source: Stacks curves.tex section-nodal
(Tag 0C46), and lemma-node-etale-local (Tag 0C57), read in the local source.
LeanSearch and LeanFinder returned only constituent maps, function-field and
residue-field structures; Mathlib grep returned zero hits for the completed-scalar
patterns. Upstream grep found no such composite. Project grep found the existing
helper, which is reused. DAG and blueprint searches found no definition-node owner;
the existing theorem's helper list does not supply that owner. `IsOrdinaryNode`
is a different predicate and is not substituted.

The field and scheme binders are `{k : Type u} [Field k] {X : Scheme.{u}}`; the
structure map and arbitrary point are `(f : X ⟶ Spec (.of k)) (x : X)`. The codomain
is `AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
(X.presheaf.stalk x)`. The defining term composes `Scheme.ΓSpecIso.inv`, `f.appTop`,
`X.presheaf.Γgerm x`, and the stalk's `algebraMap` into completion, exactly the
four arrows in the new node's statement. The associated algebra is `.toAlgebra`,
as already used by the unchanged consumer. There is no algebraic-closedness,
finite-type, closed-point, dimension or smoothness restriction on this map.
For empty X there is no x to supply; generic points and every characteristic are
allowed. No existence theorem, `choose`, or postponed proof enters its definition.

## Repair of return H2

The return on immutable head `f56eebcf6073` requested definition-node ownership
for `completedLocalScalarMap`. Added the full H12 definition record above and
replaced the delivery-added theorem dependency with this definition dependency.
The original mathematical statement, proof and proof dependencies are unchanged;
no `statement_change` is appropriate. Comparing with the read-only current base
confirms that all other item fields agree. The Lean file is retained unchanged.

Second reading of this repair: I reopened the new record, the existing map's
signature, docstring and complete body, and the consumer. Each arrow of the new
definition is the actual map in the body. The consumer still uses the prescribed
canonical k-algebra structure in its nodal `AlgEquiv`. The theorem's conclusion
is neither assumed nor used by the new definition node. This is self-review,
as the dispatcher prohibits other agents; the maintainer reviews independently.

Repair validation: `scompile.py` compiled the unchanged theorem as sandbox and
library modules in 2.1 s and 2.2 s with no diagnostics. The initial saved-packet
dry run passed (`2b6379aa09`); the repaired packet is checked again before push.
The exact blueprint search printed `0 blueprint nodes match completedLocalScalarMap`.
