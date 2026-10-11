## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedPointOfAffineOpen` states
`AlgebraicGeometry.closedPoint_of_affineOpen`, with its proof left as `sorry`.
No definitions, auxiliary claims, or new nodes are needed. The node is unchanged
except for its `lean` record.

The statement matches each hypothesis and clause:

- The field k is `{k : Type u} [Field k]`.
- The scheme X is `{X : Scheme.{u}}`.
- Its structure morphism over k is `(f : X ⟶ Spec (CommRingCat.of k))`;
  `[LocallyOfFiniteType f]` says locally of finite type, with no quasi-compactness
  or finite-type strengthening.
- An affine open subscheme U of X is `(U : X.Opens) (_hU : IsAffineOpen U)`.
  Mathlib defines `IsAffineOpen U` as `IsAffine U`, for the induced open subscheme.
- A point x in U is `(x : U)`; membership is carried by its subtype.
- Closedness of x in U is `(hx : x ∈ closedPoints U)`.
- The conclusion `(x : X) ∈ closedPoints X` asserts closedness in X of the same
  point under the inclusion. `closedPoints` is definitionally the set of points
  whose singleton is closed.

Dependency declarations read and used:

- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`. Its recorded companion
  `QuasiCompact` (Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact) was also read;
  it is not required by this node.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme`, used for the base scheme; `Spec.map` and
  `Spec.homEquiv` were read as the record specifies. The affine-open hypothesis
  uses Mathlib's `AlgebraicGeometry.IsAffineOpen` from
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-weil-closed-points`: `closedPoints`, `Mathlib.Topology.JacobsonSpace`.
  Its signature, defining body, and `mem_closedPoints_iff` were read.

The single FiniteType import supplies these notions transitively. All universes
and variables are explicitly bound. A common universe for k and X follows the
Mathlib Scheme morphism API; arbitrary universe u is allowed, and smaller objects
can be lifted to a common universe.

Edge cases checked: the empty scheme and empty open have no x and give vacuous
statements; U = X gives the immediate closedness assertion. No nonemptiness,
separatedness, reducedness, algebraic closure, field-characteristic restriction,
or global quasi-compactness is assumed. Nonseparated and non-quasi-compact
locally finite-type schemes are included. Affineness is retained even though
Jacobson topology gives the conclusion for any open subset.

Source checked: the local Stacks tex file was absent, so I opened
[Stacks Tag 0478](https://stacks.math.columbia.edu/tag/0478), Lemma 33.14.1.
Its Jacobson assertion applies to schemes locally of finite type over a field.
The module docstring carries the node's two-step closure-and-density proof.
No statement correction or dispute was found.

Searches made using `/home/ubuntu/weil-launcher/msearch.py` (real queries and
results logged in `searches.jsonl`):

- LeanFinder: "closed points of an affine open in a scheme locally of finite type
  over a field are closed in the scheme". Eight hits, including
  `LocallyOfFiniteType.jacobsonSpace`,
  `isClosed_singleton_iff_locallyOfFiniteType`, and
  `Scheme.Hom.closePoints_subset_preimage_closedPoints`; none has the item's
  precise objects and hypotheses. They are supporting general results.
- Loogle: `IsClosed, AlgebraicGeometry.LocallyOfFiniteType`. Nine hits, including
  closed-point residue-field results requiring algebraic closure; no exact match.
- Mathlib grep: `isClosed.*singleton|preimage_closedPoints|jacobsonSpace` in
  AlgebraicGeometry. Twenty-three hits; confirms the supporting Jacobson results.
- LeanSearch: "closed points of an affine open are closed in a scheme locally of
  finite type over a field". Service unavailable (Internal Server Error);
  no mathematical verdict is inferred from the failure.
- `rg` of WeilConjectures and lean/Sheaf for closed points and affine opens:
  `WeilConjectures/ClosedPoints.lean` has a private result from maximality to
  closedness in U and another result from finite residue fields to closedness
  in X; neither states this field-relative assertion. The landed
  `Sheaf/AlgebraicGeometry/ClosedPointField.lean` gives residue-field criteria,
  not this affine-open assertion. The item's id was also searched throughout
  WeilConjectures, with no hits.
- `rg` of Mathlib, WeilConjectures, lean/Sheaf, and
  `dag/lean_names_upstream.json` for the chosen full declaration's short name
  `closedPoint_of_affineOpen`: no existing declaration found.

Validation: server single-module compile and `deliver2.py --no-push` dry run;
results recorded below after completion. No delivery is pushed by this worker.

## Second reading by E1

I opened the item node in `dag/nodes/sec-picard-framework/lem-sc-affine-maximal-points-closed-in-lft-scheme.json`
and the module `Sheaf.AlgebraicGeometry.ClosedPointOfAffineOpen`.
The node's objects and clauses match the Lean signature item by item:

- The field object is `{k : Type u} [Field k]`, rendered by the first two binders.
- The scheme is `{X : Scheme.{u}}`, and its structure morphism is
  `f : X ⟶ Spec (CommRingCat.of k)` with exactly `[LocallyOfFiniteType f]`.
- The affine open is `U : X.Opens` with the explicit hypothesis
  `_hU : IsAffineOpen U`; the hypothesis is present even though the proof is
  sorry and the eventual open-embedding argument only needs openness.
- The point is `x : U`, so its membership in the open is represented by the
  subtype, and `hx : x ∈ closedPoints U` is exactly the node's closed-point
  hypothesis.
- The conclusion `(x : X) ∈ closedPoints X` is the node's ambient closedness
  clause, with the same coercion and quantifier order.

No extra assumptions occur: there is no quasi-compactness, finite-type,
separatedness, reducedness, nonemptiness, characteristic, algebraic-closure,
or global finiteness hypothesis. The common universe `u` permits arbitrary
schemes and fields in the statement. Empty `X` or `U` has no point `x` and is
vacuous; `U = ⊤` specializes immediately to the ambient assertion; zero or
characteristic cases are not excluded by `[Field k]`.

I checked the dependency records, including `def-weil-finite-type-morphism`,
`def-weil-affine-spectrum`, `def-weil-closed-points`, and the proof dependency
`lem-sc-lft-over-field-jacobson-space`. Their declarations give respectively
`LocallyOfFiniteType`, `Spec`, `IsAffineOpen`, `closedPoints`, and the Jacobson
density statement used by the node's two proof steps. The latter is a separate
statement node whose recorded Mathlib candidate is the non-instance lemma
`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`; it is not silently
treated as an inferred instance in this item's statement.

Searches were repeated with LeanFinder, Loogle, LeanSearch, and `rg` over
Mathlib, `WeilConjectures`, `lean/Sheaf`, the DAG names, and the slopmaster2
source for `closedPoint_of_affineOpen`, affine-open closed points, and Tag 0478.
Only general Jacobson/open-embedding results were found; no exact declaration
exists. LeanSearch was unavailable, as recorded in `searches.jsonl`.

No mismatch was found and no source or node correction was required. The only
repair to the worker report is this independent reading and clarification that
the Jacobson statement is a proof dependency rather than an additional
hypothesis. The module compiled cleanly with `scompile.py`; its sole proof is
the required `sorry`.
