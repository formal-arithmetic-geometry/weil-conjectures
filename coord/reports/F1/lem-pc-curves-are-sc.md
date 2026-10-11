## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothProjectiveCurveConnected` states
`AlgebraicGeometry.Scheme.Hom.isConnectedCurve_of_isSmoothProjectiveCurve`, with only
`sorry` as proof. No definitions are introduced and no node fields besides `lean` change.

Hypothesis and clause correspondence:

- An algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- A scheme X over k: `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`. The explicit
  structure morphism is the argument taken by the recorded curve definition.
- A smooth projective curve: `[f.IsSmoothProjectiveCurve]`, precisely the recorded
  `Scheme.Hom.IsSmoothProjectiveCurve`, extending `f.IsCurveOverField`, `Smooth f`
  and `IsProjective f`. `IsCurveOverField` requires an integral, separated, finite-type
  scheme of local-ring dimension one, as the node's hypothesis says.
- A connected curve in the file-06 sense: the first conjunct `IsConnectedCurve f`,
  using the same module and notions as the dependency `def-sc-curves`.
- Nonempty and connected: its field `connectedSpace : ConnectedSpace X` supplies both;
  `ConnectedSpace.toNonempty` is part of Mathlib's connectedness definition.
- Separated: the inherited `IsCurve.toIsSeparated` field of `IsConnectedCurve f`.
- Finite type: the inherited `LocallyOfFiniteType f` and `QuasiCompact f` fields
  of `IsCurve f`, their conjunction being Mathlib's finite-type convention.
- Topological Krull dimension one: `IsConnectedCurve.krullDim_eq_one` states
  `topologicalKrullDim X = 1`; the inherited at-most-one field adds no strength.
- Smooth structure morphism: the second conjunct `Smooth f`.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`,
  `AlgebraicGeometry.Scheme.Hom.IsSmoothProjectiveCurve` (def-pc-smooth-projective-curve),
  and its underlying declarations in `Sheaf.AlgebraicGeometry.Variety` and
  `Sheaf.AlgebraicGeometry.Dimension` were read in full.
- `WeilConjectures.AlgebraicGeometry.Curve`, `AlgebraicGeometry.IsCurve` and
  `AlgebraicGeometry.IsConnectedCurve` (def-sc-curves). The recorded declaration
  names IsCurve; the same module gives exactly the connected specialization, so
  there is no unusable dependency or need to redeclare it.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`, as explicitly identified
  in def-weil-algebraic-closure's mathlib_match.
- `Mathlib.Topology.Connected.Basic`, `ConnectedSpace` (def-weil-connected-scheme).
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`
  (def-kun-topological-krull-dimension), used in the connected-curve field.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- def-weil-pbc-scheme-conventions fixes no extra notion; separatedness and finite type
  use Mathlib's `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` through IsCurve.

Edge cases checked: the empty scheme is excluded by the integral hypothesis and
also by dimension one; a point Spec k has dimension zero and is excluded. A disconnected
union of curves is not integral, hence cannot satisfy the hypothesis. Connected reducible
curves can satisfy the conclusion but need not satisfy the stronger hypothesis; the theorem
only gives the stated implication. No characteristic assumption is imposed. The common
universe matches both dependency classes and imposes no additional smallness restriction:
any field and its scheme can be considered in a sufficiently large common universe.
Projectivity remains in the hypothesis although the proof does not use it.

Searches (all run with the prescribed msearch.py wrapper unless specified):

- LeanSearch: `smooth projective integral scheme dimension one connected curve`:
  unavailable, Internal Server Error; no mathematical verdict inferred.
- LeanFinder: `A smooth projective integral curve over an algebraically closed field is
  a smooth connected curve`: eight unrelated Weierstrass-curve results, no matching statement.
- Loogle: `AlgebraicGeometry.IsConnectedCurve, AlgebraicGeometry.IsIntegral`:
  zero hits; IsConnectedCurve is unknown to the Mathlib search service.
- Mathlib grep: `IsSmoothProjectiveCurve|IsConnectedCurve` in AlgebraicGeometry:
  zero hits.
- Local rg: `IsSmoothProjectiveCurve|isConnectedCurve_of|curves-are-sc` in the source
  WeilConjectures and project lean/Sheaf: only the existing smooth-projective-curve
  definition appeared, no implication matching this item.
- Local grep: `lem-pc-curves-are-sc` in the source WeilConjectures: no occurrence.
- Name collision rg: `isConnectedCurve_of_isSmoothProjectiveCurve` in
  dag/lean_names_upstream.json, Mathlib, source WeilConjectures and lean/Sheaf:
  no occurrence.

The module docstring includes all five DAG proof steps, including the conversion from
local-ring dimension to topological dimension. No statement dispute or correction is needed.
The blueprint markdown named by the source record is absent in this machine's literature
checkout; the node's full statement and five sourced proof steps were read instead, together
with the actual recorded dependency declarations. This does not require a source correction.

## Second reading by F1

I reread the node `lem-pc-curves-are-sc` and the complete declaration
`AlgebraicGeometry.Scheme.Hom.isConnectedCurve_of_isSmoothProjectiveCurve`.
The correspondence is as follows.

- The node's algebraically closed field (k) is rendered by
  `{k : Type u} [Field k] [IsAlgClosed k]`; no characteristic hypothesis is added.
- Its scheme (X) and structure map to `Spec(k)` are rendered by
  `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`.  This is the explicit structure morphism used by
  the recorded `IsSmoothProjectiveCurve` and `IsConnectedCurve` declarations, so it denotes
  the same scheme-over-field object.
- The smooth-projective-curve hypothesis is exactly `[f.IsSmoothProjectiveCurve]`; opening its
  dependency shows the curve-over-field, smooth, and projective fields required by the node.
- The conclusion `IsConnectedCurve f ∧ Smooth f` renders every listed clause: the first class
  extends separatedness, locally finite type and quasi-compactness, and has
  `connectedSpace` (hence nonempty) and `krullDim_eq_one`; the second conjunct is smoothness of
  the same structure morphism.  Thus no conclusion is dropped or strengthened and quantifier
  order is unchanged.

I checked the dependency declarations in `SmoothProjectiveCurve.lean`, `Variety.lean`,
`WeilConjectures.AlgebraicGeometry.Curve`, and the Mathlib leaves for `IsAlgClosed`,
`ConnectedSpace`, and `topologicalKrullDim`.  They are the declarations cited by the module;
there is no duplicate declaration in Mathlib, WeilConjectures, or `lean/Sheaf`.

Edge cases were checked: the empty scheme cannot satisfy the integral curve hypothesis (and
`ConnectedSpace` supplies nonemptiness); `Spec k` has dimension zero and is excluded by the
dimension-one field; disconnected or reducible alternatives do not satisfy the integral input;
no characteristic is assumed; and the shared universe `u` is the standard universe of the
scheme and its base field and introduces no extra mathematical restriction.

The prescribed searches (LeanSearch, LeanFinder/Loogle, and repository/Mathlib grep) found no
existing statement or definition.  The first reading's statement and module already matched the
node in every hypothesis and conclusion, so I made no changes.  Compilation with
`scompile.py F1 lem-pc-curves-are-sc` succeeds with only the permitted `sorry` proof warning.
