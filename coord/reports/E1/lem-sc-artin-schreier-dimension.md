## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension` states
`AlgebraicGeometry.isZero_etaleCohomology_constantZMod_of_one_lt_of_charP`, with `sorry` as
its only proof. No definitions, new nodes, dependency replacements, or statement corrections
were needed.

Hypothesis and conclusion correspondence:

- An algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- A scheme over this field is `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`.
  This explicit morphism is required by the recorded curve declaration.
- A separated connected curve is `[IsConnectedCurve f]`. Its parent `IsCurve f` supplies
  separatedness, local finite type and quasi-compactness (together finite type), and dimension
  at most one. Its own fields supply connectedness, nonemptiness and dimension exactly one,
  as expressly required by def-sc-curves. This uses the connected-curve specialization in the
  same recorded module, rather than imposing merely `ConnectedSpace` on a dimension-at-most-one
  scheme.
- Smoothness over the field is `[Smooth f]`.
- Characteristic `p > 0` is `(p : ℕ) [CharP k p] (hp : 0 < p)`.
  Primality need not be assumed separately: positive characteristic of a field is prime.
- The constant sheaf `F_p` is exactly `C.constantZMod p`, the recorded sheafification of the
  constant presheaf with value `AddCommGrpCat.of (ULift (ZMod p))`.
- For every cohomological degree greater than one, `(q : ℕ) (hq : 1 < q)`.
  The recorded cohomology functor takes integer indices, so the degree is `(q : ℤ)`.
- `H^q(C,F_p)` is `(Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)).obj`
  applied to `((DerivedCategory.singleFunctor
  (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj (C.constantZMod p))`.
  This is precisely derived global sections of the sheaf placed in degree zero, followed by
  degree-q homology, as specified in the recorded def-weil-pbc-etale-cohomology.
- The equation `H^q = 0` is `IsZero` of this **abelian-group category object**. It asserts that
  its additive group is trivial; it is not an `IsZero` statement about a bare type.

Dependencies inspected and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve` and
  `AlgebraicGeometry.IsConnectedCurve` (full class fields and docstrings read).
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `AlgebraicGeometry.Scheme.constantZMod` (definition and docstring read).
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` (signatures, ambient category binders,
  definitions and docstrings read).
- Mathlib's `Smooth`, `IsAlgClosed`, `DerivedCategory.singleFunctor` and categorical `IsZero`.

Edge cases: `p=0` is excluded by the exact stated positive-characteristic hypothesis; `p=1`
is impossible for a field with `CharP k 1`. Degrees zero and one are excluded, degree two is
included. The empty scheme and `Spec k` are excluded by the node's definition of connected
curve, faithfully encoded by `IsConnectedCurve`. Affine and proper smooth curves are both
included: neither property is imposed. Arbitrary scheme universes are allowed; the ULift
coefficient group lives in the universe required by the small étale site.

Searches for an existing statement:

- `msearch.py ... leansearch "etale cohomology characteristic p curve constant ZMod vanishes
  above one"`: service unavailable (Internal Server Error), recorded as unavailable.
- `msearch.py ... leanfinder "Artin Schreier vanishing etale cohomology constant F_p smooth
  connected curve characteristic p above degree one"`: eight hits concerning cotangent
  cohomology and Hilbert 90; no matching statement.
- `msearch.py ... loogle '"ArtinSchreier"'`: zero hits.
- `msearch.py ... grep 'ArtinSchreier|artinSchreier|cohomology.*constantZMod'`:
  zero Mathlib hits.
- `rg` on the source tree for `constantZMod`, `subsingleton_sheafH`, `CharP`,
  `IsConnectedCurve`, and the item's identifier: read the affine-only Artin–Schreier theorem
  and `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP`
  in `Curve/SmoothCalculations.lean` in full. The latter concerns the sheaf `Λ/pΛ` for an
  arbitrary coefficient ring and uses Ext cohomology `Sheaf.H`, not the recorded constant
  abelian sheaf and derived-global-sections functor. It is not an exact declaration for this
  node. The source affine theorem also has an additional affine hypothesis.
- `rg` on `lean/Sheaf` for the item's identifier, `cohomology.*constantZMod`,
  `Etale.cohomology`, and the chosen declaration name: no existing declaration states this
  theorem. The chosen name also has no source or Mathlib match.

The blueprint and Stacks literature files referenced in the node are absent in this clone.
The node's full seven-step proof was read; its source check was made against
[Stacks Tag 0A3N](https://stacks.math.columbia.edu/tag/0A3N), which gives vanishing above
one for separated finite-type dimension-one schemes over an algebraically closed field of
positive characteristic. The module docstring retains the node's seven-step proper/affine
argument and names its dependencies; no proof route was changed.

Validation: `scompile.py E1 lem-sc-artin-schreier-dimension` compiled the module cleanly on
the server (exit code 0, 2.0 seconds), with no warnings. The delivery dry run is the last check;
the independent second reader supplies the second-reading section and delivers.

## Second reading by E1

I reread the node statement, its three statement dependencies, the recorded declarations, and
the Lean module. The item-by-item correspondence is:

- The node's algebraically closed field `k` is rendered by `{k : Type u} [Field k]
  [IsAlgClosed k]`; no extra field or algebraic-closure hypothesis is present.
- The scheme over `k` and its structure morphism are `{C : Scheme.{u}}` and
  `(f : C ⟶ Spec (.of k))`. This is the recorded representation of a scheme over the base.
- “Separated connected curve” is `[IsConnectedCurve f]`. Its declaration extends `IsCurve f`,
  supplying separatedness, finite type, quasi-compactness, and dimension at most one, and adds
  connectedness and dimension exactly one (hence nonemptiness). No stronger curve property is
  assumed.
- Smoothness over the field is exactly `[Smooth f]`; no properness or affineness is added.
- Positive characteristic `p > 0` is `(p : ℕ) [CharP k p] (hp : 0 < p)`. The positivity
  hypothesis excludes `p = 0`; primality is automatic for a field and is not an added assumption.
- The constant sheaf `F_p` is the dependency declaration `C.constantZMod p`, whose underlying
  coefficient is the recorded `ULift (ZMod p)` constant étale sheaf. The displayed cohomology
  object is precisely `Etale.cohomology ... (q : ℤ)` applied to that sheaf in degree zero,
  matching the node's cited cohomology convention.
- The degree condition `q > 1` is `(q : ℕ) (hq : 1 < q)`, and the conclusion is categorical
  `IsZero` of the abelian-group cohomology object, exactly expressing `H^q(C,F_p)=0`.

The quantifier order and universes are preserved: the coefficient category is
`AddCommGrpCat.{u + 1}`, while the scheme and field use the same `u`; no independent universe
for a test object is introduced. The empty scheme is excluded by `IsConnectedCurve`; `Spec k`
is excluded by its dimension-equality field. Degree two is included, while degrees zero and one
are excluded. Positive characteristic and all allowed algebraically closed fields are covered.

I searched Mathlib, the slopmaster2 source, and `lean/Sheaf` with Artin–Schreier,
`constantZMod`, and cohomology queries (including Loogle/LeanFinder via `msearch.py`). The only
nearby declarations are the affine-only source theorem and the Ext-based constant-mod-sheaf
statement; neither has this node's hypotheses and derived étale cohomology conclusion. No
existing exact declaration was found. The recorded dependency declarations were usable, so no
dependency module or statement correction was needed. The module compiled cleanly with
`scompile.py`; no mismatch was found and no Lean text was changed.
