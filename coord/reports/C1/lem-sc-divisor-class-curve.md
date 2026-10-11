## Worker report

The module `Sheaf.AlgebraicGeometry.DivisorClassCurve` states
`AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic_associatedModule`.
The single theorem has only `sorry` as its proof. No notions are redefined and no new nodes
or dependency modules are supplied. The node statement is unchanged.

Hypotheses and conclusion, clause by clause:

- The base field is `(k : Type u) [Field k] [IsAlgClosed k]`. Algebraic closedness is the
  standing setting of the cited `def-sc-curves` and `def-sc-divisor`, not a restriction added
  to their setting. The latter's module requires exactly this hypothesis.
- The curve over k is `(C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]`.
  `IsConnectedCurve` extends `IsCurve`, hence separatedness and finite type, and includes
  connectedness, nonemptiness and dimension exactly one. `[Smooth f]` renders smoothness.
- Proper or not: there is no properness binder, projectivity binder, or affine binder.
- `Cl(C)` is the recorded `Scheme.DivisorClassGroup`, not another quotient.
  Its integral and Noetherian instance arguments are explicitly supplied by
  `(C.smooth_connected_curve_local_rings k f).choose` and
  `isNoetherian_of_locallyOfFiniteType f`. These are consequences, not assumptions.
- `∃ e : ... ≃+ Additive C.Pic` states the existence of an isomorphism of abelian groups.
  The additive wrapper expresses the same tensor-product law, since `Pic.instCommGroup`
  uses multiplicative notation.
- The specified map `[D] ↦ [O_C(D)]` is rendered by `∀ D : C.Divisor` and
  `Nonempty ((fromSkeleton C.Modules).obj (e (QuotientAddGroup.mk D)).toMul.val ≅
  D.moduleOfSmoothConnectedCurve k C f)`. Equality of Picard classes is precisely
  isomorphism of the representative sheaves (`Pic.eq_ofIsInvertible_iff`). Thus this
  condition fixes the map on every divisor class; an unspecified abstract equivalence
  would not suffice. Using representatives avoids choosing an extra invertibility proof
  in the statement. Invertibility already follows from `lem-sc-divisor-module-local`.
- The parenthetical disconnected comment is componentwise application of the connected
  assertion, as explained in the node's stage-1 `split_report`; the item does not assert
  a separate global quotient formula for disconnected schemes. Apply the theorem to each
  connected curve component. No connected curve is excluded.

Declarations inspected and reused:

- `WeilConjectures.AlgebraicGeometry.Curve`: `IsCurve` and `IsConnectedCurve` (full
  class fields and docstrings inspected). The existing definition record names `IsCurve`;
  the same module gives the required connected specialization, so no replacement is needed.
- `WeilConjectures.AlgebraicGeometry.Curve.Divisor`: `Scheme.Divisor`, `Scheme.div`,
  `Scheme.principalDivisors`, `Scheme.DivisorClassGroup`; read their full definitions.
- `Sheaf.AlgebraicGeometry.DivisorModule`: `Scheme.Divisor.moduleOfSmoothConnectedCurve`
  and `associatedModule`; read its explicit sections and construction, including the
  derived integral, regular and Noetherian instances.
- `Sheaf.AlgebraicGeometry.DivisorModuleLocal`: `Scheme.Divisor.module_local`; read the
  full theorem and its docstring, which give local generators and invertibility.
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`:
  `Scheme.smooth_connected_curve_local_rings`; its chosen integral instance is used in
  the quotient type. Its already-landed node is added to `stmt_deps`, as permitted by
  STMT_DEPS MAY GAIN LANDED NODES. It was already a proof dependency.
- `Sheaf.AlgebraicGeometry.FunctionField`: `Scheme.functionFieldOfComponents`; read its
  full definition and integral-scheme clause. That clause reuses Mathlib
  `Scheme.functionField` (generic stalk), as does the divisor quotient.
- `WeilConjectures.AlgebraicGeometry.PicardFunctor`: `Scheme.Pic`, `Pic.eq_iff_nonempty_iso`;
  `WeilConjectures.AlgebraicGeometry.Picard.Group`: `Pic.instCommGroup`, `Pic.ofIsInvertible`,
  `Pic.eq_ofIsInvertible_iff` and its group-law definitions.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`;
  full local triviality definition inspected. It is used through the Picard group and the
  recorded local divisor-module theorem.

Existing-declaration searches:

- `msearch.py ... leanfinder`: "The divisor class group of a smooth connected curve is
  isomorphic to its Picard group via the associated divisor module". Eight results,
  consisting of ring class groups and Weierstrass point classes; none gives the scheme
  statement or the specified module map.
- `msearch.py ... loogle`: "DivisorClassGroup, Pic". Zero results; unknown identifier
  `DivisorClassGroup` in Mathlib.
- `msearch.py ... grep`: `DivisorClassGroup|divisorClassGroup`, Mathlib `AlgebraicGeometry`.
  Zero results.
- `msearch.py ... leansearch`: "The divisor class group of a smooth curve is its Picard
  group". Service unavailable (Internal Server Error); no verdict drawn from that search.
- `rg` of the source project and of `lean/Sheaf` for
  `lem-sc-divisor-class-curve|divisorClassGroup|DivisorClassGroup`: source
  `Curve/Picard.lean` contains `exists_divisorClassGroup_addEquiv_pic`. Read its full
  signature, docstring and the preceding `Divisor.toPic` and `Pic.ofClosedPoint`.
  It requires `SmoothOfRelativeDimension 1`, `IsCurve`, `IsIntegral`, `IsNoetherian`,
  and specifies the point-ideal-dual map, without identifying it with the explicit
  valuation-bound module newly supplied by `def-sc-divisor`. Therefore it is not recorded
  as an exact existing match. The present theorem specifies the missing identification
  and uses exactly the node's curve hypotheses.
- `rg` for the new full declaration basename in Mathlib, the source and `lean/Sheaf`:
  no collision.

Source and edge cases:

Read the node's six proof steps and source references. The local blueprint source files
are absent on this machine; inspected the cited source at
https://stacks.math.columbia.edu/tag/0BE9 (Lemma 31.28.7), including its local-UFD hypothesis
and proof of Pic-to-Cl bijectivity. The present map is its inverse on smooth curves.
The existing source project's docstring also contains the blueprint assertion and proof.
The proof docstring follows all six steps of the DAG, including the corrected inverse sign
in the injectivity argument. No statement correction is needed.

Checked zero and negative divisors, principal divisors and the zero class: the statement
quantifies over every integer-valued finitely supported divisor and identifies its actual
associated module, so none of these cases is excluded. Empty schemes and dimension-zero
schemes are excluded by the node's definition of connected curve itself. Nonproper smooth
curves and arbitrary field characteristics are included. The equivalence has no bound on
Picard classes or on divisor coefficients. All variables and universes are bound explicitly;
there are no `let`, `show`, file-local instances, or notation in the statement.

Validation: the module compiled on the server with exit code 0 in 2.0 seconds and no
warnings. `deliver2.py C1 lem-sc-divisor-class-curve --no-push` printed OK: the module compiles
and passes the preflight except for the independent second reading, which the second reader
writes. Nothing was pushed.

## Second reading by C1

I reread the node, its source place, and the complete Lean declaration independently.
The node's objects, hypotheses, and conclusion match as follows:

- The node's smooth connected curve over an algebraically closed field is rendered by
  `(k : Type u) [Field k] [IsAlgClosed k]`, `(C : Scheme.{u})`, and
  `(f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]`. `IsConnectedCurve f`
  supplies the curve, finite-type, separated, connected, nonempty, and dimension-one
  conditions; `Smooth f` supplies smoothness. No properness, projectivity, or affineness
  hypothesis is present.
- The node's divisor class group `Cl(C)` is rendered by
  `@DivisorClassGroup C (C.smooth_connected_curve_local_rings k f).choose
  (isNoetherian_of_locallyOfFiniteType f)`. The chosen integral and explicit Noetherian
  arguments are consequences of the hypotheses, and are exactly the parameters required
  by the recorded `DivisorClassGroup` abbreviation.
- The node's target `Pic(C)` and its abelian group law are rendered by `Additive C.Pic`.
  The existential `e : ... ≃+ Additive C.Pic` is therefore an additive-group isomorphism.
- The map clause `D ↦ [O_C(D)]` is rendered for every `D : C.Divisor` by
  `Nonempty ((fromSkeleton C.Modules).obj (e (QuotientAddGroup.mk D)).toMul.val ≅
  D.moduleOfSmoothConnectedCurve k C f)`. This identifies the image of each divisor
  class with the explicitly recorded associated module, rather than leaving the map
  unspecified. `moduleOfSmoothConnectedCurve` is the node's `O_C(D)` construction and
  uses no additional assumptions.
- Quantifier order is preserved: field and curve data precede the existential equivalence,
  which precedes the universal divisor condition. There are no additional clauses.

The source (Stacks 0BE9, with 0BE8 for injectivity) assumes a smooth integral curve with
local UFD/DVR rings; the project's `IsConnectedCurve` plus `Smooth` hypotheses and the
local-rings dependency provide precisely those consequences. The source allows proper and
nonproper curves, and the Lean statement has no properness condition. Zero and negative
divisors, principal divisors, and the zero class are included by the unrestricted
`C.Divisor` quantifier. Empty and dimension-zero schemes are excluded exactly by
`IsConnectedCurve`; arbitrary characteristic is allowed. The sole universe `u` is shared
by the field, scheme, and morphism, so no case is lost through an independent universe.

I searched Mathlib, the source project, and `lean/Sheaf` by declaration name and by
`DivisorClassGroup`/`Pic` concepts (LeanSearch, Loogle/LeanFinder, and grep). The source
has `exists_divisorClassGroup_addEquiv_pic`, but it uses `Divisor.toPic` (point-ideal duals)
and does not identify the map with the explicit valuation-bound module required here, so it
is not an exact existing declaration. No exact Mathlib or project declaration exists.

No mismatch was found. In particular, the explicit integral and Noetherian instance
arguments are derived witnesses rather than extra hypotheses, and the representative
isomorphism is the appropriate Lean rendering of the node's class assignment. The module
already compiles cleanly with only the theorem's required `sorry`; no source or node edits
were necessary.
