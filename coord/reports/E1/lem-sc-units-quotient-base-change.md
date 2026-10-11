## Worker report

The module states AlgebraicGeometry.units_quotient_base_change, with sorry as its only
proof. It asserts an isomorphism of the two unit groups modulo nth powers and specifies
its value on every unit class; thus the isomorphism is the pullback-induced map.
No new notions, dependency modules, or statement corrections are needed.

Clause-by-clause correspondence:
- The extension k ⊆ k' is `(k k' : Type u) [Field k] [Field k'] [Algebra k k']`.
  A unital map from a field to a field is injective, so no additional inclusion data are needed.
  Both algebraic-closedness assumptions are `[IsAlgClosed k] [IsAlgClosed k']`.
- The curve and its structure map are `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`.
  `[IsConnectedCurve f]` includes separatedness, finite type, nonemptiness, connectedness,
  and dimension exactly one; `[Smooth f]` and `[IsAffine C]` give smoothness and affineness.
- The integer and positivity condition are `(n : ℕ) (hn : 1 ≤ n)`.
- The base-changed scheme is `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))`;
  its projection to C is `pullback.fst f ...`.
- Global rings are `Γ(C, ⊤)` and `Γ(pullback f ..., ⊤)`; their unit groups use `ˣ`.
  The image subgroup `(powMonoidHom n : G →* G).range` is exactly the subgroup of nth powers.
  `G ⧸ ...` is the Mathlib quotient group; commutativity makes the subgroup normal.
- `∃ e : ... ≃* ...` says the quotient groups are isomorphic. The universally quantified
  equation `e (QuotientGroup.mk a) = QuotientGroup.mk (Units.map ... a)` specifies the map
  on every representative. Here the ring pullback is the projection's `appTop.hom`, and
  `Units.map` induces the map on units. Quotient projection is surjective, so this condition
  specifies the induced map uniquely, rather than asserting an unrelated isomorphism.

Dependencies read:
- def-sc-curves: WeilConjectures.AlgebraicGeometry.Curve, AlgebraicGeometry.IsCurve and
  AlgebraicGeometry.IsConnectedCurve; the latter is used directly in the statement.
- def-sc-field-extension: its recorded bundle specifies Limits.pullback and pullback.fst;
  those are used directly. Etale.cohomologyMap and Etale.upperStar are irrelevant to this
  statement about global units, so their module is not imported.
- def-sc-divisor: Sheaf.AlgebraicGeometry.DivisorModule, including
  Scheme.Divisor.moduleOfSmoothConnectedCurve and the source divisor declarations.
- lem-sc-compactification: WeilConjectures.AlgebraicGeometry.Curve.Compactification,
  IsConnectedCurve.exists_smooth_properCompactification.
- lem-sc-global-functions: WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective,
  Scheme.GlobalSectionsBijective.of_isAlgClosed.
- lem-sc-affine-unit-divisor-base-change: Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange,
  AlgebraicGeometry.affine_unit_divisor_base_change.
The final four dependencies supply the docstring proof, not notions in the signature;
therefore their imports are unnecessary at this statement-only stage.

Edge cases checked before writing: n=1 gives trivial quotient groups; n=0 is expressly
excluded by the node. No invertibility or prime-to-characteristic hypothesis is added:
constants have nth roots even in characteristic dividing n. Empty schemes and points are
excluded by the node's connected-curve definition itself. The identity field extension
induces the identity map on quotient classes. Nonconstant units, for example on G_m,
are retained by the quotient: the condition is not an assertion that all units are powers.
All fields and schemes share an arbitrary universe u, as in the recorded base-change
conventions; any given fields and curve can be placed in a common universe.

Searches for an existing statement:
- LeanFinder via msearch.py: "pullback induces an isomorphism on units modulo nth powers
  for a smooth affine connected curve under extension of algebraically closed fields";
  eight unrelated Weierstrass-curve hits, no match.
- Loogle via msearch.py: "QuotientGroup.mk, powMonoidHom"; two generic quotient/Selmer
  results, no curve base-change result.
- LeanSearch via msearch.py: "Units modulo nth powers invariant under algebraically
  closed base extension of a smooth affine curve"; unavailable, Internal Server Error.
- Mathlib grep via msearch.py: "units.*quotient|quotient.*units" in AlgebraicGeometry.
  Direct rg over Mathlib AlgebraicGeometry with quotient/baseChange and units/quotient
  patterns found no matching statement.
- rg over WeilConjectures and lean/Sheaf for the node id, units_quotient/base_change,
  and quotient/unit patterns found the source theorem IsConnectedCurve.finite_units_quotient
  (Curve/Affine.lean), which proves finiteness only, and our ConstantInvariance docstring
  citing this node. Neither states this isomorphism. No duplicate definition is introduced.

The source proof is reproduced step by step in the theorem docstring from the node's
source-tagged proof. The referenced blueprint Markdown is not materialized in this local
read-only checkout; the node retains its exact source document and place. No node fault
or statement dispute was found.

## Second reading by E1

I independently read the node `lem-sc-units-quotient-base-change`, its dependency
signatures, and `UnitsQuotientBaseChange.lean`. The correspondence is as follows.

- The node's algebraically closed extension `k ⊂ k'` is rendered by
  `(k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
  [Algebra k k']`. For fields, the unital algebra map is the required inclusion;
  no stronger embedding or finite extension assumption is introduced. Verdict: exact.
- The smooth affine connected curve over `k` is rendered by
  `(C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
  [IsAffine C]`. `IsConnectedCurve` supplies the curve's separated finite-type and
  dimension-one conditions together with connectedness; the other two instances supply
  smoothness and affineness. Verdict: exact.
- The integer hypothesis `n ≥ 1` is exactly `(n : ℕ) (hn : 1 ≤ n)`. Verdict: exact.
- The base change `C_{k'}` is the displayed
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))` and its projection is
  `pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))`. These are the
  recorded pullback notions from `def-sc-field-extension`, not private aliases.
  Verdict: exact.
- The two groups are the unit groups of `Γ(C, ⊤)` and of the base-changed global
  sections, each quotiented by
  `(powMonoidHom n).range`, the subgroup of nth powers. Verdict: exact.
- The conclusion is `∃ e : ... ≃* ...`, followed in the same order by
  `∀ a : Γ(C, ⊤)ˣ, e (QuotientGroup.mk a) = QuotientGroup.mk (Units.map ... a)`.
  This both asserts the isomorphism and identifies it with pullback on every class,
  matching the node's phrase “pullback induces”. Verdict: exact.

No hypotheses or conclusion clauses were added, dropped, strengthened, or weakened.
The file has no unbound variables (`set_option autoImplicit false`) and the sole proof is
`sorry`, as required for a stage-2 statement.

Edge cases reviewed: `n = 1` is allowed and gives the expected trivial power quotient;
`n = 0` is excluded exactly by `hn`; characteristic dividing `n` is allowed; identity
field extensions give the identity pullback; nonconstant units are not silently removed;
and empty or zero-dimensional schemes are excluded by `IsConnectedCurve`, as in the
node's connected-curve definition. The common universe `u` is the universe forced by the
scheme morphism to `Spec k` and does not introduce an extra restriction beyond that
encoding.

I repeated the existing-definition searches (LeanFinder, Loogle, LeanSearch, and grep
over Mathlib, `WeilConjectures`, and `lean/Sheaf`) for units, quotient groups, and affine
curve base change. They found only generic quotient APIs and the unrelated finiteness
lemma `IsConnectedCurve.finite_units_quotient`; no declaration states this isomorphism.
Thus no existing declaration applies and no duplicate notion or dependency module is
needed. The module compiled cleanly with `scompile.py`; no mismatch was found and no
file or node change was necessary beyond recording the statement.
