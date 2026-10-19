## Worker report

The module [FixedObjectPushoutComparison.lean](lean/Sheaf/AlgebraicTopology/FixedObjectPushoutComparison.lean)
adds the helper `SSet.Bergner.fixedArrowAdjunct` and states
`SSet.Bergner.fixed_object_pushout_comparison` with `sorry` as its complete proof.
The helper is the adjunct of `h` under the recorded
`SSet.Bergner.fixed_object_free_arrow_adjunction`; its data is obtained by the
adjunction and is determined by the universal property.

The theorem quantifies a small object type `O`, endpoints `a b : O` (with no
inequality), simplicial sets `K L`, an arbitrary map `i : K ⟶ L`, a fixed-object
simplicial category `C : Fixed O`, and `h : K ⟶ C.Hom a b`. It existentially
provides `P : Fixed O`, the fixed pushout legs `j` and `v`, and their commutativity
proof. `Nonempty (IsColimit (PushoutCocone.mk ...))` renders the fixed-object
pushout clause. For each target `T`, the first conjunct states that every map out
of `P` restricts to a compatible pair; the second gives existence and uniqueness
of an extension for every compatible `(G, ell)`. The third conjunct states
postcomposition compatibility, and the fourth repeats the extension property
with a prescribed object function `f : O → T`. `HEq` records the generator map
when the target endpoint types are presented through the two object maps.

The dependency declarations used are:

- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`,
  `SSet.Bergner.Fixed`, `SSet.Bergner.U`, and the fixed-object category structures;
- `Sheaf.AlgebraicTopology.FixedObjectFreeArrowAdjunction`,
  `SSet.Bergner.freeArrow`, `SSet.Bergner.freeArrowMap`,
  `SSet.Bergner.freeArrowFunctor`, `SSet.Bergner.mappingSetEvaluation`, and
  `SSet.Bergner.fixed_object_free_arrow_adjunction`;
- Mathlib `CategoryTheory.Limits.PushoutCocone`, `PushoutCocone.mk`,
  `CategoryTheory.Limits.IsColimit`, and `CategoryTheory.CoherentNerve.SCat`.

Edge cases checked against the source statement are: `a = b` is permitted (the
free-arrow construction retains loop generators); `i` is arbitrary, including
empty and non-injective maps; no Kan hypothesis is present; and `O` may be empty
(the theorem has no nonemptiness assumption). The fixed-object carrier `P :
Fixed O` gives the canonical object set `O`, while the target object function is
arbitrary and need not be injective.

Searches made before writing:

- `msearch.py ... leanfinder` for “pushout of a free arrow attachment in a fixed
  object simplicial category is also the pushout with arbitrary object functions”:
  only ordinary small-object and Cech pushout declarations matched; none had the
  enriched fixed/variable comparison.
- `msearch.py ... leanfinder` for “inclusion of O-object simplicial categories
  preserves pushouts”: hits were `SimplicialThickening`, `SSet.hasColimits`, and
  `CategoryTheory.SimplicialObject`; no matching assertion.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` for
  `fixed-object pushout`, `freeArrow`, `sCat_O`, and
  `lem-coef-scat-fixed-object-pushout-comparison`: the free-arrow and interval
  dependency modules were present, but no comparison statement.
- `grep -rl` over `dag/nodes/` confirmed this node is the sole occurrence of its
  id and no existing node carries the comparison notion.

No `STATEMENT-DISPUTED` flag or node correction is required.

## Second reading by Q157

I reread the source node, all three dependency records, and the complete Lean
signature. The binders match the node hypothesis by hypothesis: `O`, possibly
coincident `a,b`, arbitrary `i`, `C`, and `h` are all present. The fixed pushout
is rendered by `P`, `j`, `v`, `comm`, and `Nonempty (IsColimit ...)`; the variable
pushout is rendered by the restriction compatibility, extension uniqueness,
postcomposition equation, and prescribed-object-function clause. No injectivity,
endpoint distinctness, or Kan assumptions were added. The helper uses the
recorded free-arrow adjunction rather than redefining it. Compilation via
`scompile.py` produced no errors or warnings after shortening the two long lines.
