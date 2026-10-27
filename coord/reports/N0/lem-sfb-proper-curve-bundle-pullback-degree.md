## Worker report

The module `Sheaf.AlgebraicGeometry.ProperCurveBundlePullbackDegree` states
`AlgebraicGeometry.Scheme.Modules.proper_curve_bundle_pullback_degree` with a single
`sorry` proof. It adds no definition and changes only the item's `lean` record.
The existing Q26 delivery was a stage-1 split, not a Lean attachment: the live node
has a reviewed seven-step proof but no `lean` field. This delivery supplies that
missing stage-2 statement. The sandbox initially contained only dispatcher briefs.

The source read is Stacks Project, `literature/stacks-project/varieties.tex`,
`lemma-degree-pullback-map-proper-curves` (Tag 0AYZ), including its proof, and the
recorded definitions. The node is its rank-one case. Its natural-language statement
needs no correction and is preserved verbatim.

Hypotheses and clauses, individually:

| Node | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]`. |
| X and Y are k-schemes | `(X Y : Scheme.{u})` and their `Over (Spec (.of k))` instances. |
| Each is separated, integral, of finite type and dimension exactly one | The two `IsIntegralCurve` instances. The recorded class extends `IsVariety`, whose fields supply integrality, separatedness, locally finite type and quasi-compactness; its own field is `topologicalKrullDim_eq_one`. |
| X and Y are proper over k | The two `IsProper` instances on the structure morphisms. |
| f is a morphism X to Y over k | `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`. |
| f is dominant, i.e. has dense image | `[IsDominant f]`. |
| The induced extension of function fields is finite | `hfinite : (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.Finite`. This is finiteness for the actual generic stalk homomorphism. Dominance identifies the image of the source generic point with the target generic point. No independently chosen field embedding or algebra structure is assumed. |
| d equals [k(X):k(Y)], the k(Y)-dimension of k(X) | `@Module.finrank Y.functionField X.functionField _ _ (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.toAlgebra.toModule`. The module instance is explicitly the one from that same canonical ring homomorphism. Under `hfinite`, finrank is the finite dimension, not its infinite-dimensional default zero. |
| Every invertible O_Y-module M | `(M : Y.Modules) [M.IsInvertible]`. |
| f* is module pullback | `(tensorPullback f).obj M`, the existing explicit inverse-image/change-of-rings/sheafification functor from the recorded pullback dependency. |
| Both degrees are chi(N) - chi(O) | `.degree k` is the recorded `Scheme.Modules.degree` on each scheme; its body is exactly the difference of the recorded Euler characteristics. |
| chi is coherent Euler characteristic | The existing `Scheme.Modules.eulerChar` is the alternating `finsum` of cohomology finranks. On these proper finite-type integral curves and invertible modules, coherence, finite cohomology and eventual vanishing give its usual meaning. |
| deg_k(f* M) = d deg_k(M) | The conclusion equates `((tensorPullback f).obj M).degree k` with the displayed canonical finrank, cast to integers, times `M.degree k`. |

The field and schemes use one arbitrary universe `u`, matching the recorded scheme,
cohomology and curve interfaces; no site universes are equated. All variables and
universes are explicit, with both `autoImplicit` and `relaxedAutoImplicit` disabled.
There is no `let` or hidden `show` binder in the statement. The theorem docstring
contains all seven proof steps and the node identifiers they use, including the
local-basis construction and compatibility of the projection formula in step 4.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs` (available through
  the public statement imports).
- `def-pc-curve`: `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`,
  `AlgebraicGeometry.IsVariety` and `AlgebraicGeometry.IsIntegralCurve`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (including its separated/universally-closed fields).
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`, whose
  documentation explicitly delegates the integral-scheme clause to Mathlib
  `AlgebraicGeometry.Scheme.functionField`, the generic local ring.
- For the induced map, the existing helper
  `AlgebraicGeometry.Scheme.Hom.functionFieldMap` in
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, and
  `AlgebraicGeometry.Scheme.Hom.apply_genericPoint_of_isDominant` in its public
  dependency `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.
  The helper's definition is stalk transport along generic-point equality followed
  by `f.stalkMap`, and has no flatness assumption.
- `def-pc-field-tower`: `Sheaf.FieldTheory.FieldTower`, `FieldExtension.degree`;
  its documented finite branch is `Module.finrank`, the expression used here.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (local triviality).
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, with the publicly
  imported `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. The repaired normalized
  adjunction interface is imported as recorded; no second pullback is defined.
- `def-pc-degree-line-bundle`:
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`,
  `AlgebraicGeometry.Scheme.Modules.degree`.
- `def-pc-euler-characteristic`:
  `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`,
  `AlgebraicGeometry.Scheme.Modules.eulerChar` and `finrankH`.

Public imports give the statement dependencies. Plain imports give all currently
stated proof dependencies, including the Mathlib proper/locally-quasi-finite
finiteness, Noetherianity, finite morphisms, coherence and affine-cohomology modules,
the explicit-tensor invertibility theorem, and the generic-rank Euler formula.
`lem-sfb-finite-dominant-generic-pushforward-stalk` is a proof dependency without a
recorded declaration in the read clone; it is not needed to type this statement,
and no unpublished module is invented or imported for it. Its future import can
be added when that proof dependency is stated.

Edge cases checked before drafting:

- Identity: the canonical field map is identity, d = 1 and the equality becomes
  degree invariance under the canonical identity tensor pullback.
- The structure module, or any degree-zero invertible module: both sides are zero.
  Negative degrees are retained since the result is an equality in integers.
- Singular integral proper curves, including a normalization map, are allowed:
  neither smoothness nor regularity nor flatness is assumed.
- Purely inseparable nonconstant maps, e.g. Frobenius on P1 over F_p, retain degree p;
  there is no separability or characteristic restriction.
- Arbitrary non-algebraically-closed fields and non-geometrically-integral proper
  curves are included. The degree uses the specified base field k on both sides.
- The empty scheme and dimension-zero schemes are correctly excluded by
  `IsIntegralCurve`, just as in the node. Zero rank bundles are excluded by local
  rank-one invertibility; no positivity or nonzero-degree hypothesis is added.
- Constant maps are excluded by dominance to an integral dimension-one target.
  Finite field extensions have positive dimension; the artificial zero value of
  finrank on infinite extensions is excluded by `hfinite`.

Searches for an existing statement:

- `msearch.py` LeanFinder: "The degree of an invertible sheaf pulled back along a
  dominant map of proper integral curves equals the function field degree times
  its degree". Eight hits: dominant-map composition and rational maps/function
  fields, plus a Weierstrass point-map lemma; none states the formula.
- `msearch.py` Loogle: `"degree", "pullback"`. Zero hits.
- `msearch.py` Mathlib grep:
  `degree.*pullback|pullback.*degree|degree.*invertible` in `AlgebraicGeometry`.
  Zero hits.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for degree/pullback and
  induced-function-field declarations, and for the blueprint identifier and the
  proposed theorem name. No existing exact statement or name collision.
- Read the relevant near-matches in full:
  `Scheme.Hom.degree_pullback` in `Modules.Ample` requires an ample invertible
  module and uses a general-dimensional forward-difference degree;
  `Scheme.Divisor.degree_pullback_eq_finrank_functionField_mul` in
  `Curve.DivisorPullback` concerns divisors on smooth curves over an algebraically
  closed field with a finite flat map; `Modules.degree_pullback` in
  `Cohomology.EulerChar` concerns field base change rather than a map of curves.
  None has exactly this statement. The induced function-field map in
  `Curve.DivisorPullback` is reused rather than reconstructed.

No statement dispute, new nodes, or dependency-record repairs are needed.

Validation: the prescribed `scompile.py N0 lem-sfb-proper-curve-bundle-pullback-degree`
compiled the module successfully in sandbox and library modes (3.2 and 3.1 seconds),
with no errors or unexpected warnings. The required `deliver2.py --no-push`
completed successfully: `OK (dry run): commit e5785c612be passes the preflight and
compiles; nothing pushed`. The packet contains exactly the item node, its module
and this report. The final delivery repeats the server checks before pushing.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
