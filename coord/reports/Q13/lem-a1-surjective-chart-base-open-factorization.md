## Worker report

The module `Sheaf.AlgebraicGeometry.SurjectiveChartBaseOpenFactorization` states
`AlgebraicGeometry.AlgebraicSpace.surjective_chart_base_open_factorization`.
Its sole theorem has proof `by sorry`; it introduces no definitions or axioms.
The node is unchanged except for `lean`.

Source read: `literature/stacks-project/spaces-properties.tex`, Tag 03FY,
`lemma-union-of-quasi-compact`, lines 726–745. The final sentence descends mapping
into a base affine open along a surjection. The node expands precisely that
argument to any open immersion and representable surjective scheme chart.
The proof docstring includes all five recorded proof steps, using scheme-test
representability, the point chase, unique scheme open factorization, naturality,
and the construction on sections. No assertion of affineness or étaleness is needed.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Base scheme S, size convention | `{S : Scheme.{u}}`, explicit `universe u`; all schemes/tests use that universe and the recorded algebraic-space universe |
| Algebraic space Y over S | `(Y : AlgebraicSpace S)` |
| S-scheme U | `(U : Over S)`, whose structural map is `U.hom` |
| Morphism q from h_U to Y | `(q : yoneda.obj U ⟶ Y.obj.obj)` |
| q representable and surjective in the scheme-test sense | `(hq : IsSurjective q)`; this recorded predicate includes representing scheme pullbacks and surjective projections, hence already implies representability |
| Any open subscheme W with inclusion j | `(W : Scheme.{u}) (j : W ⟶ S) [IsOpenImmersion j]`; an open immersion identifies W with its open image, exactly the open-subscheme description of def-weil-open-immersion |
| U's structural map factors through j | `(hU : ∃ c : U.left ⟶ W, c ≫ j = U.hom)` |
| Natural transformation b : Y to h_W | `∃ b : Y.obj.obj ⟶ yoneda.obj (Over.mk j)` |
| Composite with h_j is the structural transformation | First conjunct: `b ≫ yoneda.map (Over.mkIdTerminal.from (Over.mk j)) = ((Over.mkIdTerminal (X := S)).isTerminalObj yoneda _).from Y.obj.obj` |
| Uniqueness of this factorization | Second conjunct universally quantifies `b'`, assumes the same structural factorization equation, and concludes `b' = b` |
| Every scheme test a : h_T to Y | Third conjunct quantifies `(T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj)` |
| Scheme lift b_a of T to W | `(yoneda.preimage (a ≫ b)).left`; the scheme map underlying the Yoneda preimage in Over S |
| j composed with b_a is T's structural map | `(yoneda.preimage (a ≫ b)).left ≫ j = T.hom` |
| Uniqueness of b_a | `∀ c : T.left ⟶ W, c ≫ j = T.hom → c = (yoneda.preimage (a ≫ b)).left` |
| Compatibility for every test morphism r : T' to T | Last conjunct quantifies `T T' r a` and gives `(yoneda.preimage ((yoneda.map r ≫ a) ≫ b)).left = r.left ≫ (yoneda.preimage (a ≫ b)).left` |
| These factorizations define b | The lifts are the Yoneda preimages of `a ≫ b` itself, so the displayed natural transformation induces exactly the displayed lifts |
| No affineness or étaleness assumptions | Neither `IsAffine` nor `IsEtale` occurs in the signature |

The represented base `h_S = yoneda.obj (Over.mk (𝟙 S))` is terminal because
`Over.mkIdTerminal` is terminal and Yoneda preserves terminal objects.
`Over.mkIdTerminal.from (Over.mk j)` has underlying scheme morphism j
(`Over.mkIdTerminal_from_left`), so its Yoneda image is exactly h_j.
The terminal object's map from Y is the canonical structural transformation,
not an arbitrary additionally assumed map. No duplicate structural-map definition
is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsSurjective`, and its defining `IsRepresentableWith`.
  Read the full signatures and docstrings in the recorded module.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
  Also read the proof dependency's exact Mathlib matches `IsOpenImmersion.lift`,
  `lift_fac`, and `lift_uniq`, lines 694–712; the module is already imported for
  the statement, so no separate proof-only import is necessary.
- `def-weil-size-convention` is a recorded metatheoretic convention, not a missing
  declaration. Its role is fulfilled by the explicit universe u and the exact
  universe-polymorphic dependency interface, without a further size assumption.
- `Mathlib.CategoryTheory.Limits.Yoneda` supplies Yoneda limit preservation;
  `CategoryTheory.Over.mkIdTerminal` and `Limits.IsTerminal.isTerminalObj`
  provide the canonical structural map used in the conclusion.

Edge cases checked before writing:

- W = S and j = identity: b is the structural transformation, and every lift
  is the structural map of its test; no proper-open condition was added.
- W empty: hU forces U empty. Surjectivity of every pullback then forces any
  test admitting a map to Y to be empty. Thus the factorization is valid,
  including for the empty algebraic space; no nonemptiness assumption was added.
- Empty U and empty Y are permitted. An empty chart cannot be representably
  surjective onto a nonempty test, so the hypothesis has its correct strength.
- Nonreduced test schemes: only image containment is deduced pointwise; the
  resulting scheme morphism is the actual open-immersion lift, so nilpotents
  are retained. This is not an assertion about factorization through a closed set.
- U and W nonaffine, and q nonétale: all are allowed. Only representability,
  scheme-projection surjectivity, and open immersion enter the argument.
- Arbitrary test morphisms over S are included, not merely étale maps or covers.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “Factorization of an algebraic space structure
  morphism through a base open subscheme descends along a representable
  surjective scheme chart”. Eight hits; these concern scheme image maps,
  local representability, or the scheme-only `IsOpenImmersion.lift` API.
  None states the algebraic-space descent assertion.
- `msearch.py ... loogle`: `"AlgebraicSpace", "IsOpenImmersion"`.
  Zero hits.
- `msearch.py ... leansearch`: “An algebraic space maps into a base open
  subscheme if a representable surjective scheme chart does”. Eight hits;
  scheme open immersions and restrictions, no algebraic-space statement.
- `msearch.py ... grep`: `AlgebraicSpace|factor.*[Oo]pen|[Oo]pen.*factor`,
  subdirectory `AlgebraicGeometry`. One hit in Morphisms/Immersion, unrelated.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` for `AlgebraicSpace`,
  `baseOpenFactor`, and `base_open_factor`: no matching declaration.
  `grep -rn` for this node id in all of `lean/WeilConjectures`: no hits.
  Broader `rg` in SixFunctors found extension-by-zero and smooth-duality open
  factorizations, all for schemes, not this statement.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for base/open factorization,
  representable surjections and Yoneda maps found the existing algebraic-space
  framework and `AlgebraicSpaceAffineAtlasOpenCover`. The latter consumes the
  same argument within an affine-cover existence assertion; it does not state
  this general unique factorization result.
- `rg` across `lean/Sheaf`, `lean/WeilConjectures`, and
  `dag/lean_names_upstream.json` for `base_open_factorization`,
  `surjective_chart_base`, and `baseOpenFactorization`: no duplicate name.

Validation: prescribed `scompile.py Q13 lem-a1-surjective-chart-base-open-factorization`
compiled the delivered module successfully in both sandbox and library module
contexts (1.9 s and 5.6 s). No errors or unexpected warnings. All variables are
explicitly bound and `set_option autoImplicit false` is enabled. Maximum line
width is below 101 characters. The report's delivery validation is completed by
the required `deliver2.py --no-push` and final delivery.

No statement correction, dependency repair, new node, or disputed statement.

## Second reading by Q13

Single-worker self-check; the dispatcher's brief reserves the independent review
for the maintainer, and prohibits starting another agent. I reopened the node and
module and compared every binder and conjunct as tabulated above. In particular:
`IsSurjective` already includes representability; the test maps live in Over S;
W is represented by `Over.mk j`; the terminal map is canonical; both uniqueness
clauses are unconditional once the relevant factorization equation is assumed;
and the final conjunct handles every r with the correct contravariant Yoneda
composition. The lifts are induced by the same b, rather than an unrelated
family chosen alongside it. No mismatch was found and no change to the accepted
statement or its dependency list was needed.
