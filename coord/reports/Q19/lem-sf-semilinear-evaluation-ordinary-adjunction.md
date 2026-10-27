## Worker report

The delivery states `AlgebraicGeometry.ProEtale.SemilinearProperOpen.semilinearEvaluationOrdinaryAdjunction`
in `Sheaf.SixFunctors.SemilinearEvaluationOrdinaryAdjunction`. Its sole proof is `sorry`.
It combines the normalization assertions without redefining any system category, operation,
evaluation functor, adjunction, or mate. The node's mathematical fields are unchanged.

Hypotheses and objects, clause by clause:

- Arbitrary commutative rings and inverse transitions are the explicit binders
  `C : ℕ → CommRingCat.{u + 1}` and `τ : ∀ n : ℕ, C (n + 1) ⟶ C n`.
  No surjectivity, flatness, finiteness, or cartesianness assumption is imposed.
- The scheme morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y)`; `(n : ℕ)` is unrestricted.
  The sites remain the recorded small pro-etale sites, with object universe u+1,
  morphism universe u, and coefficient/module universe u+1. No equality of these
  universes or derived localization hypothesis is imposed.
- The strict semilinear category is the existing `Modules C τ X`, which abbreviates
  `SemilinearSections.Systems` for the actual vertical coefficient ring. The target
  constant-coefficient tower category is the existing `StrictTower.Towers (C n) X`.
- The existing `levelTower C τ n X` is literally `SemilinearSections.evaluation ... n ⋙
  Functor.const ℕᵒᵖ`, so it is precisely the specified E^0, not a diagram of derived objects.
- `∃ D : push C τ f ⋙ levelTower C τ n Y ≅ levelTower C τ n X ⋙
  StrictTower.towerDirectImage (C n) f` has the displayed direction in the node.
  The first two conjuncts say, using `HEq` of actual functions, that both `D.hom` and
  `D.inv` at every system M, tower index m, and site object H are the identity on
  `M.val.obj (op (n, (proEtaleBaseChange f).obj H))`, namely M_n(H ×_Y X).
  Heterogeneous equality is needed only for the definitionally different coefficient
  presentations of the same section groups; it does not weaken identity on sections.
- The third conjunct quantifies over every competing natural isomorphism D' with the
  hom normalization alone and concludes `D' = D`. In particular uniqueness is solely
  from the prescribed sections, not from additional unit or mate properties.
- The next conjunct identifies the *existing* `evalPullInv C τ n f` with the inverse
  of the Mathlib `mateEquiv` applied to `D.hom`, for the specified `ordinaryAdj` and
  the specified level ring-module adjunction whiskered by ℕᵒᵖ. This is the node's
  inverse adjunction mate, retaining its units rather than an arbitrary isomorphism.
- `IsIso (evalPullInv C τ n f)` is invertibility on the entire ordinary category.
- `∃! b` is the single-level inverse-image evaluation comparison, oriented from
  level pullback after evaluation on Y to evaluation after system pullback.
  Its determining property is exactly the single-level unit equation: the level
  unit followed by the level direct image of `b.hom.app M` equals evaluation of
  the system unit followed by the zeroth tower component of `D.hom`.
  Zeroth tower evaluation here recovers the actual single-level direct comparison;
  all tower components agree by their section normalization. Uniqueness is of the
  whole natural isomorphism for this equation alone.
- The following universal conjunct applies to every b satisfying that same unit
  equation and asserts `((evalPullInv C τ n f).app M).app (op m) = b.hom.app M`
  for every M and every m. This is the constant-diagram lift with the canonical
  compositors: `Functor.constComp` has identity components, as does the canonical
  reassociation. Since tower morphisms are determined by all their components,
  this specifies equality of the actual natural transformations, including tower
  transition naturality. It does not replace the compositor with a false
  definitional equality of constant functors.
- The penultimate conjunct is exactly the displayed tower unit equation, in Lean's
  left-to-right composition order: tower unit, then tower direct image of a, equals
  E^0 applied to the system unit, then D at the system pullback.
- The final conjunct is exactly the consequent counit equation in proof step 6:
  a at the system direct image followed by E^0 of the system counit equals tower
  pullback of D followed by the specified tower counit.
- D and b are natural isomorphisms of full functors, and a is the recorded natural
  transformation, so naturality is for every ordinary system morphism, not a
  bounded, cartesian, constructible, or otherwise restricted subcategory.

Dependency declarations read and used:

- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`:
  `AlgebraicGeometry.ProEtale.SemilinearProperOpen.Modules`, `coefficients`,
  `transition`, `push`, `pull`, `ordinaryAdj`, `levelTower`, `evalPullInv`,
  `evalPushOrdinary_existsUnique`, and `evalPullInv_isIso`.
  The last two establish parts of the package already; they do not publicly state
  its single-level lift and both unit/counit equations. Those constructions are
  reused, not copied into new definitions.
- `Sheaf.Paper.SemilinearSystemModels`:
  `WeilConjectures.SemilinearSections.Systems` and `evaluation`, the recorded
  vertical-slice functor with the identity coefficient identification.
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`:
  `AlgebraicGeometry.ProEtale.StrictTower.Towers`, `coefficients`, `modulePullback`,
  `moduleDirectImage`, `towerPullback`, `towerDirectImage`, and `constantRingIso`.
  These are the actual termwise functors and canonical constant-ring comparison.
- The Mathlib leaf `def-weil-pbc-adjunction-mate` uses its `mathlib_match`,
  `CategoryTheory.mateEquiv` in `Mathlib.CategoryTheory.Adjunction.Mates`.
  Its inverse has exactly the unit/D/counit formula used here. The module imports
  this directly and also `Mathlib.CategoryTheory.Adjunction.Whiskering`.
- The Mathlib scheme leaf is `AlgebraicGeometry.Scheme` in
  `Mathlib.AlgebraicGeometry.Scheme`, and scheme morphisms are `X ⟶ Y`.
- Proof-only imports include the recorded ring-square module and its
  `semilinearEvaluationRingSquare` and `evaluationPush`; the constant-left-module
  theorem `CategoryTheory.constant_left_module_inverse_image`; the module
  adjunction theorem `SheafOfModules.module_pullback_pushforward_adjunction`;
  `CategoryTheory.Adjunction.liftsGroupRingObjects`; the recorded pro-etale
  inverse-image and constant-coefficient operation modules; and Mathlib's
  `CategoryTheory.constantSheaf`. These support the six-step proof docstring.

Source checks: read `literature/stacks-project/sites-modules.tex`, label
`lemma-adjoint-pullback-pushforward-modules` (Tag 03D7), its tensor/restriction
adjunction proof; the current blueprint's `fix-prop-coherence.proof.md`; and the
full ordinary comparison/mate argument in `SemilinearProperOpenMatePasting`,
lines 1685–1911. This node is an agent-formulated refinement, as its source says.
No statement correction or disputed statement is needed.

Edge cases checked before writing: n=0, m=0 and arbitrary m; zero coefficient
rings, infinite coefficient rings, arbitrary nonsurjective or nonflat coefficient
transitions, zero systems, empty schemes, and identity scheme morphisms. The
identity-on-sections and unit characterizations make sense in each case, and the
componentwise inverse-image proof never requires a coefficient lift or tensor
exactness of a transition. No test index type or extra universe bound is added.

Searches (2026-10-22):

- `msearch.py ... leanfinder "Evaluation of strict semilinear systems commutes with
  direct image and its inverse pullback mate is invertible"`: eight results,
  including `LinearEquiv.toLinearMap_symm_comp_eq`, `Module.apply_evalEquiv_symm_apply`
  and unrelated Profinite lemmas; no matching system statement.
- `msearch.py ... loogle "CategoryTheory.Adjunction.whiskerRight"`: finds the
  whiskered adjunction and its component unit/counit formulas, not this statement.
- `msearch.py ... grep "evalPushOrdinary|evalPullInv|moduleEvalG"`: no Mathlib match.
- `msearch.py ... leansearch "Evaluation followed by a constant tower commutes with
  direct image and pullback on semilinear module systems"`: eight results including
  `SheafOfModules.evaluation`, `PresheafOfModules.evaluation`, and
  `ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.evalAt`; no matching statement.
- `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `evalPushOrdinary|evalPullInv|moduleEvalG|lem-sf-semilinear-evaluation-ordinary-adjunction`:
  the recorded SemilinearProperOpenMatePasting comparisons and varying-ring level
  comparisons are present; there is no public declaration giving this complete
  ordinary package with the specified system adjunction and both equations.
  In particular the useful `eval_pull_mate_isIso` and `constant_diagram_mate`
  proof helpers are private; they are not introduced as new notions here.
- `rg -n "semilinearEvaluationOrdinaryAdjunction"` in Mathlib and both project
  source roots: no existing declaration with the chosen name.

Validation: every compiler invocation uses the prescribed `scompile.py` on the
single module, in module mode. The first check exposed the missing constant-diagram
compositor; the final formulation checks the equal components at every index.
The prescribed delivery dry run and final delivery follow after the clean compile.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
