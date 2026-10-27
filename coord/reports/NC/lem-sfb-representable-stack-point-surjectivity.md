## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableStackPointSurjectivity` states the two
source cases of lem-sfb-representable-stack-point-surjectivity. Both theorems have `sorry`
proofs; there are no definitions, axioms, additional assumptions, or proved lemmas.
The node changes only in `lean` and in the addition of the already landed definition
`def-sfb-algebraic-moduli-stack` to `stmt_deps`. No statement correction is needed.

Source read: `literature/stacks-project/stacks-properties.tex`, definition-points (04XG),
lemma-points-cartesian (04XH), and lemma-characterize-surjective (04XI), especially both
implications of its proof (lines 802–882 in this checkout). Also read
`literature/stacks-project/algebraic.tex`, lemma-representable-algebraic (03YS), part (2),
lines 1465–1498: an algebraic space gives a Deligne–Mumford, hence algebraic, stack.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary base scheme S is `{S : Scheme.{u}}` in both theorems. Test schemes
  are all `T : Over S`, with no finite-type, affine, nonempty, or separation restriction.
- The target algebraic stack X is `X : BasedCategory.{v₁, w₁} (Over S)` and
  `hX : IsAlgebraicModuliStack X`. Reading this existing definition gives exactly
  stack descent in groupoids, algebraic-space diagonal, and a smooth surjective
  scheme atlas. Smoothness is the Mathlib `Smooth` in the atlas predicate.
- In the first theorem the source algebraic stack is
  `Y : BasedCategory.{v₂, w₂} (Over S)` with `hY : IsAlgebraicModuliStack Y`.
  In the second theorem the other allowed source is `A : AlgebraicSpace S`,
  used as the existing `discreteModuli A.obj.obj`. This keeps the algebraic-space
  point classes without requiring the caller to supply an additional stack structure.
- The morphism is `f : BasedFunctor Y X` or
  `f : BasedFunctor (discreteModuli A.obj.obj) X`. The functor's base equality
  makes it a morphism over S. No arbitrary maps on points replace this functor.
- Representability is exactly `hf : IsRepresentableByAlgebraicSpaces f`. This
  recorded definition gives, for every scheme map t, a space Z and a projection p
  with `HasSpaceBaseChange f T t Z p`.
- The left-hand surjectivity is `Function.Surjective (moduliPointMap f)` for
  stacks. For a space source it is
  `Function.Surjective (moduliPointMap f ∘ moduliSpacePointMap A.obj.obj)`.
  The latter domain is exactly `AlgebraicSpace.Point A.obj.obj`, not a set of
  K-rational points for one selected field. The existing canonical comparison
  sends a representative to its field-valued Yoneda object.
- For every scheme map into X, the right-hand side quantifies
  `(T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)`.
  It then quantifies every `(Z : AlgebraicSpace S)` and
  `(p : Z.obj.obj ⟶ yoneda.obj T)` subject to `HasSpaceBaseChange f T t Z p`.
  This condition provides an equivalence with the actual 2-fibre product and a
  2-isomorphism identifying its first projection with p. It does not allow an
  unrelated algebraic space or an arbitrary map to T.
- Surjectivity on underlying algebraic-space point sets is literally
  `Function.Surjective (AlgebraicSpace.mapPoint p)`, whose codomain is
  `AlgebraicSpace.Point (yoneda.obj T)`. Quantifying all presentations is the
  presentation-independent meaning of the canonical projection, not a stronger
  mathematical assertion. The representability hypothesis ensures presentations
  exist, so the implication over presentations is not vacuous.
- The `↔` includes both implications. There is no flatness or local finite
  presentation binder. Both theorem docstrings reproduce the node's two proof
  steps with the common-extension isomorphism and the actual fibre-product triple.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (signatures/docstrings at lines 35–76).
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `discreteModuli`, `discreteModuliMap`, `IsModuliStack`,
  `HasSpaceBaseChange`, and `IsRepresentableByAlgebraicSpaces`; read the full
  definitions and docstrings at lines 365–544.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, and the representability/atlas predicates
  in their definitions; read lines 35–84. The fppf sheaf condition is retained
  in the bundled object, with the existing representable diagonal and atlas.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  signature and docstring at lines 58–65, used by the existing atlas interface.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `CategoryTheory.moduliSpaceFieldObject`, `moduliSpacePointMap`, and
  `moduliSpacePointMap_isHomeomorph`; read the complete module. It publicly
  exposes the recorded point quotient and induced maps from
  `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliFieldObject`,
  `ModuliFieldRelation`, `ModuliPoints`, `moduliFieldMap`, and `moduliPointMap`.
  Their full definitions and docstrings were read, with no new point quotient.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`:
  `AlgebraicGeometry.AlgebraicSpace.PointRepresentative`, `PointRepresentative.Rel`,
  `Point`, and `schemePointMap`; read the complete module. The induced point map
  `AlgebraicGeometry.AlgebraicSpace.mapPoint` in the publicly imported
  `Sheaf.AlgebraicGeometry.ProperCurveModuli` (lines 40–50) is reused verbatim.
- Added landed dependency `def-sfb-algebraic-moduli-stack`:
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`,
  `CategoryTheory.IsAlgebraicModuliStack`. Read its node, all four definitions,
  and their complete signatures/docstrings. It already expresses the general
  stack notion in the item's text; no dependency record repair is required.

Edge cases checked before writing and again against the signatures:

- Empty source and nonempty target: left surjectivity fails; testing a target
  field representative makes the corresponding empty space projection fail.
- Empty target: all maps and all admissible scheme tests are empty as appropriate;
  both sides hold. Empty test schemes are included automatically.
- Identity maps, including stacks with nontrivial stabilizers such as BG: the
  statement uses point classes and fibre groupoids, not a set-valued replacement
  of an arbitrary stack. Scheme base changes of the identity are identities.
- `Spec ℂ → Spec ℝ` over ℝ: surjective despite the absence of an ℝ-rational
  lift. Common field extensions and field-valued point classes retain this case.
- No quasi-compactness, characteristic, atlas finiteness, or morphism finiteness
  restrictions enter either signature. The source and target categories have
  separate object/morphism universes; all schemes and their fields use u, the
  established size convention. No equality between independent stack universes
  is imposed.

Searches actually run with `msearch.py NC lem-sfb-representable-stack-point-surjectivity`:

- LeanFinder: "A representable morphism of algebraic stacks is surjective on field
  valued point classes if and only if every scheme base change is surjective on
  algebraic space points". Eight hits, all scheme surjectivity/locality or stalk
  results (including `AlgebraicGeometry.surjective_iff` and base-change stability);
  none states the stack criterion.
- Loogle: `AlgebraicGeometry.surjective_iff, CategoryTheory.moduliPointMap`.
  Zero hits; the service reports unknown identifier `CategoryTheory.moduliPointMap`.
  This is a limitation of its Mathlib index, not a negative result for our project.
- LeanSearch: "surjectivity on points of algebraic stacks is equivalent to
  surjectivity of every scheme base change". Eight hits on schemes and stalks;
  no matching stack statement.
- Mathlib grep: `ModuliPoints|moduliPointMap|AlgebraicStack|representable.*surjective`
  under `AlgebraicGeometry`: zero hits.
- Direct project `rg` for representability/surjectivity, `stackPointMap`,
  `StackPoint`, and then `ModuliPoints|moduliPointMap`, plus the exact item id,
  in `lean/WeilConjectures`: no matching criterion. `rg` in `lean/Sheaf` found
  the existing interfaces and `surjective_moduli_iff_chartwise`; the latter uses
  field-extension lifting and surjective étale scheme charts, so is not this
  criterion on existing point quotients. Read its full statement and proof
  docstring. `point_open_calculus` treats space-to-space representable-by-schemes
  maps, so likewise does not state this item. `stack_point_topology` states atlas
  surjectivity, topology and continuity, not the equivalence here. Exact-name
  searches for both new theorem names in Mathlib and both project roots returned
  no collisions. No new notion or new definition node is needed.

## Second reading by NC

A separate final reading by this dispatcher worker matched the two declarations
against the unchanged node and Stacks 04XI; the maintainer performs the independent
review after delivery. The stack case retains hX, hY and representability, with
separate category universes. The space case retains the bundled fppf algebraic
space and its own field-valued point set, mapped canonically into stack points.
Both right-hand sides test every scheme map and every presentation of its actual
2-pullback, with point-surjectivity of the specified projection. The use of all
presentations was checked against the equivalence and projection compatibility
in HasSpaceBaseChange; hf rules out a vacuous condition. No added flatness or
finite-presentation hypothesis, rational-point requirement, or dropped empty case
was found. The algebraic-stack definition was added as an already landed statement
dependency because its declaration occurs explicitly. No other node fields or
upstream sources were edited. Both postponed proofs have complete two-step
natural-language docstrings. Compilation and dry-run results follow below.

Validation: scompile.py compiled both the sandbox module and its library-module
form in 3.9 seconds each, without errors or unexpected warnings. The prescribed
deliver2.py --no-push returned OK: commit d8b9d14cdfc passes server preflight
and per-file compilation. A local source check confirms the signature is
verbatim in lean.statement, every Lean line is at most 100 characters, and only
lean and the authorized landed-node addition to stmt_deps differ from the base.
