## Worker report

The module `Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction` states
`AlgebraicGeometry.fppf_family_isEffective_of_affine_singletons`, with its entire
proof postponed by `sorry`. Its source is Stacks Project, Descent, Tag 02W3
(`lemma-descending-types-morphisms`), read in `literature/stacks-project/descent.tex`,
lines 9028–9130, specialized to fppf. No statement correction or new notion is needed.

Clause-by-clause correspondence:

- A property of scheme morphisms is `P : MorphismProperty Scheme.{u}`.
- Invariance under isomorphism is `[P.RespectsIso]`.
- Hypothesis (i), arbitrary base-change stability, is `[P.IsStableUnderBaseChange]`:
  its defining field tests arbitrary Cartesian squares, not just affine squares.
- Hypothesis (ii) is `hfinite`: for every natural number `n`, families `Y B : Fin n →
  Scheme.{u}` and morphisms `h`, pointwise `P (h j)` implies `P (CategoryTheory.Limits.Sigma.map h)`.
  `Sigma.map` is the canonical morphism between the two scheme coproducts. Enumerating
  by `Fin n` covers exactly all finite families, using the stated iso invariance.
  There is no positivity restriction on `n`.
- Hypothesis (iii) is `haffine`: both `A` and `B` have `IsAffine`; `p : A ⟶ B` is
  flat, surjective, locally of finite presentation, quasi-compact and quasi-separated.
  The last three assumptions render exactly the finite-presentation convention in
  the node, without replacing it by a different finiteness convention.
- Every scheme over `A` and singleton descent datum is quantified as `V : Over A`
  and `D : Over.DescentDatum p V`; `P V.hom → D.IsEffective` is its exact implication.
- The conclusion quantifies a family `f : ∀ i, U i ⟶ T` and
  `hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T`. This is precisely
  pointwise flatness, local finite presentation, and joint surjectivity.
- `D : SchemeCoverDescentDatum f` retains the local schemes `D.localScheme i`
  and, via specified Yoneda representations, all overlap isomorphisms and cocycles.
  `hP : ∀ i, P (D.localScheme i).hom` is the property on every local structure map.
- `D.IsEffective` is geometric effectivity: an object `X : Over T`, Cartesian
  projection squares for every local scheme, and invariance under the given
  transitions on all test points. Thus it means compatible isomorphisms with the
  pullbacks of one global scheme, exactly as the node specifies. It does not impose
  `P X.hom`.
- The explicit universe `u` controls schemes and `I : Type (u + 1)` uses the published
  family-descent interface and the existing size convention, as in the published
  separated-locally-quasi-finite fppf descent theorem. No nonempty, countability,
  finite-cover, or affine-base restriction is imposed on the conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and its
  projections, through the recorded descent definitions and their Cartesian squares.
- `Mathlib.AlgebraicGeometry.Limits`: scheme coproduct instances, `sigmaOpenCover`,
  `disjoint_opensRange_sigmaι`; the finite coproduct map is `Limits.Sigma.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `QuasiCompact` and `QuasiSeparated` are the Mathlib morphism predicates named by
  the convention-only `def-weil-pbc-scheme-conventions` record.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum` and `.IsEffective` (full source and docstrings read).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`.
- `Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum`:
  `AlgebraicGeometry.SchemeCoverDescentDatum` and `.IsEffective`, recorded on the
  already landed `def-trf-scheme-cover-descent-datum`. This node is added to
  `stmt_deps`, as authorized for landed notions; no duplicate definition is supplied.
- `def-weil-size-convention` has no object declaration; explicit universes implement it.

The stated proof dependencies are retained as non-public imports:
`FppfAffineRefinement`, `FiniteCoproductLfpQcqs`, `FpqcCanonicalPullbackDatum`,
`FpqcRefinementReflectsEffectivity`, and `FpqcEffectivityOpenLocal` under
`Sheaf.AlgebraicGeometry`; Mathlib `Gluing`, `Morphisms.Affine`, and
`Morphisms.Separated` supply the remaining gluing and affine-permanence tools.
Cover base-change is in the imported fppf/fpqc precoverage API. The theorem docstring
carries all seven DAG proof steps, including the finite-refinement property argument
and the restriction back to the original family.

Edge cases checked before writing: `n = 0` is explicitly permitted in `hfinite`,
so the empty-to-empty coproduct morphism is included. Empty covering index types
are allowed by the binders; a covering then forces an empty base, and geometric
effectivity is realized by the empty scheme. Empty affine schemes and zero rings
are not excluded from `haffine`. Infinite families and non-affine bases remain
allowed. No property is assumed for the infinite coproduct or concluded for the
global realization. An arbitrary false property is incompatible with the empty
coproduct hypothesis, as it should be; the stability assumptions are not tautologies.

Searches for an existing statement:

- `msearch.py ... leanfinder "Scheme descent data for arbitrary fppf covering families
  are effective if effective over flat surjective finite presentation affine singleton
  covers"`: eight hits, headed by the morphism-property `DescendsAlong` instance.
  Other hits concern effective epimorphisms and generic stack descent. None is
  effective descent for scheme objects under the three hypotheses here.
- `msearch.py ... loogle '"DescentDatum"'`: zero hits.
- `msearch.py ... grep 'DescentDatum|effective.*descent|isEffective'
  AlgebraicGeometry`: zero hits in Mathlib's algebraic geometry directory.
- Direct `rg` of upstream `WeilConjectures` and the side `lean/Sheaf` for
  `fppf.*(effectiv|affine)|family.*(descent|Descent)|FamilyDescent`: found the
  published family-datum definition and the separated-lqf specialization; neither
  states this general reduction. Direct search for this node id upstream: no hits.
- Direct `rg` for `DescentData|DescentDatum` in the upstream `Comma` sources read
  the singleton transport API in full; direct search of `dag/nodes` located the
  published family-interface node and its reviewed Lean record.
- Mathlib's morphism-property limits API was inspected: its base-change stability
  and canonical coproduct map are reused, rather than defining new predicates.

No `STATEMENT-DISPUTED` issue was found.

## Second reading by N8

This is a same-worker self-check; the dispatcher explicitly prohibits starting
another agent, and the delivery receives the maintainer's independent review.
Re-read the node, Tag 02W3, the complete singleton and family datum interfaces,
and the delivered signature. Checked the property, iso invariance, all three
hypotheses, the complete fppf covering condition, each local property, the cocycle
and geometric effectivity, and the empty finite family. The existing family
interface was found during the search and cited instead of making a second one.
No mismatch requiring a node correction was found; no mathematical statement
beyond the assigned reduction is added.

Validation: `scompile.py N8 lem-trf-fppf-family-affine-effectivity-reduction` compiled
the sandbox and final library path cleanly (2.2 s and 2.0 s). The initial name-clash
error on unqualified `Sigma.map` was repaired by using
`CategoryTheory.Limits.Sigma.map`. The required `deliver2.py ... --no-push` then
reported `OK (dry run)` with preflight and compilation passing. UTC record date
was checked with `date -u +%F`: 2026-10-18.
