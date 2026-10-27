## Worker report

The module `Sheaf.AlgebraicGeometry.AffineLimitChartDiagrams` states
`AlgebraicGeometry.AffineLimitChart.exists_diagrams`, with one postponed theorem and
fully constructed auxiliary data. No natural-language statement, split, or dependency
list is changed. The previous worker's stage-1 refusal does not apply: the current node
has a reviewed split and no Lean record, is in the stage-2 queue, and brief-stage2 §0
expressly authorizes the stage-2 handoff. There is no repair note for the item.

Source checked: `literature/stacks-project/limits.tex`, label
`lemma-descend-unramified` (Tag 0C4W), first proof paragraph; the same paragraph at
https://stacks.math.columbia.edu/tag/0C4W. The given charts are assumptions of this
lemma, so no qcqs or finite-type hypothesis from the surrounding descent theorem
needs to be added. The proof docstring follows all six accepted steps and their
named dependencies, including the reviewed addition of the Spec-colimit leaf.

Hypotheses, in node order:

- `I : Type u`, `[Preorder I]`, `[IsDirected I (· ≤ ·)]`, `[Nonempty I]` encode a
  nonempty directed set. Using a preorder includes partially ordered sets and does
  not require antisymmetry anywhere; the argument and conclusion are invariant
  under equivalent indices. Indices and schemes use the same `u`.
- `D : Iᵒᵖ ⥤ Scheme.{u}` is the inverse system; the instance binder for every
  `D.map a` states precisely affine transition morphisms. `c : Cone D` and
  `hc : IsLimit c` specify the given limit and its projections. `i₀ : I` is fixed.
- `U V : Over (D.obj (op i₀))` and `g : U ⟶ V` are the two schemes and their
  morphism over the given stage. An over-category morphism includes its structure
  compatibility, rather than asking for an arbitrary underlying map.
- `n : ℕ`, `m : Fin n → ℕ` are the cardinalities of the two finite covers. The
  coordinate rings are `R₀`, `B₀`, `C₀`, all actual `CommRingCat` objects.
- `w j : Spec (R₀ j) ⟶ D.obj (op i₀)` is an open immersion, so its range is the
  given affine open W. `y j` is an open immersion into V with structure morphism
  `Spec.map (b j) ≫ w j`; this is the containment of its image in W with the
  given coordinate ring B. Its over-category type imposes this factorization.
- `x j k` is an open immersion into U with structure morphism
  `Spec.map (b j ≫ φ j k) ≫ w j`. The given ring map `φ j k` is an R₀-algebra map
  because C's R₀-structure is the composite `b j ≫ φ j k`. This permits any
  compatible initial choice of C's R₀-algebra structure.
- `hxy` states that restriction of g on the X chart is exactly `Spec.map φ`, with
  the given Y inclusion. `hy` states the Y ranges cover V. `hx` states, for each
  j, that the X ranges cover the inverse image of that Y range under g.
  Presenting an affine open by an open immersion from its specified spectrum is
  equivalent to an affine open subset together with its coordinate identification;
  it does not identify distinct opens or require an extra choice of a cover.

Conclusion, in node order:

- `bases D c i₀` has index `WithInitial (Over (op i₀))`. An object of
  `Over (op i₀)` is exactly a stage i together with i₀ ≤ i, its arrows are the
  inverse-system transition arrows, and the adjoined `star` is the given limit
  c.pt. The arrows from `star` are the given cone projections, as real data in
  `bases`. No arbitrary lift or map is hypothesized.
- `charts F f := F ⋙ Over.pullback f ⋙ Over.forget _` is the actual fibre product
  T ×_S Z. For an open immersion Z → S this is the inverse-image open, with the
  usual projection. Consequently the diagram `charts (bases D c i₀) (w j)` is the
  inverse-image W system, including its limit object.
- `A j` is the contravariant diagram of coordinate rings of these affine W charts.
  The natural isomorphism `eW j` identifies the entire diagram with their spectra,
  so both the stage and limit charts are affine and all their projections and
  transitions are retained. `r j t` is the R₀ structure homomorphism. The first
  projection clause for `eW` makes its map to W₀ exactly `Spec.map (r j t)`; the
  next clause gives compatibility of r with every transition. At the identity
  stage this is automatically an isomorphism with R₀, as the inverse image of W₀
  along the identity is W₀.
- `Nonempty (IsColimit (ringCocone (A j)))` is the asserted directed colimit R of
  the stage rings, with all coprojections fixed: `ringCocone` uses exactly
  `A.map` of the arrows from the adjoined limit. Taking the opposite of the
  over-category merely writes the upper tail with its forward ring direction.
- `eY` and `eX` identify the actual pulled-back Y and X schemes with
  `Spec (tensor (r j t) (b j))` and
  `Spec (tensor (r j t) (b j ≫ φ j k))`. `tensor` installs precisely the algebra
  structures of the two given homomorphisms and returns Mathlib's `A ⊗[R] B`;
  `pure`, `left`, and `right` are its pure tensors and standard coprojections.
- The pure-tensor equation for `q j k t` is `a ⊗ b ↦ a ⊗ φ(b)`, so q is the
  specified id ⊗ φ. Those for `vY` and `vX` are `a ⊗ z ↦ α(a) ⊗ z`, where
  α is the appropriate `A.map`. This determines the maps on arbitrary tensors,
  without assuming an arbitrary algebra equivalence.
- The `right` equations for eY and eX identify their projections to the original
  charts with the canonical tensor inclusions. The `left` equations, together
  with eW, identify their projections to T. Thus both projections are included.
  The next two equations identify every chart transition with the specified
  `vY`/`vX`. Indices range over the adjoined category, so this includes maps from
  the limit, identities, and composites.
- The `IsOpenImmersion` clauses say that the pulled-back y and x maps are open
  immersions. The following range-union equalities say that they cover V_T and,
  for each j, the inverse image of Y_{j,T} under g_T. Together with the Y cover
  these give the full X cover of U_T. `mapCharts` constructs these maps by the
  actual `pullback.map`, so these are the inverse-image opens of the given
  charts and retain the original finite index families.
- For each j,k the existential h is a morphism over the original base whose
  underlying map is explicitly `Spec.map (φ j k)`. Its base change is identified
  with `Spec.map (q j k t)` by the displayed eX/eY equation. By hxy this is
  exactly g_T restricted to those charts. `IsPullback` then states the chart
  square for each transition; ordinary stages give exactly i₀ ≤ i' ≤ i, and
  the adjoined arrows also express the compatibility with the limit.
- The final clause supplies the two actual ring isomorphisms F and G in the
  stated order. Their source, intermediate ring and target are respectively
  `(A_t ⊗ C₀) ⊗_(A_t ⊗ B₀) (A_s ⊗ B₀)`,
  `C₀ ⊗_B₀ (A_s ⊗ B₀)`, and `A_s ⊗ C₀`.
  The two pure-tensor formulas are precisely
  `(a ⊗ c) ⊗ (a' ⊗ b) ↦ c ⊗ (α(a)a' ⊗ b)` and
  `c ⊗ (a' ⊗ b) ↦ a' ⊗ φ(b)c`.
  The equations with `right` make F and G isomorphisms of algebras over
  E = A_s ⊗ B₀, where E acts on the final ring by q_s. The last two equations
  identify their composite on both factor inclusions with vX and q_s; hence
  this is the canonical coordinate comparison, not merely an abstract ring
  isomorphism. Ring isomorphisms preserving these E structure homomorphisms are
  exactly E-algebra isomorphisms.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`:
  `Spec.homEquiv` and `Spec.reflective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`,
  the actual preimage-of-every-affine-open class, supplied by the public
  affine-transition import.
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition`. Its full current signature
  includes affineness of projections, restricted open limits, and the affine
  comparison with every projection; the module is imported publicly.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map` and `pullback.lift`; the instances
  for schemes come from `Mathlib.AlgebraicGeometry.Pullbacks`.
- The same Pullbacks module supplies the recorded proof dependencies
  `Scheme.pullback_map_isOpenImmersion` and `pullbackSpecIso`, with its two
  projection formulas. `Scheme.Pullback.range_map` is in its imported
  `PullbackCarrier` module. The node's Mathlib matches are used directly.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`:
  `CategoryTheory.IsPullback.paste_vert_iff`; imported for the proof plan.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.reflective`; imported
  for the accepted Spec-colimit-limit proof dependency.

All helper declarations belong to this node's module and are listed in
`lean.declarations`, with source and blueprint docstrings. They package existing
notions and canonical constructions; no independent missing notion, new definition
node, dependency redefinition, or statement correction is needed.

Edge cases checked before writing and during the clause audit:

- Singleton I: `Over (op i₀)` still includes the identity stage, and no strict
  inequality is required. Preorders with equivalent indices are permitted.
- Empty Y cover: `n = 0` is permitted and hy forces V empty; the existence of g
  forces U empty. No artificial Nonempty instance is imposed on either chart
  family. For an empty inverse image, `m j = 0` is permitted.
- Empty charts and zero rings: no Nontrivial assumption occurs. Tensor products,
  spectra, zero-ring maps and the displayed formulas all still make sense.
- Arbitrary (including non-injective and non-surjective) ring structure maps and
  φ: nothing assumes flatness or finiteness. The tensor formulas use only
  balancing, so no cancellation or injectivity is hidden.
- Non-quasi-compact base stages: no compactness or quasi-separatedness assumption
  is imposed. Finite covers are given, rather than derived.
- Identities, composite transitions and all limit projections are covered by the
  same functors and quantified morphisms. Universes are bound explicitly and
  `autoImplicit` is false.

Searches made (the wrapper's results were read, along with local declarations):

1. `msearch.py`, leanfinder query: "Affine charts of inverse limits of schemes
   with affine transition maps are tensor product spectra naturally compatible
   with projections and base change". Eight hits: chiefly
   `isAffineHom_π_app`, `exists_appTop_π_eq_of_isLimit`,
   `exists_appTop_π_eq_of_isAffine_of_isLimit`, `exists_isAffineOpen_preimage_eq`
   and finite-type hom approximation results. These give individual limit
   clauses, not this full chart family and its coordinate comparison.
2. `msearch.py`, loogle query:
   `AlgebraicGeometry.Scheme, CategoryTheory.Limits.IsLimit`.
   Twelve hits, including `isLimitOpensCone`, `Scheme.isAffine_of_isLimit`,
   `isAffineHom_π_app`, `nonempty_isColimit_Γ_mapCocone`, and glueing limits.
   None is the stated finite chart diagram.
3. `msearch.py`, grep query:
   `pullbackSpecIso|isLimitOpensCone|isColimit.*Γ`, under AlgebraicGeometry.
   Twenty-five hits; `pullbackSpecIso` and the restricted-open limit are the
   appropriate ingredients, not duplicates of this result.
4. Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id:
   no existing declaration tagged with this node. Concept search
   `chart.*[Dd]iagram|Chart.*[Dd]iagram|affineLimitChart|[Aa]ffine.*[Cc]hart.*[Ll]imit`
   found upstream upper-tail affine chart section-ring and Picard chart results.
   Read `AffineBaseChangeChartColimit.lean`: it concerns base change of a diagram
   of spectra and one section-ring colimit, without this pair of chart covers,
   restricted morphism, two projection identifications or canonical two-step
   tensor comparison. It is not an exact existing match.

The final file passed `scompile.py` both as a sandbox module and under its intended
library module name (7.2 s and 6.5 s respectively), with no compiler errors or
non-sorry warnings. All data definitions are real constructions. The only
postponed theorem is `AlgebraicGeometry.AffineLimitChart.exists_diagrams`, matching
this DAG node. No STATEMENT-DISPUTED finding.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
