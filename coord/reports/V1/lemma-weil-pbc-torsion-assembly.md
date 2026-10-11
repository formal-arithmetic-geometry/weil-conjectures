## Worker report

The module `Sheaf.AlgebraicGeometry.TorsionAssembly` states
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_torsion_assembly`, with one
`sorry` proof and no definitions. The statement is unchanged from the DAG.

Hypothesis and clause correspondence:

- The four schemes and four arrows of the diagram are explicitly bound as
  `{X' X Y' Y : Scheme.{u}}`, `{g' : X' ⟶ X}`, `{f' : X' ⟶ Y'}`,
  `{f : X ⟶ Y}`, `{g : Y' ⟶ Y}`.
- A cartesian square with its commutativity and specified identification with the
  fibre product is `sq : IsPullback g' f' f g`. Its universal property gives the
  canonical comparison isomorphism to the chosen pullback; conversely an
  identification respecting both projections gives this property. The exchange
  depends only on `sq.toCommSq`, as the dependency states.
- Properness is `[IsProper f]`. There is no condition on `g`, nor a Noetherian,
  finite-presentation, characteristic, or coefficient-invertibility hypothesis.
- The abelian sheaf is `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  Torsion is precisely the dependency's `hF : Scheme.IsTorsionAbelianSheaf F`,
  the canonical-colimit definition, not sectionwise torsion or bounded exponent.
- Placement in degree zero is
  `(DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1}) 0).obj F`, a genuine object of the specified abelian
  bounded-below derived category.
- The specified exchange morphism is
  `(derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app (...)`.
  The first conjunct states its `IsIso` in the bounded-below category over `Y'`.
- The equivalent formulation is the second conjunct: `∀ p : ℤ, IsIso` of the
  image of this same morphism under `DerivedCategory.Plus.homologyFunctor`
  on `Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}` in degree `p`.
  Both assertions are included; no change from integer degrees to only
  nonnegative degrees is made. Functors preserve isomorphisms, and the converse
  is the cohomology detection theorem named in node proof Step 0.
- The final identification in the node explains these cohomology maps: the
  source of `derivedBaseChangeMapPlus` is `lowerStar f`'s right derived functor
  followed by the exact derived inverse image along `g`; the target is derived
  inverse image along `g'` followed by the right derived direct image along `f'`.
  Higher direct image is defined as the cohomology of that right derived image.
  Thus the `.map` expression is precisely the cohomological exchange map
  transported through the node's canonical identifications, not an arbitrary
  isomorphism between these objects. This explanation is also in the docstring.

Dependencies read and used:

- `def-weil-pbc-cartesian-square`: source module
  `WeilConjectures.SixFunctors.BaseChange.Square`,
  `AlgebraicGeometry.Etale.squareUpperStarIso`. Its full signature takes a
  `CommSq` and yields the composite inverse-image isomorphism. We supply the
  stronger cartesian datum `IsPullback` and use its `toCommSq`; the recorded
  exchange constructor internally uses the square coherence. No second
  cartesian-square or exchange definition is introduced.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, explicitly imported. Its locally finite type
  formulation agrees with finite type since universal closedness supplies
  quasi-compactness, as its node record explains.
- `def-weil-pbc-torsion-etale-sheaf`:
  `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`,
  `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`, explicitly imported and used.
- `def-weil-pbc-derived-categories`: the record explicitly identifies the abelian
  category as `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat)` and
  its bounded-below part as Mathlib `DerivedCategory.Plus`. We use the existing
  Mathlib `DerivedCategory.Plus.singleFunctor` and `.homologyFunctor`, read in
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`. The node's new declaration
  `torsionCohomology` concerns module coefficients and is not needed here.
- `def-weil-pbc-derived-exchange`:
  `WeilConjectures.SixFunctors.BaseChange.Derived`,
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, explicitly imported and used.
  Its complete signature and docstring were read, including the resolution
  characterization and naturality.
- `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, used inside the recorded exchange type.
  The extra recorded name `rightDerivedLowerStarPlus` actually occurs in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; its full
  docstring and body identify it as `(lowerStar A g).rightDerivedFunctorPlus`.
  This is already imported by the exchange module. The inaccurate module for
  that secondary name does not prevent using the existing definitions; no
  dependency replacement is needed.

Edge cases checked before writing: zero sheaf (killed by 1), torsion sheaves of
unbounded exponent, empty schemes, arbitrary proper morphisms, identity base
changes, inseparable or characteristic-dividing coefficients, and `p < 0`.
No edge case is removed by a positivity hypothesis, nonemptiness assumption,
uniform exponent, or invertibility assumption. Scheme universe `u` and abelian
group universe `u + 1` match the established small-etale-site encoding; all
variables and the universe are explicitly bound. No index universe is added.

Searches for an existing statement:

- `msearch.py ... leanfinder "Proper base change for torsion abelian sheaves
  derived exchange morphism is an isomorphism"`: eight hits, all sheaf-of-modules
  pullback/free-object isomorphisms; no proper base change theorem.
- `msearch.py ... loogle "IsIso, IsProper"`: no results, unqualified `IsIso`
  was unknown. Repeated with `"AlgebraicGeometry.IsProper"`: twelve hits for
  properness, its instances and stability under base change; no cohomological
  exchange statement.
- `msearch.py ... grep "properBaseChange|proper_base_change|derivedBaseChangeMapPlus"
  AlgebraicGeometry`: no Mathlib matches.
- `rg` over the source's `WeilConjectures` and the project's `lean/Sheaf` for
  `lemma-weil-pbc-torsion-assembly|torsionAssembly|torsion_assembly`: no matches.
- Source/project `rg` searches for `derivedBaseChangeMapPlus`, `singleFunctor`,
  and torsion base change found source `Etale.isIso_baseChange_of_isProper`
  in `SixFunctors/Etale/BaseChangeTheorems/Proper.lean`. This takes a complex of
  `ModuleCat Λ` sheaves and stalkwise torsion cohomology, rather than the node's
  abelian sheaf and canonical-colimit torsion predicate; using it requires the
  abelian/module equivalence and a torsion comparison, so it is not an exact
  declaration of this statement. The project has the definition
  `HasTorsionAbelianBaseChange` in `TorsionAbelianBaseChange.lean`, but no assertion
  that proper morphisms satisfy it. `ArbitraryRingTorsionSheafBaseChange.lean`
  gives a theorem conditional on prime-quotient injective acyclicity; it is not
  the present unconditional theorem for proper `f`.

Source verified at https://stacks.math.columbia.edu/tag/095T (Theorem 59.91.11):
proper `f`, arbitrary `g`, torsion abelian `F`, and the specific derived base
change isomorphism. The source-place blueprint file is absent from this clone's
literature tree; the complete imported statement and nine proof steps are in
the node and were read. The declaration docstring carries all nine steps and
their dependencies. No mathematical dispute or statement correction is needed.

Validation: `scompile.py V1 lemma-weil-pbc-torsion-assembly` compiled the module
on the server in 2.0 seconds, with no errors or warnings. The node's `lean.statement`
is the signature verbatim, and only `lean` changes in its sandbox copy.

## Second reading by V1

I independently opened the node and the module and matched the statement clause by
clause. The objects are rendered by the implicit binders `{X' X Y' Y : Scheme.{u}}`
and the four morphism binders `{g', f', f, g}`. The node's cartesian square is rendered
by `sq : IsPullback g' f' f g`; this includes the commutativity equation and the
pullback universal property, while allowing the empty and degenerate schemes covered by
the node. The node's hypothesis that `f` is proper is exactly the instance
`[IsProper f]`; `g` has no added hypothesis. The coefficient object is exactly
`F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`, and torsion is exactly
`hF : Scheme.IsTorsionAbelianSheaf F`, using the dependency's canonical filtered
colimit definition rather than a bounded-exponent substitute.

The conclusion's derived object in degree zero is rendered by
`DerivedCategory.Plus.singleFunctor ... 0).obj F`. The specified exchange morphism is
exactly `(derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app ...`; the
first conjunct asserts its `IsIso` in the bounded-below derived category over `Y'`.
The second conjunct quantifies over every `p : ℤ` and asserts `IsIso` after the
specified `DerivedCategory.Plus.homologyFunctor` map, preserving negative degrees and
therefore the node's full equivalent cohomology formulation. No clause, quantifier,
or object is missing, strengthened, or weakened, and the `lean.statement` field is
verbatim equal to the theorem signature.

Edge cases checked are the zero sheaf, unbounded torsion exponent, empty schemes,
identity and arbitrary base changes, inseparable or characteristic-dividing maps, and
all integers including `p < 0`; none is excluded by the Lean binders or hypotheses.
Searches were rerun with LeanFinder/Loogle and `rg` over Mathlib, `WeilConjectures`,
and `lean/Sheaf` for the theorem and its exchange/torsion notions. They found only
the general exchange and torsion definitions and a different module-coefficient
proper-base-change theorem, so no existing exact declaration applies. The dependency
declarations and their source signatures were opened; no unusable dependency or
private replacement was found. Consequently I made no code or node-statement
change in this second reading.
