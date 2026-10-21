## Worker report

The module `Sheaf.AlgebraicGeometry.ProperGeometricFibreCohomologicalBound` states
`AlgebraicGeometry.exists_uniform_geometric_fibre_dimension_and_torsion_cohomology_bound`.
Its only theorem has proof `sorry`; it introduces no definition. The node changes only in
`lean`. No statement correction, missing notion, dependency repair, or disputed statement
was needed. The full four-step natural-language proof is in the theorem docstring.

Hypothesis and clause correspondence:

- Schemes and the named morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Properness is `[IsProper f]`, the recorded Mathlib notion. Its universally closed
  component supplies quasi-compactness, so it implies finite type as used in the proof.
- The quasi-compact base is `[CompactSpace Y]`; there is no Noetherian hypothesis.
- The nonnegative integer bound is `∃ e : ℕ`, equivalently an integer at least zero.
  The same existential variable occurs in both conclusions.
- Every base change is quantified by `∀ (S : Scheme.{u}) (g : S ⟶ Y)`; there is
  no quasi-compactness or other condition on S or g.
- Its structural morphism is `pullback.snd f g : pullback f g ⟶ S`. Every fibre
  is quantified by `(s : S)` and is `(pullback.snd f g).fiber s`.
- Dimension at most e is
  `topologicalKrullDim ((pullback.snd f g).fiber s) ≤ (e : WithBot ℕ∞)`.
  This retains bottom for empty schemes and does not round or discard infinite dimension.
- Every separably closed field is `(Ω : Type u) [Field Ω] [IsSepClosed Ω]`.
  Every specified field-valued point is `(ybar : Spec (.of Ω) ⟶ Y)`, without
  any condition that Ω be algebraically closed or an algebraic closure of a residue field.
- The geometric fibre is the chosen scheme pullback `pullback f ybar`.
- All abelian étale sheaves are
  `F : Sheaf (pullback f ybar).smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Torsion is precisely the recorded `Scheme.IsTorsionAbelianSheaf F`, the
  canonical colimit-of-kernels map being an isomorphism; neither a common annihilator
  nor invertibility of an integer on the fibre is required.
- The cohomological quantifier is `∀ q : ℕ, 2 * e < q → ...`, as the node's
  cohomology definition has nonnegative degrees.
- Vanishing is `IsZero` of
  `(Etale.cohomology AddCommGrpCat.{u + 1} (pullback f ybar) (q : ℤ)).obj`
  applied to `((DerivedCategory.singleFunctor (Sheaf ... AddCommGrpCat.{u + 1}) 0).obj F)`.
  This is exactly the dependency's derived-global-sections definition of H^q of a
  sheaf in degree zero, and `IsZero` is applied to an abelian-group object.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `AlgebraicGeometry.Spec` (also the field spectrum).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` on the underlying space of Y.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the node explicitly
  records scheme base change as `Limits.pullback f g` with structural map
  `pullback.snd f g`; its `moduleBaseChange` is for modules and is not substituted
  for the scheme pullback.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf`:
  `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` (and its `rightDerivedGlobalSections`).
- `Mathlib.Algebra/Field/Defs.lean`: `Field`, the Mathlib leaf for def-weil-field.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`.

The proof-only imports preserve the DAG plan: `exists_fibre_dimension_bound` from
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`;
`topologicalKrullDim_fieldExtension_and_denseOpen` from
`Sheaf.AlgebraicGeometry.DimensionExtension`;
`Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed` from
`Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`;
`Scheme.subsingleton_H_of_two_mul_add_lt_of_isAffine` from
`Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension`;
`Scheme.subsingleton_H_of_two_mul_add_lt_of_affine_bound` from
`Sheaf.AlgebraicGeometry.Sites.AffineToGlobalTorsionCohomologicalDimension`; and
`Scheme.isTorsionAbelianSheaf_characterizations` from
`WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations`.
The Mathlib proof dependencies use the already imported pullback, residue-field,
finite-type composition/base-change, and quasi-compact composition/base-change APIs;
no additional local copy is supplied. The proof-only cohomological-dimension modules
use either derived cohomology or `Sheaf.H`; their comparison belongs to the proof,
not to an extra hypothesis of this theorem.

Edge cases checked before writing:

- Empty Y: both universal conclusions are vacuous, with bound e = 0 available.
- Empty X or an empty fibre: Krull dimension is bottom, hence bounded by e;
  abelian sheaves on the empty site have vanishing cohomology.
- Finite proper morphisms and zero-dimensional fibres: e = 0 permits the expected
  positive-degree vanishing. Degree zero is never incorrectly forced to vanish.
- For a proper curve such as P^1 over a separably closed field, e = 1 permits
  nonzero H^2 and only forces vanishing for q > 2.
- Separably closed imperfect fields are allowed, as are torsion sheaves with
  characteristic-primary torsion or with no uniform annihilator.
- Base changes need not be quasi-compact, and s ranges over every point of S.
- All scheme and field objects use the same arbitrary universe u, matching the
  recorded scheme/base-change interfaces. The site sheaf coefficients are in u+1,
  as required by the recorded torsion and cohomology declarations. No independent
  smaller testing universe or additional universe equality is imposed.

Searches, 2026-10-21:

- `msearch.py ... leanfinder`: "For a proper morphism to a quasi compact scheme,
  dimensions of all base changed fibres are uniformly bounded and torsion etale
  cohomology of separably closed fibres vanishes above twice this bound".
  Eight hits, including `IsSmoothOfRelativeDimension`, base-change stability,
  `IsProper.isStableUnderBaseChange`, and finite-fibre facts; no full conjunction.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsProper, topologicalKrullDim`.
  Successful query, zero hits.
- `msearch.py ... grep`: `cohomologicalDimension|cohomological_dimension|topologicalKrullDim.*(fiber|pullback)`
  in Mathlib/AlgebraicGeometry. Successful query, zero hits.
- `msearch.py ... leansearch`: "Uniform dimension bound for arbitrary base changed
  fibres of proper morphisms over quasi compact schemes and vanishing of torsion
  etale cohomology of separably closed fibres". Eight hits: properness definitions,
  base-change stability, compactness of fibres; no full conjunction.
- `rg` in both project roots for the item id, `exists.*fibre.*dimension`, and
  `geometric.*cd.*bound`: no existing declaration for this node; found and reused
  the ordinary-fibre dimension bound. Broader geometric-cohomology searches found
  adjacent statements about direct images, curves, and finite-type geometry,
  with different hypotheses or conclusions. The proposed full declaration name
  has no match in either root or `dag/lean_names_upstream.json`.
- The blueprint source's Étale statements paragraph was read directly, including
  the same uniform 2d bound after base change.

Validation: prescribed `scompile.py Q59 lem-sfb-finite-proper-geometric-cd-bound`
compiled the one file both as a sandbox module and under its final library module
name, in 2.7 s and 2.4 s respectively, with no warnings or errors.

## Second reading by Q59

Worker self-check against the node and the completed file: properness and compactness
are exactly the two assumptions; the single existential e binds both conclusions;
all S, g and s are quantified in the first clause; the second quantifies all
separably closed Ω, all ybar and all torsion abelian étale sheaves, with q > 2e.
In particular the second projection is the structural map of base change, torsion
uses the colimit definition rather than an extra sectionwise assumption, and the
cohomology object is the recorded functor applied to F in degree zero. No mismatch
was found and no statement was changed. This is a worker self-check, not a claim
of an independent second worker: the dispatch brief prohibits spawning agents and
assigns independent review to the maintainer.
