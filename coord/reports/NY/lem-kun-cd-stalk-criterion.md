## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion` states
`AlgebraicGeometry.Etale.isZero_higherDirectImage_iff_geometric_cohomology_colimits`.
Its sole theorem has proof `sorry`; there are no new definitions or auxiliary assertions.
The node is unchanged except for its `lean` record.

Hypotheses and clauses, matched individually:

- Schemes and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Quasi-compact: `[QuasiCompact f]`; quasi-separated: `[QuasiSeparated f]`.
- Nonnegative cohomological degree: `(q : ℕ)`, cast to `ℤ` at homology and shift.
  This includes degree zero and every integer degree at least zero.
- Abelian etale sheaf on X: `(F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- Torsion: `(hF : F.IsTorsion)`. This is local finite additive order on a covering
  sieve, not the stronger assertion that all groups of sections are torsion.
- `R^q f_* F = 0`: `IsZero` of the degree-q `DerivedCategory.Plus.homologyFunctor`
  applied to `rightDerivedLowerStarPlus ... f` of F embedded by `singleFunctor ... 0`.
- If and only if: the displayed `↔`.
- Every geometric point of Y: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)`. The field universe is the scheme universe, as in
  the dependency's point and strict-henselization constructions. No restriction
  to closed points or to a preselected residue-field closure is imposed.
- The colimit over pointed etale neighbourhoods is
  `(Y.pointSmallEtale y).presheafFiber.obj P`. Reading `pointSmallEtale` shows its
  fiber is the functor of lifts of y to etale Y-schemes. Reading `presheafFiber`
  shows it is `colim` after restriction along the opposite category-of-elements
  projection. Thus all neighbourhoods and pointed morphisms occur, with the
  correct opposite variance; cofilteredness is built into the site point.
- The groups `H^q(W ×_Y X, F|)` and their restriction maps are P, exactly the
  presheaf written in the recorded public
  `nonempty_higherDirectImage_iso_sheafification_abelian_single`. Namely, start
  with `uliftYoneda ⋙ free ⋙ presheafToSheaf`, pull back by `upperStar ... f`,
  put the resulting free abelian sheaf in degree zero, and take derived Hom into
  F[q] via `preadditiveYoneda`. Pullback of the free representable gives the free
  sheaf on W ×_Y X; Ext from that free sheaf is restricted etale cohomology.
  This uses the dependency's public formula verbatim, not its private helper.
- Vanishing of the filtered colimit: `IsZero` of that abelian-group object.
  This is categorical vanishing of the actual group, not a predicate on a bare Type.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` is objectwise base-change evaluation.
  Its derived extension is `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`
  in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, imported publicly.
- `def-weil-pbc-etale-sheaves` has a mixed record. The relevant recorded component
  is `CategoryTheory.Sheaf.IsTorsion`, read and imported from its actual source
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
  The sheaf category is Mathlib's `CategoryTheory.Sheaf`; none of the unrelated
  locally constant or constructible predicates in the mixed record is needed.
- `Sheaf.AlgebraicGeometry.StrictHenselization`:
  `AlgebraicGeometry.Scheme.strictHenselizationRing`, `strictHenselizationScheme`,
  and the coordinate-ring diagram supply the stated strict-local-test interpretation.
  This dependency is imported, but no replacement of all pointed neighbourhoods
  by a single strict-local scheme is made in the statement.
- `def-weil-pbc-scheme-conventions` is a convention record with no declaration;
  its relevant components are Mathlib's Scheme, QuasiCompact, and QuasiSeparated.
- Proof dependency `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`:
  `AlgebraicGeometry.Etale.nonempty_higherDirectImage_iso_sheafification_abelian_single`
  (and its general derived version) supplies the exact presheaf formula.
- Proof dependency `Mathlib.CategoryTheory.Sites.Point.Skyscraper`:
  `CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`.
- Proof dependency `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map`.
- Proof dependency `Mathlib.CategoryTheory.Sites.Point.Basic`:
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber` and `presheafFiber`,
  together with `AlgebraicGeometry.Scheme.pointSmallEtale` in
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.

The docstring gives all three proof steps and the relevant DAG identifiers.
All available proof-dependency modules are imported. No cycle omission is needed.

Edge cases checked: q = 0 gives ordinary direct image and the section presheaf;
F = 0 gives zero groups throughout; X empty gives zero cohomology; Y empty makes
geometric-point quantification vacuous and its category of abelian sheaves trivial.
No nonemptiness, characteristic, finite-type, properness, or bounded torsion
hypothesis is added. Fields are not restricted to finite extensions. A point has
its identity neighbourhood, and the opposite indexing category is filtered.

Searches on 2026-10-15:

- `msearch.py ... leanfinder "higher direct image vanishes iff the filtered colimits
  of cohomology over geometric pointed etale neighbourhoods vanish"`: eight hits,
  including `DerivedCategory.isZero_of_isLE`, `isZero_of_isGE`, and affine transition
  limit section lemmas; no exact statement.
- `msearch.py ... loogle "presheafFiber, IsZero, rightDerivedLowerStarPlus"`:
  zero hits; unknown identifier `presheafFiber`.
- `msearch.py ... grep "higherDirectImage|rightDerivedLowerStarPlus|isZero.*presheafFiber"`:
  zero hits in the search service's Mathlib sources.
- `msearch.py ... leansearch "A higher direct image vanishes if and only if the colimit
  of cohomology over every geometric pointed etale neighbourhood system vanishes"`:
  UNAVAILABLE, Internal Server Error; no search verdict inferred.
- `rg` in local Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` for
  `isZero_higherDirectImage_iff_geometric_cohomology_colimits|higherDirectImage.*stalk|
  stalk.*higherDirectImage`: only specialized boundary/local-duality and coherent
  formal-functions stalk results, not this criterion; the proposed name is unused.
- Broader `rg` for `cohomologyPresheaf|stalk.*criterion|isZero.*[Dd]irect|
  isZero.*presheafFiber` located the existing abelian cohomology-presheaf formula,
  which is reused, and unrelated coherent-module results.
- `grep -rn "lem-kun-cd-stalk-criterion"` in the upstream project: no matches.
  The upstream-name census also has no entry for this item or proposed name.

Validation: the delivered file compiled cleanly with `scompile.py` on the server
(1.8 seconds, nice 19, two threads, 60-second file limit). No local compiler was run.
No statement dispute, correction, new node, or dependency replacement is needed.

## Second reading by NY

Independently read the node, its blueprint source, Stacks `etale-cohomology.tex`
at `lemma-higher-direct-images` (03Q8), `definition-stalk`, and
`lemma-stalk-exact` (03PT), all four statement-dependency nodes, and all four
proof-dependency records. Read the actual declarations in their recorded modules,
including the public abelian-single comparison in
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`, rather than relying on
the worker's description. Stacks 03Q8 assumes only a morphism of schemes and an
abelian sheaf; its extra generality does not remove the qcqs and torsion
hypotheses explicitly present in this node. The stalk results assume an arbitrary
scheme and geometric point; no standing Noetherian or characteristic assumption
is missing here.

The complete object/hypothesis/conclusion checklist is:

- Schemes X and Y and a morphism between them: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  Verdict: the same arbitrary schemes and morphism, with no base field imposed.
- Quasi-compact and quasi-separated: `[QuasiCompact f] [QuasiSeparated f]`.
  Verdict: precisely the two properties in the node, using the convention node's
  Mathlib notions, with no finite-type or properness assumption.
- Nonnegative cohomological degree: `(q : ℕ)` and its cast `(q : ℤ)`.
  Verdict: all and only the nonnegative integer degrees intended by the node.
- Torsion abelian etale sheaf: `(F : Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)`.
  Verdict: the category is Ab(X_et). The actual `Sheaf.IsTorsion` definition
  quantifies over sections and covering sieves with locally finite additive
  order; it does not impose a uniform annihilator or torsion on every section
  group. This is the relevant component of the mixed etale-sheaves node.
- The higher direct image is zero: the left `IsZero` applies to degree-q
  `DerivedCategory.Plus.homologyFunctor` of `rightDerivedLowerStarPlus` applied to
  F via `singleFunctor _ 0`. Verdict: exactly R^q f_* F. Read `lowerStar` as
  evaluation on base changes and `rightDerivedLowerStarPlus` as its right
  derived functor on bounded-below categories; F[0] belongs to that category.
- Equivalence and universal quantifier: `↔ ∀ (Ω : Type u) [Field Ω]
  [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y), ...`.
  Verdict: both directions, for every geometric point as in the recorded
  strict-henselization and geometric-point conventions, not only closed points.
- Pointed neighbourhoods and their restriction maps: `(Y.pointSmallEtale y)`
  has fiber `Etale.forget Y ⋙ coyoneda.obj (op (Over.mk y))`; its elements are
  precisely lifts of y to etale Y-schemes. `Point.presheafFiber` is whiskering
  along the opposite category-of-elements projection followed by `colim`.
  Verdict: the actual filtered colimit with the correct contravariant arrows.
  The strict-henselization dependency constructs its coordinate-ring diagram
  from affine members of this same pointed category; the statement correctly
  retains all pointed neighbourhoods, not just its spectrum limit.
- Groups in the diagram: the displayed `uliftYoneda`, free abelian presheaf,
  sheafification, `upperStar ... f`, `singleFunctor _ 0`, and
  `preadditiveYoneda.obj (F[0]⟦q⟧)` composite.
  Verdict: Hom(f* Z[W][0], F[0][q]) is restricted etale cohomology on W ×_Y X,
  naturally in W. Pullback of a free representable is the free representable on
  the base change. This is exactly the public presheaf in the dependency's
  `nonempty_higherDirectImage_iso_sheafification_abelian_single` signature, not
  a new cohomology definition or a private helper.
- Vanishing of each colimit: the right `IsZero` is on the resulting object of
  AddCommGrpCat. Verdict: zero group, with no added conclusion or clause omitted.

Edge cases: q = 0 is included and gives direct image and sections. F = 0 and
X empty give zero groups. If Y is empty the point quantifier is vacuous and
the category of abelian sheaves is trivial, as required. There is no assumption
of nonempty schemes, any characteristic, bounded torsion, or finite coefficient
groups. An existing geometric point has the identity pointed neighbourhood, so
its indexing category is nonempty and cofiltered; there is no excluded empty
index case. The universe u is arbitrary. The fields are in the same universe
as Scheme.{u}, consistently with `pointSmallEtale` and strict henselization;
residue-field algebraic closures exist there and detect every scheme point.
The coefficient groups live one universe higher, accommodating the site and
derived Hom groups. No independent smaller universe makes a test vacuous.

Independent duplicate searches (2026-10-15):

- LeanFinder: "An etale higher direct image is zero if all filtered neighbourhood
  cohomology groups vanish at geometric points" returned eight etale-morphism
  and etale-locus results, none this criterion.
- Loogle: `IsZero, GrothendieckTopology.Point.presheafFiber` returned no hits,
  reporting unknown identifier `IsZero`; this is not evidence of absence alone.
- LeanSearch: "A sheaf of abelian groups on the etale site is zero precisely
  when all geometric fibers of its cohomology presheaf vanish" was unavailable
  (Internal Server Error); no verdict inferred from that service.
- `rg` with `isZero.*(lowerStar|directImage|presheafFiber)`,
  `vanish.*(stalk|direct image)`, `stalk.*criterion`, and
  `cohomology.*colimit` in Mathlib's geometry/sites, upstream etale six functors,
  and project geometry found the reused comparison and specialized vanishing
  results. Opened the upstream constantModSheaf criterion: it is a one-way
  locally-killed-class criterion for constant quotient module sheaves, not this
  equivalence for arbitrary torsion abelian sheaves.
- A full-tree search for `isZero.*presheafFiber`,
  `higherDirectImage.*iff.*(stalk|geometric)`, and `stalk.*higherDirectImage`
  in Mathlib, upstream, and project found only boundary local-duality material;
  its stalk-duality assertion for curves is a different statement. The proposed
  declaration name and item id are absent from upstream and its name census.

No mismatch found; no Lean or node repair is necessary. There are no new nodes
or dependency modules to review, and no statement correction requiring citer
verdicts. The sole theorem remains `by sorry`, with no definitions or auxiliary
proofs added. Its docstring carries all three node proof steps, including
sheafification, preservation of stalks, and conservativity applied to 0 → G.
The named universe and all variables are bound; no file-local notation or
instances occur. The node's `lean.statement` was checked verbatim against the
file's signature and agrees. Independent `scompile.py` validation of the sole
delivered file passed cleanly: 1.8 seconds, nice 19, two threads, 60 seconds per
file; no warnings or errors. Only the second-reading report was added.
