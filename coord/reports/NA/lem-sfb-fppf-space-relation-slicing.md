## Worker report

The module `Sheaf.AlgebraicGeometry.FppfRelationSlicing` states
`AlgebraicGeometry.exists_fppf_relation_slicing`, with its entire proof postponed
by `sorry`. The node statement is unchanged. Source read: Stacks Project,
`bootstrap.tex`, lemma-slice-equivalence-relation, Tag 0489, including Steps 1--3
and the size footnote. The node already corrects the source's printed unprimed
`R → U` in the conclusion to the primed projections; no further correction is needed.

Hypotheses and conclusion, clause by clause:

- The base scheme is `{S : Scheme.{u}}`; `{V R : Over S}` are arbitrary schemes
  over it. Morphisms `s t : R ⟶ V` are therefore morphisms over `S`.
- Injectivity of `j=(s,t)` on sections over every test scheme is exactly `hinj`,
  injectivity of `r ↦ (r ≫ s, r ≫ t)` for every `T : Over S`. The pair is the
  sectionwise map into the fibre product; no explicit redundant product map is needed.
- Identification with an equivalence relation is `hrel`, asserting `Equivalence`
  of the binary relation `∃ r, r ≫ s = a ∧ r ≫ t = b` on `T ⟶ V`, for every `T`.
- Flatness of both projections is `[Flat s.left] [Flat t.left]`; local finite
  presentation is the two `LocallyOfFinitePresentation` instance hypotheses.
- The new schemes and projections are existential `V' R' : Over S` and
  `s' t' : R' ⟶ V'`. The first two conclusion conjuncts give precisely the same
  sectionwise injectivity and equivalence conditions for them, for every test `T`.
- The map `g : V' ⟶ V` carries the new relation into the old one through
  `r : R' ⟶ R` and the two equations `r ≫ s = s' ≫ g`, `r ≫ t = t' ≫ g`.
  These specify a map of relations over `S`, without imposing any extra property on `g`.
- All six requested projection properties appear explicitly: `Flat s'.left`,
  `Flat t'.left`, `LocallyOfFinitePresentation s'.left`,
  `LocallyOfFinitePresentation t'.left`,
  `Scheme.Hom.IsLocallyQuasiFinite s'.left`, and the same predicate for `t'.left`.
  The recorded Stacks-compatible quasi-finite predicate includes local finite type.
- The two quotient sheaves are existential `F F' : Sheaf
  (Scheme.fppfTopology.over S) (Type u)`. The presheaf coequalizers of the Yoneda
  maps of `s,t` and `s',t'` are the sectionwise quotient presheaves: presheaf
  coequalizers in sets are computed sectionwise, and coequalizing a relation
  already satisfying `Equivalence` is exactly its equivalence-class quotient.
- The maps `η`, `η'` and their two universal-property conjuncts specify exactly
  the sheafifications of these presheaves. For every sheaf `G`, precomposition
  with the unit is a bijection on natural transformations. This is the
  sheafification adjunction of def-weil-pbc-sheafification, specialized to these
  presheaves, without a global instance asserting sheafification of every
  small-valued presheaf on a large site. This is the same interface as the landed
  relation-restriction dependency. Both universal properties are conclusions;
  there is no added hypothesis assuming that these sheafifications exist.
- The isomorphism is `e : F' ≅ F`. The final equation says that its underlying
  map after the quotient projection equals `yoneda.map g` followed by the old
  quotient projection. Consequently it is the induced map, rather than an
  arbitrary isomorphism. The equation uniquely determines it: first cancel the
  coequalizer projection, then use injectivity in the universal property of `η'`.
- Universe `u` is explicit and shared by the schemes and section sets. The
  category `Over S` has object universe `u+1` and morphism universe `u`; its
  presheaves take values in `Type u`, the universe of its Hom sets. No equality
  between object and morphism universes or smallness hypothesis was imposed.

Recorded statement-dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  exposed through the public scheme imports.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, through the
  scheme pullback import. `Over S` and its section pairs express the product
  universal property; no second fibre product definition is introduced.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `CategoryTheory.presheafToSheaf`,
  `toSheafify`, and `sheafificationAdjunction`. Their full signatures and docstrings
  were read; their defining adjunction is expressed through the two unit universal
  properties because the global small-valued sheafification instance is not assumed.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`:
  `AlgebraicGeometry.Scheme.fppfPrecoverage`, `Scheme.fppfTopology`, and
  `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and its
  stalkwise equivalence `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, defined through the
  recorded `IsQuasiFiniteAtPoint` with its finite-type requirement.
- def-weil-size-convention is the recorded metatheoretic convention and has no
  declaration to import. Explicit universes implement it.

Proof dependencies with recorded modules are imported without `public`:
`Sheaf.AlgebraicGeometry.FlatRelationCMOpen`,
`Sheaf.AlgebraicGeometry.RelationRestrictionQuotient`,
`Sheaf.AlgebraicGeometry.CohenMacaulayRelationPointSlice`, and
`WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange`.
The current server source of `CohenMacaulayRelationPointSlice` was read with
`scompile.py --source`, since it was not yet in the local read clone.
Mathlib proof-dependency imports include `AlgebraicGeometry.Limits` for small
scheme coproducts, `Morphisms.QuasiSeparated` for the permanence interface, and
`Morphisms.UniversallyOpen` for `UniversallyOpen.of_flat`. Flat base change and
locally-finite-presentation base change are already in the public imports.
The finite-type-point detector has no recorded declaration/module to import;
its proof step remains explicitly documented for stage 3.

Edge cases checked: the empty scheme and hence empty family of slices are allowed;
the sectionwise relation on an empty section set is an equivalence relation.
For nonempty test schemes mapping to an empty scheme there are no sections;
for the empty test scheme the Hom sets are singletons and injectivity is valid.
The diagonal relation and the total relation are both covered by the hypotheses.
No nonemptiness, quasi-compactness, separatedness, Jacobson, Noetherian, finite
index, or characteristic condition is added. The new presentation need not have
`g` flat, surjective or an immersion. Arbitrary set-sized families in the scheme
universe are allowed, as required by the source size footnote.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder: "A flat locally finitely presented equivalence relation on schemes
  has a locally quasi finite flat presentation with the same fppf sheaf quotient".
  Eight results, including `LocallyOfFinitePresentation`, `UniversallyOpen.of_flat`,
  `Flat.isQuotientMap_of_surjective`, and descent of morphism properties; none states
  replacement of an equivalence relation or preservation of its quotient.
- Loogle: `"Scheme", "Flat", "Quotient"`. No results.
- Mathlib grep: `slice.equivalence|fppfQuotient|SchemeEquivalenceRelation`.
  Four results, all ordinary slice-category equivalences; no scheme relation slicing.
- LeanSearch: "Slicing flat locally finitely presented scheme equivalence relations
  with unchanged fppf quotient and locally quasi finite projections". Eight results
  about `LocallyQuasiFinite`, restriction, and pullback stability; no slicing theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for equivalence relations,
  `relationQuotient`, `fppfQuotient`, slicing, and fppf quotients found the landed
  relation-restriction quotient lemma and the étale quotient interface, plus
  ordinary morphism slicing. Their statements were read; neither is this lemma.
- Exact item-id search in `lean/WeilConjectures` found no declaration.
  Exact proposed-name search in both roots and `dag/lean_names_upstream.json`
  found no name collision.

No new nodes, dependency repairs, statement correction, or statement dispute.
The complete eight-step proof plan is in the theorem docstring; its proof is `sorry`.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
