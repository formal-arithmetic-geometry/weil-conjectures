## Worker report

The delivery states `AlgebraicGeometry.finiteEtale_fppf_descent` in
`Sheaf.AlgebraicGeometry.FiniteEtaleFppfDescent`, with proof `sorry`, and supplies the
family finite-etale descent category and canonical-pullback compatibility predicate
in `Sheaf.AlgebraicGeometry.FiniteEtaleCoverDescent`. No theorem is proved, and
all three supporting definitions have real data. The original statement, proof,
proof dependencies, and source are unchanged. The statement-dependency list gains
the new definition node and the already existing finite-etale-category node.

Clause-by-clause rendering:

- A scheme `T`: `(T : Scheme.{u})`; local schemes and arrows are
  `(U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)`.
- A set-indexed family in the chosen size convention: `{I : Type (u + 1)}`,
  matching the recorded `SchemeCoverDescentDatum` interface, with explicit
  `universe u` and `autoImplicit false`. No `Small`, `Finite`, or `Nonempty`
  assumption on the family is imposed.
- An fppf covering: `hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T`.
  This is exactly joint surjectivity, flatness, and local finite presentation;
  it does not require any individual covering arrow to be quasi-compact.
- `FEt(T)` and all base morphisms:
  `MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ T`. Its object property is
  finite AND etale and its morphism property is `⊤`. This is the exact
  Mathlib specialization recorded by `def-weil-pbc-finite-etale-category`.
- Local finite etale objects with overlap isomorphisms and triple cocycle:
  `FiniteEtaleCoverDescent f`, the full subcategory of the existing
  `SchemeCoverDescent f` cut out by
  `∀ i, IsFinite (D.localScheme i).hom ∧ Etale (D.localScheme i).hom`.
  The dependency's `data` has its invertible overlap transitions, identity,
  naturality, and cocycle, and `representation` identifies these with scheme
  maps by Yoneda. The diagonal identity follows from the invertible cocycle.
- All compatible local morphism families: morphisms in that FULL subcategory,
  hence the original descent-data morphisms, without any `IsIso` condition.
  `FiniteEtaleCoverDescent.localMap` applies the local sheaf map to the
  universal point and then the target representing bijection inversely.
- Pullback, rather than an unspecified equivalence: the existential `F` is
  constrained by `FiniteEtaleCoverDescentCompatible F q`. Its first clause is
  `IsPullback (q P i) ((F.obj P).obj.localScheme i).hom P.hom (f i)`;
  its second says the specified overlap transport preserves the composite to
  `P` on EVERY test scheme and EVERY test point; its last is
  `(localMap (F.map g) i).left ≫ q Q i = q P i ≫ g.left` for EVERY base morphism.
  The Cartesian universal property makes these the canonical pullback objects,
  overlap comparisons, and base-changed arrows. There is no arbitrary-map
  assumption replacing canonical pullback.
- Pullback is an equivalence: `Nonempty F.IsEquivalence` in the conclusion,
  not a hypothesis. Essential surjectivity supplies each datum with a finite
  etale global object and a compatible descent-data isomorphism. Evaluating
  its represented local maps gives the required isomorphisms with the local
  schemes; the Cartesian squares identify their sources with `X ×_T U_i`.
  Full faithfulness supplies the existence AND uniqueness of the descended
  morphism for every compatible local family. These are the two stated
  'in particular' clauses, not weaker independent assertions of effectivity.
- No quasi-compactness, noetherianity, nonemptiness, or constant-rank condition:
  none occurs in any binder, object predicate, or compatibility equation.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `.Hom`.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `AlgebraicGeometry.Scheme.fppfPrecoverage` and `.fppfTopology`.
- `def-weil-size-convention`: its convention-only record has no declaration;
  explicit universe `u` and family level `u + 1` render it.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`. Integral maps are not needed by this statement.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`, and the equivalent
  Cartesian-square predicate `IsPullback` used by the recorded effectivity interface.
- `def-trf-scheme-cover-descent-datum`:
  `Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum`,
  `AlgebraicGeometry.SchemeCoverDescentDatum`, `SchemeCoverDescent`, and its
  `localScheme`, `data`, and `representation` fields. This interface is used
  directly; no replacement datum is defined.
- `def-weil-pbc-finite-etale-category`: the recorded
  `CategoryTheory.MorphismProperty.Over` specialization from
  `Mathlib.CategoryTheory.MorphismProperty.Comma` and pullback from
  `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`. The latter is
  imported by the support module. The alternative upstream
  `Scheme.FiniteEtale` is an equivalent iterated full-subcategory presentation;
  the node's recorded Mathlib presentation is used here.

Proof imports include the recorded modules
`Sheaf.AlgebraicGeometry.FppfFamilyCoproductDescentEncoding`,
`WeilConjectures.AlgebraicGeometry.AffineFpqcDescent`,
`WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover`, and
`WeilConjectures.AlgebraicGeometry.FpqcDescentEtale`. Other proof ingredients
(fppf-to-fpqc, subcanonicity, base-change covering stability, coproducts, and
locality of affineness) are Mathlib declarations available through these imports.
The theorem docstring carries all six proof steps and their DAG references.
For an index in `Type (u + 1)` one must first pass to a small affine refinement
before forming coproducts in `Scheme.{u}`; the docstring records this size detail.
No extra smallness or existence-of-large-coproduct hypothesis is inserted.

Edge cases checked: an empty family covers only the empty base, and the category
of empty-family data is equivalent to the finite-etale category of that empty
scheme. Empty local schemes are allowed and all their maps/transition equations
are meaningful. Infinite families and empty covering members are allowed.
Disconnected bases and ranks changing between components are unrestricted.
The identity cover gives the usual category back, and an ordinary morphism
between finite etale objects need not be invertible. Test schemes use the same
`Scheme.{u}` universe as the base, so the compatibility quantification is not
vacuous because of a smaller independent universe.

Searches made before writing:

- `msearch.py ... leanfinder`: 'Finite etale schemes and all morphisms satisfy
  effective descent for an arbitrary fppf covering family'. Eight hits concern
  etale topologies and etale morphism properties; none states family effectivity.
- `msearch.py ... loogle`: `"Etale", "Descent"`; no hits.
- `msearch.py ... grep`:
  `finiteEtale.*(descent|stack)|descent.*finiteEtale|[Ff]inite.{0,10}[Ee]tale.{0,30}[Dd]escent`;
  no Mathlib hits.
- `msearch.py ... leansearch`: 'The category of finite etale scheme descent data
  for an indexed covering family, with all compatible morphisms'. The hits are
  generic pseudofunctor descent data and `isEquivalence_toDescentData`, which
  assumes `IsStack`; they do not establish finite-etale fppf descent.
- `msearch.py ... leanfinder`: 'Full subcategory of family scheme descent data
  whose local schemes are finite etale, and canonical pullback functor
  characterized by Cartesian squares and overlap transport'. Hits include
  `Scheme.Etale.forget` and generic relative gluing, no exact family category.
- `msearch.py ... grep`: `FiniteEtale.*Descent|finiteEtale.*descent|finite_etale.*descent`;
  no Mathlib hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf`: found
  `WeilConjectures.AlgebraicGeometry.FiniteEtaleDescent`,
  `FiniteEtaleDescentData`, `FiniteEtaleDescentDataExistence`, and the existing
  family `SchemeCoverDescentDatum`. Read their signatures and docstrings.
  Upstream `finiteEtaleDescent` requires a singleton SURJECTIVE ETALE arrow,
  whereas this node allows arbitrary fppf families. It is not an exact match.
- `rg` for the item's id in `lean/WeilConjectures`: no match.
- `tools/blueprint_refs.py search 'finite etale descent'`: zero blueprint
  nodes; `ancestor` reports `blueprint.from.node = None`, inherited by the new node.
- `rg` across `dag/nodes`, `lean/WeilConjectures`, and `lean/Sheaf` for
  `FiniteEtaleCoverDescent|FiniteEtaleCoverDescentCompatible`: no matches.
  The new node includes the verbatim fresh Mathlib search outputs.

Validation: both delivered modules compiled separately in dependency order through
`scompile.py`, using module mode. The first attempt diagnosed missing expected
morphism-property typing in field notation; spelling `MorphismProperty.Over`
explicitly fixed it. The second attempt compiled both files, including their
library module names, without errors or unexpected warnings.
No statement dispute or source correction is needed.

## New nodes

`def-sfb-finite-etale-cover-descent` defines the finite-etale FULL subcategory of
`SchemeCoverDescent f`, extracts its local maps by the existing specified Yoneda
bijections, and defines the geometric equations characterizing canonical pullback.
Source: Stacks Tag 0BLZ, with Tags 023V and 02W5 for the descent and representing
interfaces. It does not duplicate the ambient scheme descent category or the
finite-etale category. Mathlib's generic pseudofunctor category is not this
specialization; upstream finite-etale descent data are for one arrow. The three
kinds of fresh search and project/DAG searches are recorded in the node.

## Second reading by NF

Author's second pass, with both node texts and both Lean modules open; the
independent maintainer review follows delivery. Checked the finite-etale AND
predicate, `⊤` on all base morphisms, preservation of ALL ambient compatible
morphisms by FullSubcategory, and the exact local inverse-Yoneda formula. Checked
that the transition equation uses the dependency's specified representations and
`data.hom`, preserving the global coordinate for all test schemes; the morphism
equation uses the local scheme map recovered from the actual `F.map g`. Checked
that `IsEquivalence` is concluded and that every occurrence of `q` participates
in the Cartesian or canonical-comparison characterization. No covering,
smallness, nonemptiness, or rank assumption is hidden in the support definitions.
The only correction during elaboration was the explicit Mathlib constructor name
for the category; the mathematical statements did not change.
