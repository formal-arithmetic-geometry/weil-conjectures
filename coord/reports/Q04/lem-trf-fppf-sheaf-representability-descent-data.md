## Worker report

The delivery states Stacks Descent Tag 02W5, specialized to the big fppf topology,
including its local-object identification and representability/effectivity clauses.
The source was read in `literature/stacks-project/descent.tex`, lines 9330–9438,
including the remark immediately after the lemma. No source or item statement correction
is needed. The theorem has exactly one `sorry`; every added definition has real data.

The module is `Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData` and its
statement is `AlgebraicGeometry.fppfSheafRepresentabilityDescentData`.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A scheme T | `(T : Scheme.{u})` |
| Set-indexed schemes T_i and structure maps | `{I : Type (u + 1)}`, `(U : I → Scheme.{u})`, `(f : ∀ i, U i ⟶ T)` |
| An fppf covering, including flatness, local finite presentation and joint surjectivity | `hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T`; this is precisely Mathlib's fppf precoverage, not just an arbitrary covering sieve |
| Size convention | Schemes have object universe u+1 and morphism universe u; the family and sets lie in u+1. There is no independent smaller test universe and no equality of object and morphism universes |
| T-schemes and h_Z(W) = Mor_T(W,Z) | `Over T`; `uliftYoneda.{u + 1}.obj Z` is the Hom presheaf with the harmless lift into the coefficient universe |
| Scheme descent data X_i and the double-overlap isomorphisms | `SchemeCoverDescent f`, defined with actual `localScheme i : Over (U i)` and `representation i`; Mathlib's `data.hom` gives natural sheaf transitions, conjugated by these representing bijections to scheme maps by Yoneda |
| Triple-overlap cocycle | `data.hom_comp`; transitions are isomorphisms by Mathlib's `DescentData.iso`. Its `hom_self` is the diagonal consequence of the invertible cocycle, not an extra condition |
| Morphisms in the scheme-datum category | Morphisms of `SchemeCoverDescent f` are `data ⟶ data'`: compatible local natural transformations. Yoneda and the specified `representation` identify these bijectively with the local scheme maps commuting with the scheme transitions. Identity and composition are inherited from Mathlib's descent category |
| Sheaves of sets on the big fppf site over T | `Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))` |
| Each h_Ti × H is represented | The full subcategory `(IsLocallyRepresentableFppfSheaf f).FullSubcategory` requires representability of each slice restriction, exactly the equivalent formulation in the remark after 02W5 |
| There is an equivalence of the two categories | The existential `e : SchemeCoverDescent f ≌ (IsLocallyRepresentableFppfSheaf f).FullSubcategory` |
| The equivalence carries the given local schemes AND their comparison maps | The first conjunct is a natural isomorphism `e.functor ⋙ inclusion ⋙ toDescentData f ≅ schemeCoverDescentForget f`. Thus it compares the entire descent datum and all its morphisms, not just unrelated objectwise choices |
| The schemes representing the products are X_i | The second conjunct explicitly gives `RepresentableBy ((Over.map (f i)).obj (D.localScheme i))` for `Limits.prod (uliftYoneda.obj (Over.mk (f i))) (e.functor.obj D).obj.obj` |
| Effectivity means X ×_T T_i ≅ X_i inducing the specified transitions | `D.IsEffective` is defined geometrically, with one `X : Over T`, maps `q i`, Cartesian squares `IsPullback (q i) (D.localScheme i).hom X.hom (f i)`, and invariance of the composite to X under the specified transition on every test point |
| H is representable iff its corresponding datum is effective | Final conjunct `(e.functor.obj D).obj.obj.IsRepresentable ↔ D.IsEffective`, for every datum D |

The natural datum isomorphism is stronger information than unrelated local representing
objects but is exactly what the node's specified comparison-isomorphism clause requests.
It ensures the local schemes and the transition maps correspond together. The separate
product-representation conjunct spells out the local-object clause on the original site.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`, `Scheme.fpqcPrecoverage`, their comparison and subcanonical instances.
  `Mathlib.AlgebraicGeometry.Sites.Small` defines `Scheme.overGrothendieckTopology` as
  the topology induced with `.over`; the statement uses `Scheme.fppfTopology.over T`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and its
  universal property. `IsPullback` from the recorded pullback definition's API states
  geometric local realization without arbitrary choices of comparison maps.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`: `Over.DescentDatum` and
  `Over.DescentDatum.IsEffective`. Read both signatures and docstrings in full. They
  handle a single morphism; their geometric definition motivates the family definition.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`, with
  Mathlib's `Sheaf`, `GrothendieckTopology.over` and `Sheaf.over` retained by its record.
  Only the set-sheaf/site component is used here; no alternative site convention is added.
- `Mathlib.CategoryTheory.Yoneda`: `Functor.RepresentableBy`, its `homEquiv` and
  naturality, `Functor.IsRepresentable`, `uliftYoneda`, and Yoneda uniqueness.
- `Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver`: `pseudofunctorOver` and
  `overMapPullback`. Read its construction: restrictions are precomposition with `Over.map`.
- `Mathlib.CategoryTheory.Sites.Descent.DescentData`: `DescentData`, its `Hom`,
  `iso`, identity/cocycle laws and `toDescentData`.
- Proof dependency imports: `Sheaf.AlgebraicGeometry.FppfAffineRefinement`
  (`Scheme.exists_finite_fppf_affine_open_refinement`),
  `Sheaf.CategoryTheory.SetSheafCoverDescent` (`setSheafCoverDescent`), and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` (the recorded module
  of `def-pur-localized-ringed-site`). The remaining proof dependencies are Mathlib
  declarations already reached by these imports and the new definition module.

Edge cases checked against the source and the signatures:

- No `Nonempty I` is imposed. An empty covering is admitted exactly when it is an fppf
  covering (hence only for the empty base). The sheaf condition on the empty covering
  forces the unique section, so the category/effectivity clauses still have their usual meaning.
- Empty schemes and empty overlaps are allowed; test schemes quantify over all Scheme.{u}.
- No quasi-compactness, separation, finite-type condition, effective-descent assumption,
  affine-local-scheme condition, or nonempty-cover hypothesis was added.
- The cover need not be finite. The family universe is the site's object universe u+1.
- The geometric predicate asks for Cartesian squares and compatibility with the actual
  transition maps; it does not merely ask that each local scheme be isomorphic to a pullback.
- Coefficient sets are in u+1 as in the recorded set-sheaf gluing theorem; represented
  Hom sets lie in u and are lifted for the explicit product presheaf. RepresentableBy
  works across these universes without a restriction on schemes or a site-universe equality.

Searches for an existing statement or missing family interface:

- `msearch.py leanfinder`: “Schemes with descent data on an fppf covering are equivalent
  to locally representable sheaves”: 8 hits, principally Zariski local representability
  and generic pseudofunctor stack equivalences. The Zariski declarations require an
  open-immersion cover; none is this fppf scheme/sheaf equivalence.
- `msearch.py leansearch`: “Category of schemes with descent datum over a covering
  family and effective datum”: 8 hits, including generic `Pseudofunctor.DescentData`
  and `EffectiveEpiFamily.desc`; no exact category of local schemes on this family.
- `msearch.py loogle`: `CategoryTheory.Over, CategoryTheory.Pseudofunctor`: 12 hits,
  generic prestack/sheaf-Hom declarations; none supplies the family scheme category.
- `msearch.py grep`: `pseudofunctor|DescentData` in `CategoryTheory/Comma`: 0 hits.
- `msearch.py grep`: `SchemeCoverDescent|LocallyRepresentableFppf|representable.*descent`
  in `AlgebraicGeometry`: 0 hits.
- `rg` of the same names in the upstream WeilConjectures source, the side project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration with these names.
  Nearby source statements inspected include the single-morphism
  `nonempty_representableBy_of_effective_fpqc_descent`; it does not give this category or equivalence.
- Searching the item's id in upstream WeilConjectures found no declaration.
- DAG grep for locally representable/sheaf scheme descent found the item,
  `def-pd-descent-datum`, and `def-galois-scheme-descent-data-category`. The last two
  are explicitly single-morphism interfaces, not the set-indexed family interface.
- `tools/blueprint_refs.py search 'scheme descent'`: 0 blueprint matches;
  `search descent`: 82 matches, no separate family scheme-datum definition.

Validation: scompile.py compiled BOTH modules separately in dependency order, including
sandbox and library locations, without errors or warnings. The only theorem is the
requested statement, with `sorry`. No library-wide build or direct Git command was run.

## New nodes

`def-trf-scheme-cover-descent-datum` introduces the missing covering-family interface
from Stacks Descent 02W5 and geometric family effectivity from 023V. It also names the
associated locally representable full-subcategory predicate. The new module is
`Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum`. The searches above and their exact
msearch results are recorded in the node. The existing `Over.DescentDatum` and the
Galois scheme-datum category apply only to one morphism and do not supply this family
interface. No generic descent notion is copied: the definition directly uses Mathlib's
`pseudofunctorOver`, `DescentData`, `RepresentableBy`, `InducedCategory`, and
`ObjectProperty.FullSubcategory`. Every local representing scheme is explicit data.
Auxiliary local sheaves with specified representing bijections introduce no restriction
or additional isomorphism classes: Yoneda identifies their transitions and morphisms
with the given scheme transitions and morphisms. Their chosen presentations are fully
faithfully forgotten. This is a presentation of scheme descent data, not an assumption
that the scheme data descend effectively.

## Second reading by Q04

The dispatcher brief explicitly forbids starting another agent and assigns independent
review to the maintainer after delivery. No independent worker review is claimed here.
For the worker's final audit, the item, new node, both modules and Stacks 02W5 were
reopened and compared using the table above. The crucial points checked were: a genuine
fppf family rather than an arbitrary sieve; all local schemes retained; invertible
transitions with the triple cocycle; morphisms compatible with transitions; a natural
comparison of the entire local datum; the explicit product-representation clause; and
geometric Cartesian-square effectivity with transition invariance. No statement mismatch
was found. No node correction or dependency-record repair was made.
