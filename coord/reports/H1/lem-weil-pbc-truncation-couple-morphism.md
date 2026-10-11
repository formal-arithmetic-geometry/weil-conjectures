## Worker report

The module `Sheaf.AlgebraicGeometry.TruncationExchangeCouple` states
`AlgebraicGeometry.Etale.truncation_exchange_couple_morphism`. All theorem proofs
are `sorry`. The only other theorem, `CategoryTheory.TruncationExchange.exists_triangle`,
states the existence of the canonical projection and boundary required to define
the displayed truncation triangle. Its docstring gives the construction from
lem-weil-pbc-truncation-triangle. Every definition has actual data: projection and
boundary choose maps from this named existence theorem, rather than using `sorry`
as data. No statement, dependency record, or proof text of a DAG node is changed.

Hypothesis and construction correspondence:

- The four schemes and four scheme maps are the explicit binders
  `{X' X Y' Y : Scheme.{u}}`, `{g'}`, `{f'}`, `{f}`, `{g}`. The cartesian square is
  `sq : IsPullback g' f' f g`; `sq.toCommSq` supplies the commutativity needed by
  the existing derived exchange. `IsPullback` records the universal property and
  hence the specified comparison with the fibre product; exchange uses only its
  commutative square, as the dependency's definition says.
- The category is precisely `DerivedCategory.Plus (Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1})`. Thus K is any bounded-below derived object of abelian
  etale sheaves, including objects bounded below only in cohomology. There is no
  chosen strict complex representative, no properness assumption and no torsion
  assumption.
- `truncationPhi f g` is `lowerStar ... f |>.rightDerivedFunctorPlus`, followed by
  `(upperStar ... g).mapDerivedCategoryPlus`. `truncationPsi g' f'` reverses this
  order using g' and f'. These are the dependency functors, not new functors.
- The integer parameters p and q are unrestricted `ℤ` throughout.
- `TruncationExchange.trunc` applies the standard t-structure's `truncLE` on D+.
  `sheaf K q` places `(DerivedCategory.Plus.homologyFunctor _ q).obj K` in degree
  zero; `layer K q` is that object shifted by `-q`.
- `inclusion K q` is the existing canonical `natTransTruncLEOfLE (q-1) q`.
  `exists_triangle` requires the projection on H^q, composed with `layerIso`,
  to be the H^q of `truncLEι`. It also requires the displayed triangle to be
  distinguished. This identifies the canonical j_q, rather than an arbitrary
  projection or triangle. The canonical k_q is then the chosen connecting arrow.
  `projection` and `boundary` take these maps from that theorem. The defining
  properties are available as its `choose_spec`; they are not extra hypotheses
  on K in the main statement.
- `D F K p q` and `E F K p q` are exactly H^{p+q} of F applied to the upper
  truncation and to the shifted cohomology sheaf, respectively.
- `alpha F K p q` is H^{p+q}(F i_{q+1}). Its `eqToHom` transports only the
  arithmetic equalities `q=(q+1)-1` and `p+q=(p-1)+(q+1)`.
- `g F K p q` is H^{p+q}(F j_q).
- `f F K p q` is H^{p+q} of `F k_q` followed by `F.commShiftIso 1`, and then the
  cohomology shift isomorphism with total degree `(p+2)+(q-1)=p+q+1`. These
  functor shift isomorphisms are the inherited composite CommShift instances of
  the dependency functors, not arbitrary choices or additional hypotheses.
- `tD` and `tE` are H^{p+q} of the existing exchange transformation at `trunc K q`
  and `layer K q`, exactly as displayed in the node.

Conclusion correspondence:

1. The first conjunct asserts existence of P and Q of the recorded type
   `BigradedExactCouple (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u+1}) 0`.
   Equalities of their D and E fields and heterogeneous equalities of all six
   structure-map families require exactly the displayed D, E, alpha, f, g.
   HEq is used because the fields' morphism types depend on D and E; it expresses
   equality of maps after the asserted equalities of the object families, not
   an unspecified isomorphism of couples. The structure's three zero-composite
   and three image/kernel fields supply every exactness clause of (1).
2. The next three conjuncts quantify over every p,q and give, in Lean's
   diagrammatic composition order, alpha_Phi followed by tD = tD followed by
   alpha_Psi; g_Phi followed by tE = tD followed by g_Psi; f_Phi followed by the
   tD in bidegree (p+2,q-1) = tE followed by f_Psi. Thus all three required
   squares commute for the specified exchange maps.
3. `pageIso` applies H^{p+q} to `F.commShiftIso (-q)` and then the cohomology
   `shiftIso (-q) (p+q) p`. This is the canonical iterated shift comparison.
   `truncationSourceIso` is the inverse-image/cohomology comparison of the exact
   inverse image, evaluated on Rf_* of the degree-zero sheaf. Its target is
   explicitly `upperStar g` applied to H^p(Rf_* H^q(K)).
   `truncationTargetIso` uses the exact inverse image's compatibility with
   `singleFunctor 0`, followed by Rf'_* and H^p; its target is explicitly
   H^p(Rf'_* of the degree-zero sheaf g'^{-1}H^q(K)). These are respectively
   g^{-1}R^p f_* H^q(K) and R^p f'_* g'^{-1}H^q(K), by the definition of higher
   direct image. The final conjunct is the square comparing tE under those
   two composed canonical isomorphisms with H^p of the existing exchange at
   `sheaf K q`, transported to precisely those source and target sheaves.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.BaseChange.Square`:
  `AlgebraicGeometry.Etale.squareUpperStarIso`, the square isomorphism whose mate
  underlies exchange. Its input is a CommSq; the pullback hypothesis above
  specializes it to the node's cartesian square.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, the transformation used in
  every tD/tE occurrence, with its full source and target signatures checked.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` and `upperStar`; the derived direct image
  is the recorded generic `rightDerivedFunctorPlus` specialized to lowerStar.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`,
  `mapDerivedCategoryHomologyFunctorIso`, `isGE_mapDerivedCategory_obj`, and the
  restricted `mapDerivedCategoryPlusHomologyFunctorIso` and
  `mapDerivedCategoryPlusSingleFunctor`. These give the inverse images and the
  canonical source/target comparisons in clause (3).
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  the recorded CommShift and IsTriangulated instances on rightDerivedFunctorPlus.
  The existing instance on composition gives xi and zeta.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded abelian-sheaf case
  is `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1})` with
  `DerivedCategory.Plus` as its bounded-below full subcategory. No coefficient
  change or new derived category is introduced; the existing types are used.
- `Sheaf.CategoryTheory.TruncationTriangle`:
  `DerivedCategory.truncation_triangle`, read in full. Its complexes-level
  projection and boundary existence and bounded-below conclusion justify
  `exists_triangle`; the actual standard truncation objects and first maps
  are reused directly from Mathlib. Stage 3 can use the recorded theorem to
  prove this named existence statement.
- Mathlib `Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`; `Plus.homologyFunctor` is the composite of
  this functor with the inclusion. Also `singleFunctorCompHomologyFunctorIso`
  and the existing ShiftSequence are used in the canonical comparisons.
- `Sheaf.CategoryTheory.ExactCouple`: `CategoryTheory.BigradedExactCouple`, used
  directly rather than making another exactness predicate or couple structure.

The two imports bring in these existing definitions and structures. The
auxiliary declarations merely name the node's displayed objects, maps and
canonical identifications; they do not replace any dependency notion. The
existing `TruncationCouple` module instead computes chosen-resolution
right-derived cohomology of a single left exact functor on a strict complex,
so it cannot supply this node's functors or its derived-object K. Its data
convention was read before writing the present formulas.

Edge cases checked mathematically before writing: K=0 gives zero layers and
couples; the empty scheme gives the zero sheaf category and the same formulas.
No integer bound is assumed on p or q: negative p, q=0 and negative q all
use signed integer shifts. For q below a lower cohomological bound the
truncations and layers are zero and the exactness and squares still apply.
For an identity cartesian square exchange specializes to identity and every
comparison square becomes the canonical naturality identity. No characteristic
or nonemptiness restriction, or independent index-universe restriction, appears.
The type of schemes is universe-polymorphic and the sheaf values use the
source library's required u+1 universe. `autoImplicit false` is set explicitly.

Searches (the msearch output records are retained in sandbox `searches.jsonl`):

- LeanFinder query `Exchange morphisms on truncation triangles form a morphism
  of exact couples`: eight results, including `TStructure.truncGEδLT`, triangle
  exactness, `ShortComplex.ShortExact.singleTriangle_mor₂`, and
  `DerivedCategory.triangleOfSESδ`; none states this exchange/couple lemma.
- LeanSearch query `A natural transformation commuting with shifts gives a
  morphism of truncation exact couples`: unavailable, HTTP Internal Server
  Error, recorded without claiming a negative semantic-search result.
- Loogle query `Functor.commShiftIso, DerivedCategory.homologyFunctor`: the
  service did not know the first identifier. A second query
  `DerivedCategory.homologyFunctor` returned twelve results: homology functors,
  their ShiftSequence and long exact sequence lemmas, but no exact-couple lemma.
- Mathlib grep query `ExactCouple|truncationCouple`: zero matches.
- Source grep of the exact node id: zero matches. Source/project rg for
  `truncation.*[Cc]ouple|[Ee]xactCouple|truncationCouple`: the project contains
  ExactCouple, TruncationCouple, TruncationCoupleExact and ExactCoupleMorphism,
  whose signatures were read; no existing exchange/truncation-couple lemma.
- Name collision rg for `TruncationExchange|truncation_exchange_couple_morphism|
  truncationSourceIso|truncationTargetIso` in Mathlib, WeilConjectures, Sheaf,
  and `dag/lean_names_upstream.json`: zero matches before writing.

The local literature checkout has lists only, so the source proof of Tag 0DDE
was opened at https://stacks.math.columbia.edu/tag/0DDE. It uses the two
hypercohomology spectral sequences and points to their construction in Derived
Categories 13.21.3. The node supplies the detailed truncation-couple expansion;
no properness/torsion hypothesis is needed for this construction of the map.

Server validation: clean single-file compilation of the final 268-line module,
3.1 seconds, with explicit `autoImplicit false`, the complete conclusion and
canonical higher-direct-image comparisons. `deliver2.py H1
lem-weil-pbc-truncation-couple-morphism --no-push` printed OK: compilation and
preflight passed except for the independent second reading, which the second
reader writes. Nothing was pushed.

## Second reading by H1

I reread the node statement, its Stacks source (Tag 0DDE, Lemma 59.91.12),
all recorded statement dependencies, and the Lean module item by item.

- The objects are the four universe-polymorphic schemes and maps
  `{X' X Y' Y : Scheme.{u}}`, `{g' : X' ⟶ X}`, `{f' : X' ⟶ Y'}`,
  `{f : X ⟶ Y}`, `{g : Y' ⟶ Y}`, the cartesian-square hypothesis
  `sq : IsPullback g' f' f g`, and
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1})`.
  These are rendered by the theorem binders exactly, with no properness,
  torsion, characteristic, or nonemptiness hypothesis added.
- The functors are rendered by `truncationPhi` and `truncationPsi`, using the
  recorded `lowerStar`, `upperStar`, `rightDerivedFunctorPlus`, and
  `mapDerivedCategoryPlus`; they have the stated source and target.
- The truncation triangle objects and maps are rendered by `trunc`, `sheaf`,
  `layer`, `inclusion`, `projection`, and `boundary`. `exists_triangle` chooses
  actual maps and states both the canonical H^q projection equation and the
  distinguished-triangle clause, so no hollow data or arbitrary triangle is
  introduced.
- `D`, `E`, `alpha`, `g`, `f`, `tD`, and `tE` have the node's displayed
  cohomological degrees and bidegrees. The `eqToHom` transports in `alpha` and
  the shift comparison in `f` are exactly the integer equalities in the node.
- `pageIso`, `truncationSourceIso`, and `truncationTargetIso` render the three
  canonical comparisons in clause (3). The final square uses the conjugated
  exchange map (source comparison inverse followed by exchange and target
  comparison), which is precisely the degree-p exchange map under the stated
  canonical identifications.
- Clause (1) is the existential pair of `BigradedExactCouple`s with equality of
  D/E families and HEq equality of all six structure-map families. Clause (2)
  has all three quantified commuting squares, with categorical composition in
  the correct order. Clause (3) quantifies over every `p q : ℤ` and gives the
  transported E-page exchange square. Every clause of the node is present and
  no extra conclusion is asserted.

Edge cases checked: `K = 0`, zero sheaves, empty schemes, `q = 0`, arbitrary
negative `p` and `q`, and identity pullback squares all type and reduce to the
corresponding zero or identity maps. No characteristic or nonemptiness
assumption is present, and all scheme and sheaf universes are the node's single
universe parameter.

The worker's searches were independently checked in the recorded `searches.jsonl`:
LeanFinder, LeanSearch, Loogle, Mathlib grep, source/project grep, and name
collision searches found no existing exchange/truncation-couple declaration.
The existing `TruncationCouple` and `ExactCouple` declarations are different
notions and do not state this result. No mismatch was found, so no source, node,
or Lean change was needed. The module compiles cleanly with `scompile.py`; the
only proof placeholders are the named `sorry` declarations permitted for stage 2.
