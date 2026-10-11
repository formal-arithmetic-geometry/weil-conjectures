## Worker report

The module states the identity, horizontal pasting, and vertical pasting laws for the derived exchange transformation, using the existing derived base-change map encoding. The coefficient category `A`, its category, abelian, Grothendieck-abelian, and sheafification hypotheses are explicit. The three conjuncts render respectively the identity-square equation, the horizontal composite equation with `upperStarCompDerivedPlus`, and the vertical composite equation with `rightDerivedFunctorPlusCompIso'`. All proofs are `sorry` as required.

Dependency declarations used include `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` from `WeilConjectures.SixFunctors.BaseChange.Derived`, `upperStarIdDerivedPlus`, `upperStarCompDerivedPlus`, and `lowerStarComp` from the same six-functor source, and the Mathlib `CategoryTheory.CommSq` and derived-category functor structures. The source's proved declarations `derivedBaseChangeMapPlus_id`, `derivedBaseChangeMapPlus_paste_horiz`, and `derivedBaseChangeMapPlus_paste_vert` were inspected as the exact corresponding equations.

Edge cases checked: identity morphisms use explicit `CommSq`; all schemes and morphisms are universally quantified; no nonemptiness, finiteness, or characteristic hypotheses are introduced; vertical and horizontal composites retain associators and comparison isomorphisms.

Searches: `rg` for the node id and exchange/pasting names in the source and Sheaf tree; source `DerivedPasting.lean` declarations `derivedBaseChangeMapPlus_id`, `derivedBaseChangeMapPlus_paste_horiz`, and `derivedBaseChangeMapPlus_paste_vert`; Mathlib/source search found no declaration with the node's full exchange statement.

## Earlier second reading (a previous round; superseded)

The node and module were read together. The coefficient-category assumptions, identity square, horizontal square pair and outer square, and vertical square pair and outer square all occur as explicit binders. Each conclusion is a natural-transformation equality rendered by the corresponding derived functor whiskering and comparison isomorphisms. No additional hypotheses or cases are present.

## Second reading by E1

I read the sandbox node, every statement dependency and its recorded declaration,
the sandbox module, the source DerivedPasting and DerivedComparison modules, the
landed DerivedInverseImageComposition and DerivedDirectImageComposition modules,
and Stacks sites-cohomology.tex Remarks 07A7, 0E46, 0E47 and Lemma 0D6E.
The literature checkout named by the node is absent here; the same Stacks source
is available read-only at /home/ubuntu/c1-stacks-review/sites-cohomology.tex,
lines 3990--4150. The Stacks assumptions are morphisms of ringed topoi and a
commutative diagram; there are no properness, finiteness or characteristic
hypotheses in these formal equations. The node specifies their application to
cartesian squares of schemes and abelian etale sheaves.

Object, hypothesis and conclusion inventory (and Lean match):

| Node item | Lean rendering and verdict |
| --- | --- |
| Abelian sheaves on the small etale sites, and D+ | `let A := AddCommGrpCat.{u + 1}`; each functor has source/target `DerivedCategory.Plus (Sheaf T.smallEtaleTopology A)`. Exact match; the generic A binder was removed. |
| Arbitrary schemes and their morphisms | `Scheme.{u}` objects and hom binders in each conjunct. Exact match; no field, base scheme or geometric finiteness assumption. |
| Derived inverse image u^-1 | `(u)^*[A].mapDerivedCategoryPlus`, the restriction of the exact inverse image's derived functor, as recorded by def-weil-pbc-derived-inverse-image. Exact match. |
| Derived direct image Ru_* | `(u)_*[A].rightDerivedFunctorPlus`; `rightDerivedLowerStarPlus` in the dependency is definitionally this functor. Exact match. |
| Adjunction u^-1 dashv Ru_* | `(upperStarLowerStarAdjunction A u).derivedPlus`, read in PlusAdjunction. No arbitrary adjunction is introduced. It is used by the conjugate comparison and the exchange-map identification. Exact match. |
| cD for inverse-image composition | `(upperStarCompDerivedPlus A v u).inv`; this source iso is oriented composite-to-iterated, whereas the node's cD is iterated-to-composite. This is exactly the orientation used by the recorded DerivedInverseImageComposition theorem. Exact match. |
| eD for identity inverse image | `(upperStarIdDerivedPlus A T).hom`, with its inverse where required. Exact match. |
| dD for direct-image composition | `(derivedDirectImageComposition u v).hom`; opened the dependency definition, whose body is conjugateIsoEquiv for cD and the specified composite adjunction. Exact match; replaced the first worker's different comparison. |
| Cartesian square with chosen fibre-product identification | `IsPullback g' f' f g`; `toCommSq` feeds the exchange map. IsPullback supplies the fibre-product universal property, equivalently the identification with the chosen pullback. Neither theta nor exchange depends on the choice of alpha; as the node says, only its commuting equality enters. Exact match; CommSq alone did not impose cartesianness and was replaced. |
| Derived exchange Ex_square | `derivedBaseChangeMapPlus A sq.toCommSq`, the dependency's recorded declaration. Source DerivedComparison, `baseChange_app_eq_mateEquiv` and `baseChange_eq_derivedBaseChangeMapPlus` identify this very map with the node's mate. This is an equality of existing constructions, not a private replacement definition. Exact match. |
| Outer rectangles are cartesian | `sq₂.paste_horiz sq₁` and `sq₁.paste_vert sq₂`. Opened Mathlib IsPullback.paste_vert_iff and paste_horiz: these produce exactly the composite morphisms of the node. No independently assumed outer square. |
| Identity law for each f | First conjunct, using `(IsPullback.id_horiz f).toCommSq`: Ex equals eD_Y whiskered by Rf_* followed by the inverse of eD_X whiskered by Rf_*. Since eD_X is invertible, this is precisely the displayed equation Rf_*(eD_X) o Ex = eD_Y Rf_*. Unitors only reassociate identity functors. Exact match. |
| Horizontal: f, f', g, g', h, h', f'' and two cartesian squares | Second conjunct binds these morphisms and both IsPullback witnesses; the outer square is their paste. All node quantifiers occur, with the second square introduced after the first. Exact match. |
| Horizontal conclusion: four arrows | `whiskerLeft Rf_* (upperStarCompDerivedPlus A h g).hom` is (cD_g,h)^-1 Rf_*; then `whiskerRight Ex₁ Dh` is h^-1 Ex₁; then `whiskerLeft Dg' Ex₂` is Ex₂ g'^-1; finally `whiskerRight (upperStarCompDerivedPlus A h' g').inv Rf''_*` is Rf''_* cD_g',h'. Associators give exactly the intermediate functors. Exact match as a natural-transformation equality. |
| Vertical: f, f', g, g', e, e', g'' and two cartesian squares | Third conjunct retains the worker's consistent diagram relabeling: node W,W',X,X',Y,Y' become Lean X,X',Y,Y',Z,Z'; node e,e',f,f',g',g,g'' become Lean f,f',e,e',g,k,g'. Thus node square3 is Lean sq₁ and node square1 is Lean sq₂. Every morphism and hypothesis occurs. Exact match. |
| Vertical conclusion: four arrows | In that relabeling, `whiskerRight (derivedDirectImageComposition e f).hom Dk` is g^-1 dD_f,e; `whiskerLeft Rf_* Ex_sq₂` is Ex_square1 Re_*; `whiskerRight Ex_sq₁ Re'_*` is Rf'_* Ex_square3; `whiskerLeft Dg' (derivedDirectImageComposition e' f').inv` is (dD_f',e')^-1 g''^-1. Associators only supply parentheses. Exact match. |
| All equations are natural in K | Equalities in natural-transformation hom types, not an existence statement or equality on selected objects. Exact match. |

Dependency audit: DerivedCategories records the existing abelian-sheaf D and D+
encoding (its torsion definition is not needed here). ExactFunctor.mapDerivedCategoryPlus
is the exact-functor restriction, not a derived functor requiring a resolution.
UpperLowerStar.Defs.lowerStar has precisely the base-change sections formula of
def-weil-pbc-direct-image, and rightDerivedLowerStarPlus is its bounded-below
right derived functor. PlusAdjunction.derivedPlus supplies the specified derived
adjunction. DerivedInverseImageComposition uses the inverses of the upstream
composition isos and upperStarIdDerivedPlus; these are the comparisons used here.
DerivedDirectImageComposition defines the conjugate comparison as data, without
sorry. Square.squareUpperStarIso constructs the square comparison from the two
composition isomorphisms and the commuting equality; cartesianness is now supplied
by IsPullback. Derived.derivedBaseChangeMapPlus is identified with the mate by the
source comparison theorem, as above. Mathlib IsPullback.paste_vert_iff and its
horizontal counterpart cover the outer pullbacks. No dependency needs a new module,
and no new definition node is needed.

Edge cases: all schemes, including the empty scheme, are quantified without
nonemptiness. The identity square exists for every f, including identities and
maps involving the empty scheme. Zero objects and zero complexes belong to each
D+ and are covered because the equality is of whole natural transformations.
There is no index family or n parameter; boundedness is the existing cohomological
bounded-below predicate, with arbitrary integral lower bound, not a restriction
to positive degrees. No characteristic, properness, noetherianity or torsion
assumption occurs. `u` is an explicitly declared arbitrary universe; abelian
sheaves are in AddCommGrpCat.{u+1}, exactly the project's site encoding. No
independent smaller test universe or unbound auto-implicit variable remains.

Independent searches: ran msearch leansearch and leanfinder with “derived exchange
natural transformation identity and composition laws for inverse images of etale
abelian sheaves”; LeanSearch returned Internal Server Error (recorded unavailable),
LeanFinder returned eight unrelated site-equivalence declarations. Ran msearch grep
`mateEquiv|conjugateIsoEquiv`: generic categorical mate tools, not this conjunction.
Also used rg on Mathlib IsPullback and Adjunction/Mates, and on the source and Sheaf
trees for `baseChange.*paste`, `baseChange.*_id`, `mate`, and
`derivedExchange_identity_pasting`. Source DerivedPasting has the three laws for
the resolution-defined exchange, but its vertical law uses
rightDerivedFunctorPlusCompIso', not this node's conjugate-defined dD. The
DerivedComparison theorem identifies the two exchange constructions, but there
is no existing declaration of the full conjunction using the recorded dD.
No existing identical statement was found. No new notion has been invented.

Mismatches repaired: generic coefficients and their extra instance binders became
the node's abelian coefficients; mere commuting squares became pullback squares;
arbitrary outer-square witnesses became the actual pasted squares; vertical
composition isos became the dependency's conjugate-defined dD, with hom initially
and inv finally; missing module blueprint marker and copyright header were added;
the compressed proof docstring became all four node proof steps with dependency
ids and source places. The existing exchange definition, equations' whiskerings,
identity orientation, horizontal comparisons and consistent vertical relabeling
were kept. The old Worker report is preserved as requested and describes the
superseded draft; this section records the delivered version.

No node statement correction was made: the node's own statement is sound and
self-contained. No hollow definitions or new proofs: the only new declaration
is the stated theorem with a single sorry. Both imports are used. Every line of
the Lean is at most 100 characters. The lean.statement record is the signature
verbatim from the file. Server single-file compilation passed cleanly (2.3 s,
exit 0, no warnings) after the repairs.
