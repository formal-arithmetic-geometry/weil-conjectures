## Worker report

The delivery states `AlgebraicGeometry.Etale.truncation_exchange_exact_couple_abutment`
in `lean/Sheaf/AlgebraicGeometry/TruncationExchangeAbutment.lean`. Its only proof is
`sorry`; it introduces no definitions or private notation. The item's TeX statement and
all dependencies are unchanged.

Source read: the blueprint file named in the node, including its Detailed form and
second Proof, read from the project server because literature is not materialized in this
clone. This is the truncation-couple argument, not the unrelated hypercover-totalization
argument in the first Proof.

Hypotheses and objects, individually:

- The four schemes and four arrows are the explicit `X' X Y' Y`, `g' f' f g` binders.
  `sq : IsPullback g' f' f g` specifies the cartesian square; `sq.toCommSq` is the
  square used by the recorded derived exchange transformation.
- `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`
  is an arbitrary bounded below complex of étale abelian sheaves, not a coefficient-module
  specialization or a complex with torsion cohomology. The single explicit universe `u`
  permits arbitrary schemes in that universe, with the source's sheaf universe `u + 1`.
- `a n : ℤ` bind the lower cohomology bound and fixed total degree. `hK` says exactly
  that the cohomology sheaf is zero for every `q < a`.
- `truncationPhi f g` is the recorded composite g inverse image after Rf_*;
  `truncationPsi g' f'` is the recorded Rf'_* after g' inverse image.
- `P Q : BigradedExactCouple ... 0` name the two exact couples on Y'. The ten data
  identifications `hPD`, `hPE`, `_hPalpha`, `_hPf`, `_hPg`, and their Q counterparts
  specify the couples of the node, with D/E/alpha/f/g exactly the recorded truncation
  data. These are the meaning of 'let the two exact couples be those obtained by applying
  Phi and Phi prime to the truncation triangles', not extra restrictions on schemes or K.
  HEq is needed only because the arrow types depend on the identified D and E families.
- Exchange is always the specific `derivedBaseChangeMapPlus AddCommGrpCat sq.toCommSq`.
  The recorded `tD` and `tE` apply cohomology to its components on truncations and layers.
  No arbitrary exchange map or arbitrary couple morphism is a hypothesis.

Conclusions, clause by clause:

1. The first four conjuncts assert the two required D lower-row vanishing conditions and
   the two E half-plane vanishing conditions. `L M : LimitSubobjects`, `A B : ∀ m,
   AlphaColimit ... m`, and `hA hB` realize the canonical abutments as P.D 0 m and Q.D 0 m.
   The two equations for the zero-index cocone maps identify them with the identity,
   as in `halfPlaneConvergence`, excluding an arbitrarily relabeled abutment map.
   `P.ConvergesTo L A` and `Q.ConvergesTo M B` give convergence in the recorded sense.
   The finite/exhaustive/separated conjuncts give the finite filtrations constructed
   there, using `imageFiltration`, and the two canonical comparison squares give
   E infinity isomorphic to the associated graded of those very filtrations.
   The half-plane inequalities imply the stated finite row range a ≤ q ≤ n on
   degree n; this includes the empty range when n < a.
2. `i j` are isomorphisms from the canonical abutments to H^n(Phi K) and H^n(Psi K).
   The two HEq clauses identify their underlying maps with H^n of the canonical
   `truncLEι n` inclusions. `U V` are decreasing filtrations on those cohomology sheaves.
   Their equalities with `(imageFiltration ...).image i.hom` and its primed analogue
   assert that the abutment isomorphisms transport the half-plane filtrations.
   The two step formulas, for every integer p, assert precisely the images of H^n
   applied to the canonical inclusions at n-p. The explicit
   `mapDerivedCategoryPlusHomologyFunctorIso n`, with inverse orientation, is the
   canonical H^n(g inverse image L) ≅ g inverse image H^n(L) comparison. Mapping U.step p
   along its hom equals the image of g inverse image of the image inclusion on Y;
   this is g inverse image of the filtration of H^n(Rf_*K), including its actual subobject
   inclusion, rather than just a noncanonical isomorphism of filtration terms.
3. `t : P.D 0 n ⟶ Q.D 0 n` is identified by HEq with the recorded `tD` component.
   The abutment square is the equality from A n to H^n(Psi K), transporting t by hA/hB,
   then j.hom, versus i.hom followed by H^n of the exchange component at K.
   Thus it says exactly iota prime composed with tD equals H^n(Ex_K) composed with iota.
4. `lift p` and its square with the two step inclusions express preservation of every
   image-filtration step by H^n(Ex_K), in the sense of `FilteredObject.Hom`.
   The maps `gr p` are characterized as the induced maps on the two successive
   cokernel quotients by their squares with `lift p` and the canonical cokernel maps.
   `z p` is the restriction of the recorded tE component to the limiting cycle
   subobjects; its HEq square incorporates the necessary transport along hPE.
   The cokernel equation defines `tInf p` as precisely its induced map modulo limiting
   boundaries, so it is the E infinity map induced by the morphism of couples.
   The isomorphisms `e e'` are canonical: their two squares identify the maps from D
   via `toPageInfinity` with the image factorization of the transported diagonal cocone
   followed by the successive quotient. `hU hV` merely name the image equalities
   needed to type those canonical factorizations. The last square
   `(e p).hom ≫ gr p = tInf p ≫ (e' p).hom` is exactly the required equality of the
   graded map and the infinite-page map under the identifications in (1) and (2).

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.BaseChange.Square`:
  `AlgebraicGeometry.Etale.squareUpperStarIso`; the cartesian-square encoding is
  `IsPullback`, and the exchange uses its commutative square through the imported
  derived exchange module.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, whose full signature is on
  the same D+ categories used here.
- `Sheaf.AlgebraicGeometry.DerivedCategories` records the existing abelian-sheaf
  `DerivedCategory`, `DerivedCategory.Plus`, and homology functors. For the latter
  restricted to D+ the statement uses `DerivedCategory.Plus.homologyFunctor`,
  already used by the recorded truncation data; torsionCohomology is not needed.
- `Sheaf.AlgebraicGeometry.TruncationExchangeCouple`:
  `CategoryTheory.TruncationExchange.D`, `E`, `alpha`, `f`, `g`, `tD`, `tE`,
  and `AlgebraicGeometry.Etale.truncationPhi`, `truncationPsi`. The ten data
  identifications use all the corresponding couple data. The source also states the
  existence of couples with exactly these specifications; they are not hollow hypotheses.
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`: its full recorded definitions
  and docstrings were read. Its image-filtration recipe is precisely the two step
  formulas here. That module's packaged `hypercohomologyFiltrations` takes a chosen
  bounded-below cochain representative and uses unbounded derived functors; this node
  instead fixes K in D+ and the recorded D+ exchange. No copy of its definition is
  introduced: U and V are existential filtrations characterized by the same images,
  using the shared `DecreasingFiltration.image` construction. In particular, this
  delivery does not silently substitute the unbounded base-change transformation.
- `Sheaf.CategoryTheory.HalfPlaneConvergence`:
  `CategoryTheory.BigradedExactCouple.halfPlaneConvergence`, with its definitions from
  `ExactCoupleConvergence`: `LimitSubobjects`, `AlphaColimit`, `imageFiltration`,
  `ConvergesTo`, `pageInfinity`, `toPageInfinity`, and `toGradedPiece`.
- `Sheaf.CategoryTheory.Filtration`: `DecreasingFiltration`, its `IsFinite`,
  `IsExhaustive`, `IsSeparated`, `gradedPiece`, and the step-factorization convention
  of `FilteredObject.Hom`.
- `Sheaf.CategoryTheory.ImageFiltration`: `DecreasingFiltration.image`.
- `Sheaf.CategoryTheory.ExactCoupleMorphism`:
  `CategoryTheory.BigradedExactCouple.coupleMorphism`; its cycle-restriction,
  boundary-quotient, and canonical graded-comparison equations are instantiated in
  the final block. No replacement notion of E infinity is defined.

Edge cases checked before writing: K zero; empty schemes; n < a (no contributing rows,
zero abutments); n = a and n = 0; arbitrary negative a,n; p < 0, p = 0 and
p > n-a. The image formulas quantify over all integer p, including n-p > n, where
surjectivity of the degree-n truncation comparison makes the image the whole object.
No properness, torsion, characteristic, separatedness, or finiteness condition is added.

Searches for an existing statement:

- msearch leanfinder, query 'derived base change exchange truncation exact couples abutment
  image filtration': eight hits on truncation short exact sequences and Ext exact sequences;
  none on étale exchange abutments or the claimed filtration comparison.
- msearch loogle, query 'CategoryTheory.BigradedExactCouple,
  DerivedCategory.Plus.homologyFunctor': zero hits, unknown identifier
  CategoryTheory.BigradedExactCouple (the notion belongs to this project's modules).
- msearch grep, query 'abutment|ExactCouple' in Mathlib Algebra/Homology: zero hits.
- msearch leansearch, query 'exact couple truncation abutment comparison derived functor':
  unavailable, Internal Server Error; no search verdict inferred from that failure.
- rg on source SixFunctors for 'exact.couple.abutment|abutment|exactCouple' and on the
  whole source for the item id: no matching declaration. rg on project AlgebraicGeometry
  for 'abutment|exact_couple_abutment' found related convergence and hypercohomology
  modules, all inspected as relevant; none states the present comparison.
- rg for the proposed full declaration's final name in Mathlib, source, project Sheaf,
  and dag/lean_names_upstream.json: no collision.

The first server compile found two redundant identity casts in the canonical graded
comparison squares; removed them. The resulting single-file server compile is clean
(4.1 seconds), with no errors or warnings. No statement correction, new node, or dependency
module is required. The old note about the choices of projection/boundary in the landed
TruncationExchangeCouple dependency was read; this delivery uses its recorded construction
without changing that shared file.

## Second reading by R1

I read the node's full statement and five proof steps, then independently read its
blueprint source on the project server: both the short form and Detailed form and
both proofs. I also read Stacks derived.tex, lemma-negative-vanishing (05TC),
and etale-cohomology.tex, lemma-proper-base-change (0DDE), with their assumptions.
The present lemma concerns the comparison, not invertibility of exchange: the
properness and torsion assumptions in 0DDE belong to the subsequent invertibility
argument, and are not assumptions of the blueprint's truncation comparison.
The hypercover paragraph in the first blueprint proof does not replace the
truncation-couple proof used by the node and this theorem.

The following is my object/hypothesis/conclusion inventory and its Lean match.
Every row has verdict PASS.

| Node item | Lean rendering and reason for verdict |
|---|---|
| Four schemes and arrows in the displayed cartesian square | `{X' X Y' Y : Scheme.{u}}`, `{g'}`, `{f'}`, `{f}`, `{g}`, and `sq : IsPullback g' f' f g`. This is the project's accepted cartesian-square encoding. `sq.toCommSq` supplies the commutative square used by exchange. |
| Bounded below complex of abelian sheaves on X | `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`. It is the abelian-sheaf case of the recorded derived-categories node, with no module coefficients or torsion assumption. |
| Integer lower bound a and fixed degree n | `(a n : ℤ)` and `hK : ∀ q : ℤ, q < a → IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj K)`. This is cohomological boundedness, not termwise boundedness. |
| Phi and Phi prime | The recorded `truncationPhi f g` is `rightDerivedFunctorPlus` of lowerStar followed by `mapDerivedCategoryPlus` of upperStar; `truncationPsi g' f'` reverses that order with the primed arrows. |
| Both exact couples from the same truncation triangles | `P Q : BigradedExactCouple ... 0`. `hPD,hPE,hQD,hQE` identify their D/E families with recorded `D`/`E`. `_hPalpha,_hPf,_hPg,_hQalpha,_hQf,_hQg` identify all three arrows with the recorded truncation inclusion, connecting map, and projection. These are specifications of the introduced couples, not extra geometric assumptions. |
| Specified exchange and its couple components | Every occurrence uses `derivedBaseChangeMapPlus AddCommGrpCat sq.toCommSq`; recorded `tD` evaluates it on `trunc K q` and `tE` on `layer K q`. There is no freely chosen transformation hypothesis. |
| Clause 1: the half-plane hypotheses | The first four conjuncts give both D vanishing conditions for `q < a` and both E vanishing conditions for `p < 0 ∨ q < a`. Thus on total degree n initial E support has `a ≤ q ≤ n`; later pages are its subquotients. The finite row assertion is a consequence of these explicit half-plane conditions, including when the interval is empty. |
| Clause 1: canonical abutments | `A B : ∀ m : ℤ, AlphaColimit ... m`, `hA,hB`, and the zero-index cocone equations identify the colimits with `P.D 0 m` and `Q.D 0 m`, with the specified identity map. These exclude a changed cocone on the same object. |
| Clause 1: convergence and finite filtrations | `P.ConvergesTo L A`, `Q.ConvergesTo M B`, and the finite/exhaustive/separated triples for `imageFiltration`. The convergence predicate supplies regularity, weak convergence, and the inverse-limit condition. Quantifying all m expresses convergence of the sequences; the remaining comparison is at the fixed n. |
| Clause 1: canonical E infinity/graded identifications | The two `∀ p q, ∃ e` blocks compare `pageInfinity` with the graded pieces of those image filtrations, and their `toPageInfinity`/`toGradedPiece` equations fix the canonical comparison. |
| Clause 2: the canonical inclusions are isomorphisms | `i` and `j` are isomorphisms to degree-n cohomology of `Phi K` and `Psi K`; the two `HEq` equations fix their homs to cohomology of `truncLEι n`. The necessary source identifications are hA/hB and hPD/hQD; HEq expresses their transport, not an arbitrary isomorphism. |
| Clause 2: transport to the stated image filtrations | `U,V : DecreasingFiltration ...`, `U = (P.imageFiltration n (A n)).image i.hom` and the primed equation, followed by `∀ p` step equalities to `imageSubobject (H^n.map (Phi.map (truncLEι (n-p))))` and its Psi analogue. These fix every step, including negative p. |
| Clause 2: first filtration is inverse image of the filtration on Y | `Subobject.exists` along `mapDerivedCategoryPlusHomologyFunctorIso n` with inverse orientation maps `U.step p` to the image of upperStar applied to the actual image inclusion of `H^n(Rf_* truncLEι (n-p))`. Thus both the comparison and the subobject inclusion are specified. |
| Clause 3: canonical abutment map is cohomology of exchange | `∃ t : P.D 0 n ⟶ Q.D 0 n`, its `HEq` with recorded `tD ... K 0 n`, and `eqToHom (hA n) ≫ t ≫ eqToHom (hB n).symm ≫ j.hom = i.hom ≫ H^n.map (Ex.app K)`. This is the node's naturality square in Lean composition order. |
| Clause 4: exchange preserves all steps and induces the graded map | `lift p` factors `(U.step p).arrow ≫ H^n.map (Ex.app K)` through `(V.step p).arrow`. `gr p` is fixed by its commuting square with the two successive-step cokernel projections, hence is the induced quotient map. |
| Clause 4: graded map is the induced infinite-page map | `z p` is tied by its inclusion square and `hPE` transport to `tE ... K p (n-p)`; the cokernel square fixes `tInf p` modulo limiting boundaries. `e,e'` are tied to the transported diagonal cocone images by the two canonical quotient squares using `hU,hV`. Finally `(e p).hom ≫ gr p = tInf p ≫ (e' p).hom` gives precisely the required comparison. |

I opened every statement dependency node and the relevant recorded declarations:
Square.squareUpperStarIso and Derived.derivedBaseChangeMapPlus in the source;
DerivedCategories, TruncationExchangeCouple, HypercohomologyFiltrations,
HalfPlaneConvergence, ExactCoupleConvergence, Filtration, ImageFiltration, and
ExactCoupleMorphism in the project. In particular, `pageCouple r` means page r+2,
`pageInfinity` is the cokernel of limiting boundaries inside limiting cycles,
`AlphaColimit` has its universal property, and `imageFiltration.step` is the image
of its diagonal cocone map. No similar-name replacement is being used.
The hypercohomology package is stated for a cochain representative and unbounded
functors; here the D+ truncation data are the dependency's expressly recorded form.
The existential U/V step equations state the same filtration without defining a
second notion. No new definition node or dependency module is needed. The dependency's
existing note about projection/boundary choices was read; the delivery introduces
no choices or definitions of its own and retains the shared recorded construction.

Edge-case reading: all indices a,n,p,q are integers. No positivity condition
excludes n=0 or negative bounds. If n<a the initial degree-n E support is empty,
and the degree-n whole-complex cohomology and abutment are zero. If n=a only
q=a can contribute. For p<0 the truncation level is above n and the degree-n
image is the whole object; for p>n-a it is zero. Zero K and empty schemes are
permitted by every binder. There is no variable finite index set to which a
Nonempty assumption could be added. No base field, characteristic, properness,
Noetherianity, separatedness or torsion condition is present. Universe u is
arbitrary and the sheaf universe u+1 is the shared six-functor encoding; no
independent smaller test universe is used.

Independent searches, using different queries from the worker:

- LeanFinder via msearch: `natural transformation between right derived functors
  identifies spectral sequence limit with filtered cohomology`. Eight hits on
  exact-functor localization comparisons and ordinary right-derived comparisons;
  none states the node.
- Loogle via msearch: `"trunc", "homology"`. Twelve displayed hits on homology of
  truncations of complexes, not étale exchange on exact-couple abutments.
- LeanSearch via msearch: `truncation spectral sequence natural transformation
  cohomology image filtration`. Service returned Internal Server Error; no
  mathematical verdict inferred from this failure.
- Mathlib grep via msearch: `converg|abutment|filtered.*cohomology` in
  Algebra/Homology/SpectralSequence: no hits.
- Independent rg for `abutment|truncation.*exchange|exchange.*filtration` on the
  source and project: inspected the generic ExactFunctorCouple,
  TruncationHypercohomology, ExactCoupleMorphism and hypercohomology-filtration
  material. They give pieces of this comparison, not the statement. Source
  SpectralSequence.Abutment is an N-graded first-quadrant notion, not this
  integer-indexed truncation comparison with its specified exchange maps.
- The theorem name has no collision in Mathlib, WeilConjectures, project Sheaf,
  or dag/lean_names_upstream.json.

Mismatch verdict: none. I did not rewrite the Lean, its docstring, or the node.
Only this independent second-reading section was appended. H5/H6: no definitions
or extra proofs occur; the theorem has exactly one `sorry`. The arithmetic
transport proofs in its signature only type the recorded indices. H8: both
source docstrings carry the blueprint id and the theorem docstring follows all
five node proof steps. H9: imports are used, all Lean lines are at most 100
characters, and `autoImplicit false` plus the explicit universe and binders leave
no unbound variable. The node's recorded Lean statement is verbatim equal to
the signature extracted by tools/stage2_delivery.py. Independent server
single-file compilation passed in 4.1 seconds with no errors or warnings.
