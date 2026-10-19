## Worker report

The delivery states `AlgebraicGeometry.Etale.truncation_exchange_exact_couple_abutment`
in `Sheaf.AlgebraicGeometry.TruncationExchangeAbutment`. It also restores the unusable
statement dependency `lem-sp-couple-morphism` under §1(B). Both theorem proofs are
`sorry`; no definition or proof is introduced. The item's natural statement, statement
dependencies, proof and proof dependencies are unchanged.

The source is the node's cited blueprint file, section “Detailed form” and its proof,
read together with the four numbered clauses in the DAG. This is not the unrelated
hypercover-total-complex argument in the first blueprint proof. There was no repair
note for this item in `coord/repair-notes`.

Hypotheses, individually:

- The four schemes and their maps are the explicit `X' X Y' Y`, `g' f' f g` binders,
  with `Scheme.{u}` throughout. `sq : ChosenCartesianSquare g' f' f g` uses exactly the
  recorded chosen Cartesian-square notion, including its fibre-product identification.
  Exchange uses its inherited `sq.toCommSq`, as the exchange definition requires.
- The bounded-below complex is
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  This is the recorded category of étale abelian sheaves, with the established size
  convention. No torsion, properness, finiteness or coefficient hypothesis is imposed.
- `a n : ℤ` are the chosen lower bound and the arbitrary total degree. `hK` says
  exactly `q < a → IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj K)`.
- The two couples are `P Q : BigradedExactCouple (...) 0`. `hPD`, `hPE`, `hQD`,
  `hQE` identify their D/E families with `TruncationExchange.D/E` for
  `truncationPhi f g` and `truncationPsi g' f'` respectively. The six heterogeneous
  equalities `_hPalpha`, `_hPf`, `_hPg`, `_hQalpha`, `_hQf`, `_hQg` identify all
  three structure maps on each side with the recorded truncation maps. These are the
  node's specification of which two couples are meant, not assumptions on arbitrary
  geometric data. Their existence is stated in `truncation_exchange_couple_morphism`.
- The functors are the dependency's actual composites: `truncationPhi f g` is
  right-derived direct image followed by exact derived inverse image, and
  `truncationPsi g' f'` is inverse image followed by right-derived direct image.
  The transformation is always the recorded `derivedBaseChangeMapPlus
  AddCommGrpCat.{u + 1} sq.toCommSq`; it is never an arbitrary natural transformation.

Conclusions, clause by clause:

1. The first four conjuncts state D-vanishing below `a` and E-vanishing for
   `p < 0 ∨ q < a`, for P and Q separately. These are exactly the hypotheses of
   `halfPlaneConvergence`, including its finite-row consequence. The existential
   `L M` are the actual limiting subobjects; `A B` are diagonal `AlphaColimit`s.
   `hA hB` identify their objects with `P.D 0 m` and `Q.D 0 m`, while the two
   index-zero equations normalize their zeroth legs. `P.ConvergesTo L A` and
   `Q.ConvergesTo M B` state convergence. The next two conjuncts state finite,
   exhaustive and separated image filtrations. The next two give the infinite-page
   isomorphisms with graded pieces, each normalized by the equation with
   `toPageInfinity` and `toGradedPiece`. Thus the comparisons are canonical.
2. `i` and `j` are isomorphisms to H^n of the whole Phi/Psi images. The two `HEq`
   clauses say their forward maps are precisely H^n of F applied to
   `(DerivedCategory.Plus.TStructure.t.truncLEι n).app K`, after the displayed
   total-degree and object equalities. `U` and `V` are `PBCDecreasingFiltration`s
   on those two cohomology objects. Their equalities to `.image i.hom` and
   `.image j.hom` say that the canonical abutment filtrations are transported.
   Their step equations give exactly the images of the canonical maps from
   truncation at `n - p`, for every integer p. The subsequent
   `Subobject.«exists»` equation uses the inverse of the canonical
   `mapDerivedCategoryPlusHomologyFunctorIso n`. It identifies U with inverse image
   along g of the image subobject defining the filtration on H^n(Rf_*K), including
   the exact functor's action on that subobject's inclusion.
3. `t : P.D 0 n ⟶ Q.D 0 n` is heterogeneously equal to the recorded exchange
   component `tD ... K 0 n`. The equality with `eqToHom (hA n)`,
   `eqToHom (hB n).symm`, `i.hom`, and `j.hom` is precisely the required
   abutment square. Its other side is H^n of exchange evaluated at K. Composition
   is written left-to-right with `≫`.
4. `lift p` restricts that same cohomology-of-exchange map to the p-th filtration
   steps; its equation with their monic inclusions is exactly preservation of
   filtration. `gr p` is characterized by the successive-step cokernel equation,
   so it is the induced graded map. `z p` is the restriction of the actual `tE`
   to limiting cycles, as specified by its inclusion equation (using hPE).
   `tInf p` is its quotient on limiting cycles modulo boundaries, specified by
   its cokernel equation. Finally `e`, `e'`, `hU`, `hV` and the two equations
   with `factorThruImageSubobject` specify the canonical comparisons on the
   transported filtrations. The final equation
   `(e p).hom ≫ gr p = tInf p ≫ (e' p).hom` is precisely the required E-infinity
   compatibility under those identifications.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, with its full functor signature.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded derived-category
  conventions; `DerivedCategory`, `DerivedCategory.Plus` and their homology functors.
  The `torsionCohomology` declaration is not used, since this node assumes no torsion.
- `Sheaf.AlgebraicGeometry.TruncationExchangeCouple`:
  `CategoryTheory.TruncationExchange.trunc`, `D`, `E`, `alpha`, `f`, `g`, `tD`, `tE`,
  `AlgebraicGeometry.Etale.truncationPhi`, `truncationPsi`, and
  `truncation_exchange_couple_morphism`, including its exact data identifications.
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`: the three actual derived
  functors, `CategoryTheory.hypercohomologyFiltration`,
  `AlgebraicGeometry.Etale.hypercohomologyFiltrations` and its specification.
  While this worker was running, NA's repaired PBC-filtration record and module
  appeared in the shared library; that published module is used, without duplicating it.
- `WeilConjectures.CategoryTheory.HalfPlaneConvergence`:
  `CategoryTheory.BigradedExactCouple.halfPlaneConvergence`, including normalized
  diagonal colimits and canonical infinite-page comparisons.
- `WeilConjectures.CategoryTheory.PBCFiltration`:
  `CategoryTheory.PBCDecreasingFiltration`, its step, finiteness, separation,
  exhaustivity and graded-piece definitions. This is the now-recorded dependency
  representation, identical to the convergence interface's representation.
- `WeilConjectures.CategoryTheory.ImageFiltration`:
  `CategoryTheory.PBCDecreasingFiltration.image`.
- `Sheaf.CategoryTheory.ExactCoupleMorphism`:
  `CategoryTheory.BigradedExactCouple.coupleMorphism`, restored in this delivery.
- Proof imports retain `derivedCoupleFunctoriality` from
  `Sheaf.CategoryTheory.DerivedCoupleFunctoriality`, negative vanishing from
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
  `lowerStar` from `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and
  `mapDerivedCategoryPlus` / `mapDerivedCategoryHomologyFunctorIso` from
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
  `WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage` supplies the canonical
  truncation-isomorphism criterion explicitly named in the node's current proof.

Edge cases checked before writing: K = 0; empty schemes; arbitrary negative a and n;
`n < a` (empty row interval and zero degree-n abutments); `n = a`; `p = 0`;
negative p, where truncation occurs above n and the image is the whole abutment;
`p > n - a`, where truncation is below the lower bound and the image is zero.
There is no restriction to nonnegative n or to nonnegative filtration indices, no
positive characteristic assumption, and no extra equality of site universes.
No mathematical statement fault or statement correction is required.

Searches (2026-10-17):

- `msearch.py ... leanfinder "truncation exact couple spectral sequence abutment
  comparison exchange morphism image filtrations"`: eight homological-complex
  truncation results, including `HomologicalComplex.shortComplexTruncLE_shortExact`;
  none states exchange abutment comparison.
- `msearch.py ... loogle "BigradedExactCouple, AlphaColimit, halfPlaneConvergence"`:
  zero results; Loogle does not know BigradedExactCouple.
- `msearch.py ... grep "exact.couple|ExactCouple|abutment|Abutment" Algebra/Homology`:
  zero Mathlib hits.
- `msearch.py ... leansearch "hypercohomology spectral sequence image filtration
  derived functor truncation"`: eight generic truncation results, no such filtration
  or exchange theorem.
- `rg -n 'exact.couple.abutment|exact_couple_abutment|abutment_comparison|truncation.*abutment'`
  in the upstream project and shared `lean/Sheaf`, and a separate grep of the item id
  in upstream: no upstream theorem; the shared historical
  `TruncationExchangeAbutment.lean` carries this statement. Read it in full and fetched
  its server source with `scompile.py --source`. Its declaration is unavailable in
  the compiler, and the historical source uses `DecreasingFiltration` where current
  convergence returns `PBCDecreasingFiltration`; it is therefore restored, rather than
  bound as `existing: true`. No second definition of any notion is added.

Validation: both delivered modules compiled separately in dependency order through
`scompile.py`, with no errors or warnings. All variables and universes are explicit;
`autoImplicit` is false in both files. Each theorem has its source and stepwise proof
plan in its docstring. The wrapper also checked the actual library module names.

## Dependency modules

`lem-sp-couple-morphism`: the recorded declaration
`CategoryTheory.BigradedExactCouple.coupleMorphism` was unknown after importing its
recorded module, as verified with `scompile.py`. The delivery restores its exact
statement in `Sheaf.CategoryTheory.ExactCoupleMorphism`, with current published imports
for exact-couple convergence and half-plane convergence. Only its node's `lean` changes;
`lean.note` records the compiler defect and the repair. No new definition is required.

The dependency hypotheses are precisely X, Y in one abelian category; bidegree-preserving
tD and tE; and the alpha, f and initialG commutative squares hα, hf, hg. The first
existential conclusion supplies every page map t, its initial-page equation,
differential compatibility, and the kernel/projection equations characterizing passage
to the next page. The conditional half-plane clause has separate bounds a and b with
exactly the D and E vanishing assumptions on the two sides. Its normalized diagonal
colimits and limiting subobjects give f, the actual abutment map, filtration-step
restrictions and the cocone-leg equations. The formula for f identifies it with
`tD 0 n`. The maps z and tInf are characterized by limiting-cycle inclusion and
boundary-cokernel equations. The comparison isomorphisms e/e' are characterized by
`toPageInfinity` and `toGradedPiece`; the toGradedPiece square and final e/gr/tInf square
state exactly compatibility of the induced graded map with the infinite-page map.
The statement applies also to zero couples, empty diagonal support and independent
negative lower bounds. The module's single theorem has proof `sorry` and a complete
three-step natural-language proof in its docstring.


## Second reading by Q22

Independent second reader, 2026-10-17. I opened the item JSON, its cited blueprint
source (both proofs, especially Detailed form), all nine statement-dependency nodes,
the delivered Lean, and the dependency repair. Verdict: the Lean says what the node
says. No statement, hypothesis, definition, or proof has been changed in this reading.
Only this report section is added.

My object/hypothesis/conclusion checklist, matched against the actual signature:

1. Four schemes and the Cartesian square, including its chosen identification:
   `{X' X Y' Y : Scheme.{u}}`, the four morphisms, and
   `sq : ChosenCartesianSquare g' f' f g`. I read that structure's `isoPullback`,
   `hom_fst`, `hom_snd`, and inherited `CommSq`; it gives precisely the node's square.
   Verdict: exact, with no properness, Noetherian, or separatedness hypothesis.
2. The actual derived composites and exchange: I opened `truncationPhi`,
   `truncationPsi`, `tD`, `tE` and `derivedBaseChangeMapPlus`. Phi is
   `lowerStar ... f |>.rightDerivedFunctorPlus`, followed by
   `(upperStar ... g).mapDerivedCategoryPlus`; Psi has the opposite order with
   g' and f'. Every exchange occurrence uses the recorded transformation evaluated
   on `sq.toCommSq`, not an arbitrary map. Verdict: exact.
3. The bounded-below object, chosen lower bound, and fixed total degree are
   `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`,
   `a n : ℤ`, and `hK : ∀ q, q < a → IsZero (...homologyFunctor ... q).obj K`.
   Verdict: exact. The node has no torsion assumption, and the Lean adds none.
4. The two particular exact couples are `P Q : BigradedExactCouple ... 0`.
   `hPD`, `hPE`, `hQD`, `hQE` identify their two object families, and the six
   heterogeneous equalities identify alpha, f, and g on both sides. I read the
   dependency definitions: D is H^(p+q)(F tau<=q K), E is
   H^(p+q)(F(H^q(K)[-q])), alpha comes from consecutive truncations, g from the
   layer projection, and f from the connecting arrow with F's shift comparison.
   The existence of these couples is supplied by
   `truncation_exchange_couple_morphism`. Verdict: these parameters specify exactly
   the couples named by the node; they add no assumption about the geometry.
5. Clause (1), vanishing and convergence: the first four conjuncts give precisely
   D = 0 below a and E = 0 for p < 0 or q < a on both sides. The existential
   `L M A B hA hB` and zeroth-leg equations give actual limiting subobjects and
   normalized diagonal colimits on D^(0,m). `P.ConvergesTo L A` and its Q version,
   the finiteness/exhaustivity/separation conjuncts, and the two comparisons
   characterized by `toPageInfinity ≫ e.hom = toGradedPiece` render the remaining
   assertions. I fetched and read the current `halfPlaneConvergence` and
   `ExactCoupleConvergence` sources using `scompile.py --source`. Their
   `LimitSubobjects` are the actual greatest lower bound of cycles and least upper
   bound of boundaries, and `pageInfinity` is their quotient. Verdict: exact;
   the finite row interval follows from p >= 0, q >= a, and p+q=n.
6. Clause (2), canonical identification with whole-complex cohomology: `i j` are
   isomorphisms, and their `HEq` equations specify H^n of the actual
   `truncLEι n` maps. `U V` equal the images of the respective diagonal
   filtrations under `i.hom`, `j.hom`. Their step equations specify images of
   H^n(F(truncLEι (n-p))), for every integer p. The subsequent
   `Subobject.«exists»` equation uses the inverse of the canonical
   `mapDerivedCategoryPlusHomologyFunctorIso n` at Rf_*K, and equates the transported
   U-step with the image of g inverse image of the original image inclusion.
   I checked the comparison's direction in ExactFunctor: it is H^n followed by
   upperStar isomorphic to derived upperStar followed by H^n, so `.symm` here
   goes from H^n(Phi K) to g inverse image of H^n(Rf_*K). Verdict: exact, including
   the requested identification of the first filtration.
7. Clause (3), identification of the abutment map: `t` is `HEq` to the recorded
   `tD ... K 0 n`. Its equation with `eqToHom (hA n)`, `eqToHom (hB n).symm`,
   `i.hom`, and `j.hom` is the canonical abutment square with H^n(exchange_K).
   Verdict: exact; the transports account for the normalized colimit objects.
8. Clause (4), preservation and the graded map: `lift p` and its monic-inclusion
   equation give preservation of U.step p by H^n(exchange_K). The cokernel
   equation for `gr p` specifies the induced map on U^p/U^(p+1). The equations
   for `z p` and `tInf p` identify restriction of the actual tE to limiting
   cycles and its descent modulo boundaries. The comparisons `e e'`, normalized
   by their equations with `toPageInfinity`, image factorizations and cokernel
   projections, are the comparisons on U and V transported from clause (1).
   The final `(e p).hom ≫ gr p = tInf p ≫ (e' p).hom` is exactly the requested
   compatibility. Verdict: exact; none of the displayed maps is left arbitrary.

Source and inherited hypotheses: I also read Stacks `etale-cohomology.tex` at
`lemma-proper-base-change` (0DDE), `derived.tex` at `lemma-negative-vanishing`
(05TC, both parts) and `lemma-right-derived-exact-functor` (015F), and
`homology.tex` at `definition-exact-couple`, `lemma-derived-exact-couple`,
`lemma-spectral-sequence-associated-exact-couple`, `definition-filtered`, and
`definition-filtration-cohomology-filtered-differential` (011Q--011T, 0121, 012E).
The node's source is its blueprint Detailed form. The extra properness and torsion
in 0DDE are needed for its base-change-isomorphism conclusion, not for this
naturality/convergence comparison; the blueprint and 05TC justify the present
hypotheses. No source-based correction or citer audit is needed.

Dependency repair, H13: I read `lem-sp-couple-morphism` against its blueprint source
and the delivered `ExactCoupleMorphism.lean`. It has arbitrary objects in one abelian
category, independent object and morphism universes u and v, bidegree-preserving tD/tE,
and exactly the three alpha/f/initialG squares. The first existential t gives every
page, the initial tE normalization, differential compatibility, and kernel/projection
squares determining passage to cohomology. Its conditional half-plane clause has
independent bounds a and b, both D/E vanishings, normalized diagonal colimits, the
map f identified with tD^(0,n), and its cocone and filtration-step equations.
The z and tInf equations specify the map on limiting cycles and their quotients.
The normalized e/e' and toGradedPiece equations give precisely the graded
compatibility requested by the node. `LimitSubobjects` and normalized `AlphaColimit`
are canonical by their universal properties, so these are the half-plane abutments.
I fetched the historical dependency source: its theorem has the same signature but
obsolete imports (the source-library migration withdrew its compiled declaration).
The repair replaces these by the published ExactCouple, PBCFiltration,
ExactCoupleConvergence and HalfPlaneConvergence modules. This is an interface
restoration under §1(B), not a competing definition. There are no new definition nodes.

Edge cases: all degree and filtration indices are integers. K=0, empty schemes,
negative a and n, n=0, n<a (empty supporting row interval), n=a, p=0, negative p,
and p>n-a remain included. For negative p truncation is above n and its image is
all of H^n; past n-a it is zero. No field, ring characteristic, or positive-degree
restriction appears. `Scheme.{u}` is arbitrary in u, with the established
AddCommGrpCat.{u+1} convention for these small sites; no independent test universe
or equality of site-object and morphism universes is imposed. The repaired generic
couple theorem also covers zero couples and different negative bounds a and b.

Independent searches, with different wording from the worker:

- LeanFinder: `naturality of spectral sequence convergence with truncation filtration
  and base change`: eight truncation-naturality declarations, including
  `HomologicalComplex.ιTruncLE_naturality`; no abutment/exchange comparison.
- Loogle: `imageSubobject, Functor.map`: zero results (identifier unavailable to its
  index); this is not treated as positive existence evidence.
- LeanSearch: `A morphism of exact couples induces a filtration preserving morphism
  of abutments compatible with the infinite page`: eight short-complex or
  homological-complex homology/cycle maps; no exact-couple abutment theorem.
- Direct rg across Mathlib Algebra/Homology, the upstream WeilConjectures tree, and
  shared lean/Sheaf, for `truncation.*(abutment|converg)`,
  `exchange.*(filtration|graded)`, `coupleMorphism`, and the exact theorem name:
  shared historical versions of these two withdrawn statements and related generic
  truncation-cocone lemmas; no alternative theorem covering the node. Opened the
  historical dependency and relevant recorded declarations rather than counting
  a matching name as an available match. Current PBCFiltration and ImageFiltration
  were also fetched and read; their existing notions are reused verbatim.

H5/H6/H8/H9 check: neither delivered module defines data, and both theorem proofs
are exactly `sorry`. Both have source/blueprint module and declaration docstrings,
with the node's proof steps. Universes are bound and autoImplicit is false.
Both node `lean.statement` records are verbatim equal to the actual theorem signatures; every Lean line is at most 100 characters.
Both delivered modules were compiled separately, in dependency order, in one
`scompile.py Q22 lemma-weil-pbc-exact-couple-abutment <both files>` invocation:
all overlay, preliminary, sandbox, and library checks succeeded, without warnings.
