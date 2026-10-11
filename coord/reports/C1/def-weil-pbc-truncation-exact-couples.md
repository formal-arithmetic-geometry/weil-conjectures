## Worker report

Existing declarations: `Sheaf.AlgebraicGeometry.TruncationExchangeCouple` already
contains every piece of this definition. No module is delivered and no notion is
redefined. The primary recorded signature is `CategoryTheory.TruncationExchange.D`;
`lean.declarations` lists the other components. This follows the bundling rule in
STATE (STAGE 2, FIRST DELIVERIES): record the existing declarations of all clauses.

Hypotheses and clauses, with `TE = CategoryTheory.TruncationExchange`:

- Schemes and the four maps are the binders of `AlgebraicGeometry.Etale.truncation_exchange_couple_morphism`.
  Its `sq : IsPullback g' f' f g` encodes the cartesian square, including commutativity
  through `sq.toCommSq`. Its K is precisely D+ of abelian etale sheaves on X.
- Phi is `AlgebraicGeometry.Etale.truncationPhi f g`, namely lowerStar's
  rightDerivedFunctorPlus followed by upperStar's mapDerivedCategoryPlus.
  Psi is `AlgebraicGeometry.Etale.truncationPsi g' f'`, with those operations reversed.
  Their `CommShift ℤ` structures are the composite structures, used by TE.f.
- The integer q is unrestricted. TE.trunc is the standard D+ truncLE. TE.sheaf is
  H^q(K) placed in degree zero; TE.layer is that object shifted by -q.
  TE.inclusion, TE.projection and TE.boundary are i_q, j_q and k_q.
  The last two select actual morphism data from the named TE.exists_triangle theorem;
  they do not contain sorry as data.
- TE.D F K p q is H^{p+q}(F(trunc K q)); TE.E F K p q is
  H^{p+q}(F(layer K q)). Specializing F to Phi and Psi gives D_A/E_A and D_B/E_B.
- TE.alpha is H^{p+q}(F i_{q+1}), with transports for
  q=(q+1)-1 and p+q=(p-1)+(q+1). TE.g is H^{p+q}(F j_q).
- TE.f is H^{p+q}(F k_q followed by F.commShiftIso 1), followed by the
  homology shift isomorphism with target degree (p+2)+(q-1)=p+q+1.
  Thus its bidegree is exactly (2,-1).
- A_q and B_q are the objects of Phi/Psi on TE.trunc K q; G_q and H_q
  are their objects on TE.layer K q. These are notation, not additional constructions.
  The first differential is TE.f F K p q followed by TE.g F K (p+2) (q-1),
  matching the type-zero convention of `CategoryTheory.BigradedExactCouple.d`.
- For t = `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus
  AddCommGrpCat sq.toCommSq`, TE.tD t K p q is H^{p+q}(t on the truncation)
  and TE.tE t K p q is H^{p+q}(t on the layer), exactly the displayed pair.
- The final paragraph explicitly defers exactness, the three commuting squares,
  and the identification with degree-p exchange to the dependency theorem
  `AlgebraicGeometry.Etale.truncation_exchange_couple_morphism`. That existing theorem
  states all three claims; TE.pageIso, truncationSourceIso and truncationTargetIso
  supply the canonical identifications. No extra assertion is added here.

Dependency declarations read and used: the recorded squareUpperStarIso in
`WeilConjectures.SixFunctors.BaseChange.Square`; mapDerivedCategoryPlus in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
lowerStar and rightDerivedLowerStarPlus in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; the CommShift and
IsTriangulated instances in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`;
DerivedCategory.TStructure.t and DerivedCategory.homologyFunctor in Mathlib;
DerivedCategory.truncation_triangle in `Sheaf.CategoryTheory.TruncationTriangle`;
CategoryTheory.BigradedExactCouple in `Sheaf.CategoryTheory.ExactCouple`;
derivedBaseChangeMapPlus in `WeilConjectures.SixFunctors.BaseChange.Derived`;
and the component declarations and final theorem in the recorded existing module.
The category encoding agrees with `Sheaf.AlgebraicGeometry.DerivedCategories`.

Edge cases: p and q are arbitrary integers, including negative p and q=0;
there is no first-quadrant or lower-bound binder added. K=0, an empty scheme,
and arbitrary cartesian squares are allowed. Degree transports preserve total
degree for alpha and increase it by one for f. No coefficient ring is imposed:
the specialization uses AddCommGrpCat, exactly the node's abelian sheaves.

Searches:

- msearch leanfinder: "two truncation exact couples of derived functors with exchange
  natural transformation": eight hits concerning shortExact truncations and
  homological functors, none defining these data.
- msearch loogle: "ExactCouple, truncationExactCouples": zero hits, unknown ExactCouple.
- msearch grep: "ExactCouple|truncationExactCouples": zero Mathlib hits.
- rg in WeilConjectures for truncationPhi, truncationPsi, BigradedExactCouple and
  truncation_exchange, and the exact node id: no matches defining this notion.
- rg in lean/Sheaf for the same patterns: found the already landed
  TruncationExchangeCouple module. Read its full definitions and theorem. The older
  TruncationCouple module uses chosen resolutions and was not substituted for these
  D+ declarations.

Validation: an experimental wrapper of these existing declarations compiled cleanly
on the server (2 seconds), then was removed because it was redundant. The delivery
contains only the existing-declaration record and this report. No statement correction,
new nodes or dependency modules. No STATEMENT-DISPUTED flag.

## Second reading by C1

I independently opened the sandbox node, every statement-dependency node, and
`Sheaf.AlgebraicGeometry.TruncationExchangeCouple` in full. The delivery is an
existing-declaration record, not a new module. I also read the original blueprint
node on the server and Stacks `etale-cohomology.tex`,
`lemma-proper-base-change` (0DDE), and `derived.tex`,
`remark-truncation-distinguished-triangle` (08J5), in the available source copies.
The blueprint's q >= a is a truncation-filtration starting bound; the reviewed
stage-1 statement defines the data for every integer q. Stacks 08J5 supports that
extension. Stacks 0DDE assumes proper f and torsion cohomology to assert that
exchange is an isomorphism. Those assumptions are not needed to define either
couple or the exchange maps, and the present node asserts no such isomorphism.

Clause checklist (TE means the global namespace
`CategoryTheory.TruncationExchange`, not a new Lean alias):

1. Four schemes, maps f : X -> Y, g : Y' -> Y, f' : X' -> Y',
   g' : X' -> X, and the chosen cartesian square: the binders of
   `AlgebraicGeometry.Etale.truncation_exchange_couple_morphism` have exactly
   those types and `sq : IsPullback g' f' f g`. `sq.toCommSq` supplies the
   commuting square to exchange. Pullback uniqueness supplies the specified
   identification with the fibre product; no additional geometric property is
   required. Verdict: matches.
2. K in D+(X_et) of abelian sheaves: the same theorem binds
   `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
   AddCommGrpCat.{u + 1})`. This is the abelian-sheaf case of the recorded
   `DerivedCategories` module, not its coefficient-module variant. Verdict: matches.
3. Phi = inverse image after derived direct image and Psi = derived direct image
   after inverse image: `truncationPhi f g` is
   `(lowerStar AddCommGrpCat f).rightDerivedFunctorPlus` followed by
   `(upperStar AddCommGrpCat g).mapDerivedCategoryPlus`; `truncationPsi g' f'`
   has the reverse order with g' and f'. Lean composition orders the functors
   in the order they act. Verdict: matches.
4. The composite shift isomorphisms xi and zeta: `TE.f` uses
   `F.commShiftIso (1 : ℤ)`. I read the right-derived CommShift instance,
   transported from the injective-object model, and the exact-functor D+
   restriction instance; composite instances give the specified composites.
   There is no freely chosen shift structure at the scheme specialization.
   Verdict: matches.
5. Every integer q, canonical tau <= q, cohomology sheaf, and T_q:
   `TE.trunc K q` is the standard D+ t-structure's `truncLE`; `TE.sheaf K q`
   is H^q(K) through `singleFunctor _ 0`; `TE.layer K q` shifts this by -q.
   `TE.inclusion K q` uses `natTransTruncLEOfLE (q-1) q`.
   `TE.projection` and `TE.boundary` select j and k from the named
   `TE.exists_triangle K q`, whose conclusion specifies a distinguished
   triangle and normalizes H^q(j) by the canonical inclusion into K.
   This is the canonical truncation projection: the standard t-structure
   identifies maps from tau <= q K to the pure degree-q layer with maps on
   H^q. With this projection and inclusion, the boundary is canonical too.
   Verdict: matches; these are actual chosen morphisms, not sorry-valued data.
6. D_F^{p,q} and E_F^{p,q}: `TE.D F K p q` is precisely H^{p+q} of
   F(trunc K q), and `TE.E F K p q` is H^{p+q} of F(layer K q).
   Specialize F to Phi and Psi for A and B. Verdict: matches.
7. alpha_F: `TE.alpha` applies H^{p+q} to F(i_{q+1}) with equality
   transports q = (q+1)-1 and p+q = (p-1)+(q+1).
   Its target is `D F K (p-1) (q+1)`. Verdict: matches.
8. g_F: `TE.g` is H^{p+q}(F(projection K q)) from D to E at
   the same indices. Verdict: matches.
9. f_F: `TE.f` is H^{p+q} of F(boundary K q) followed by the
   composite CommShift map, then the homology shift isomorphism.
   Its target indices are (p+2,q-1), whose total degree is p+q+1.
   Verdict: matches, including the order of composition and shift sign.
10. A_q, G_q, B_q, H_q are the corresponding objects of Phi/Psi on
    `TE.trunc`/`TE.layer`. They are names for the four displayed expressions,
    not missing mathematical definitions. The first differential is
    `TE.f F K p q ≫ TE.g F K (p+2) (q-1)`, exactly the type-zero
    `BigradedExactCouple.d` after the data identifications in the existing
    theorem. Verdict: matches; the first couple page is conventional E_2.
11. The exchange pair: specialize `TE.tD` and `TE.tE` to
    `derivedBaseChangeMapPlus AddCommGrpCat sq.toCommSq`. Their bodies are
    H^{p+q} of the transformation on `TE.trunc K q` and `TE.layer K q`
    respectively. Verdict: matches, without an isomorphism hypothesis.
12. The final deferred claims are exactly the dependency theorem
    `truncation_exchange_couple_morphism`: its first conjunct gives two
    type-zero exact couples with all five data identified, its next three
    conjuncts give the alpha, g and f squares, and its last conjunct gives
    the degree-p exchange comparison via `TE.pageIso`,
    `truncationSourceIso`, and `truncationTargetIso`. The sourceIso hom/inv
    pair on the right cancels, leaving exactly the claimed transported
    H^p(exchange on H^q(K)). Verdict: matches all three deferred claims.

Dependency check: I opened the recorded `squareUpperStarIso` signature and
body (the square's inverse-image comparison); `mapDerivedCategoryPlus`
(the restriction of the exact induced functor), its shift instance;
`lowerStar` (continuous sheaf pushforward along site base change);
`rightDerivedFunctorPlus` shift/triangulated structures;
`DerivedCategory.TStructure.t` (standard cohomological t-structure);
`DerivedCategory.homologyFunctor` and its complex factorization;
`DerivedCategory.truncation_triangle`; `BigradedExactCouple` and `d`;
`derivedBaseChangeMapPlus` and its underived-on-resolutions characterization;
and the full recorded couple-morphism module. None supplies a stronger
hypothesis or a different notion at this specialization. The generic
HasDerivedCategory, Abelian, and shift requirements are supplied by the
existing scheme/sheaf instances; the specialized theorem adds none as
hypotheses on the square or K.

Edge cases: p and q range over all integers, including p < 0 and q = 0.
Zero K and empty schemes are admitted by the same binders; no nonempty,
Noetherian, proper, finite-type, torsion, field, or characteristic restriction
appears. No index family is involved, so an empty indexing set is inapplicable.
The generic data use independent object, hom, and derived-category universes;
Scheme.{u} with abelian groups at u+1 is the project's shared small-etale-site
encoding and can be lifted for any square. No extra lower bound or first-quadrant
condition is imposed.

Independent searches with different words:

- msearch leansearch: "bigraded cohomology groups from consecutive truncation
  triangles and base change". Service returned Internal Server Error; recorded
  as unavailable, with no mathematical negative verdict.
- msearch loogle: '"couple"'. Only `Derivation.couple`, an unrelated Lie
  subalgebra of derivations.
- msearch grep: `truncation.*couple|couple.*truncation|exchange.*spectral`.
  No Mathlib hits.
- rg with those expressions and `TruncationExchange` in WeilConjectures and
  lean/Sheaf: the landed exchange-couple module supplies precisely these data.
  I also opened the older `TruncationCouple` module: its domain is chosen
  bounded-below complexes/resolutions, so it is not substituted for the
  present D+ construction.

Faults and changes: no mathematical mismatch found. I kept the existing record,
its verbatim D signature, and all Lean declarations unchanged; added this
independent checklist and fresh search/validation evidence to the report.
No new nodes, dependency modules, statement correction, or disputed statement.
All definitions have actual data; named auxiliary theorem proofs remain sorry.
The existing module's source/blueprint docstrings correctly belong to its original
couple-morphism node; duplicating it just to change a docstring would violate H4.
Its theorem docstring contains the five proof steps of that dependency. The
present definition node has no proof steps. No new theorem or proof is delivered.

Validation: compiled a scratch import of the existing module with #check for
all 19 recorded declarations plus `TE.exists_triangle` and `TE.layerIso`, using
scompile.py on the server. Exit code 0, compiled in 2.0 seconds, no warnings.
The scratch file is outside the delivered lean directory. No unbound variable
or universe was found in the source signatures (autoImplicit is disabled).
