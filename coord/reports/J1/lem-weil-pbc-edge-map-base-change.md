## Worker report

Module `Sheaf.AlgebraicGeometry.EtaleEdgeMapBaseChange` states the cohomological base-change
identity and its finite-morphism consequence. Both theorem proofs are `sorry`. No definition,
new node, dependency module, or statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Four arbitrary schemes are `X' X Y' Y : Scheme.{u}`; the four arrows are `g'`, `f'`, `f`,
  and `g`, with precisely the sources and targets displayed in the node.
- The cartesian square is `sq : IsPullback g' f' f g`. Its `sq.toCommSq` supplies the
  equality `g' ≫ f = f' ≫ g`. This is equivalent to the chosen pullback identification
  in the node: a pullback cone has its unique comparison isomorphism with the chosen
  categorical pullback. No extra datum can change the specified square isomorphism.
- The specified theta is the upstream `squareUpperStarIso AddCommGrpCat sq.toCommSq`,
  used internally by `baseChangeMap`. Upstream `upperStarComp` has the inverse orientation
  to the node's c: its hom goes from diagonal pullback to iterated pullback. The definition
  `squareUpperStarIso = (upperStarComp f' g diagonal sq.w).symm ≪≫ upperStarComp g' f`
  therefore gives precisely `c_{f,g'}^{-1} ∘ c_{g,f'}`.
- The abelian sheaf is `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`. There are
  no torsion, constructibility, field, dimension, properness, or separation hypotheses.
- The exchange is exactly `(baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F`;
  its sheaf source and target are `g^* f_* F` and `f'_* g'^* F`.
- Cohomological pullback is the dependency's `cohomologyMap`. An edge map is spelled out
  as `(Sheaf.H.map (upperStarLowerStarAdjunction ... f).counit.app F q).comp
  (cohomologyMap f (lowerStar ... f |>.obj F) q)`, with parentheses as in the module.
  No alternative edge-map notion is introduced.
- Every nonnegative degree is `q : ℕ`, including zero. `Sheaf.H.map` renders the induced
  map on cohomology of a sheaf morphism. The first theorem equates additive homomorphisms:
  the left is `g'^* ∘ H^q(ε_f) ∘ f^*`, and the right is
  `H^q(ε_f') ∘ f'^* ∘ H^q(Ex^0) ∘ g^*`. Both have exactly the node's source and target.
- The identity theorem has no hypothesis on `f`.
- The finite clause is the second theorem: `[IsFinite f]` and
  `hEx : IsIso ((baseChangeMap ... sq.toCommSq).app F)` are precisely its two hypotheses.
  Finiteness of `f'` is a consequence, not an added hypothesis. The conclusion states
  bijectivity of `e_f` and `Ψ = e_f' ∘ H^q(Ex^0)`. These are additive maps, so bijectivity
  gives additive equivalences via `AddEquiv.ofBijective`. The first theorem is exactly
  `g'^* ∘ e_f = Ψ ∘ g^*`, so the two pullback maps are identified through these canonical
  isomorphisms, as in the node's proof step 7. The two declarations together state every
  clause; the finite consequence does not assert bijectivity of either horizontal map.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.BaseChange.Square`:
  `AlgebraicGeometry.Etale.squareUpperStarIso`, `baseChangeMap`, and the docstring/signature
  of `upperStar_map_baseChangeMap_app_counit`. The first two implement the recorded
  cartesian-square and underived-exchange notions.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`,
  `lowerStarComp`, `upperStarComp`. These enter through the square module; no redundant
  direct import is added.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `AlgebraicGeometry.Etale.cohomologyMap`, `cohomologyMap_map` (the latter read for the
  intended proof, not used in a proof at stage 2).
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `AlgebraicGeometry.Scheme.smallEtaleTopology`;
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `CategoryTheory.Sheaf.H.map`.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`:
  `CochainComplex.IsKInjectiveResolution` was read in full. It is used only in the node's
  intended proof, not in the signature of this resolution-independent statement; no
  unused import is added.
- `lem-weil-pbc-cohomology-pullback-functorial` has no `lean` or `mathlib_match` record on
  the supplied base. This is a stage-2 readiness inconsistency: it is a statement used
  in the intended proof, not a missing notion needed to write this item's signature.
  The dependency's entire statement was read; no private replacement or partial
  restatement is introduced. All notions needed here already have usable declarations.

Edge cases checked before writing: degree zero is included and gives the ordinary section
identity; the zero sheaf yields maps between trivial cohomology groups; empty schemes are
allowed; identity squares use the canonical inverse-image composition isomorphisms. The
finite theorem allows arbitrary base change and no characteristic restriction. Universes
follow the recorded abelian-sheaf encoding, with schemes in `u` and coefficients in `u+1`.
The theta orientation was checked against the full upstream definition, not just its name.

Source: [Stacks Lemma 0A5D](https://stacks.math.columbia.edu/tag/0A5D), Section 03SB,
proof invoking finite direct-image base change. The local Stacks TeX file was absent, so
this exact source was read online. The node expands the implicit compatibility there
using naturality, composition, and the adjunction triangle identity; the declaration
comments contain all seven proof steps and the dependency identifiers.

Searches for an existing statement (2026-10-11 UTC):

- `msearch.py leansearch`, query `sheaf cohomology edge map commutes with cartesian base
  change`: service unavailable, Internal Server Error; no mathematical verdict assigned.
- `msearch.py leanfinder`, query `edge map of direct image on etale sheaf cohomology
  commutes with base change`: eight hits, all scheme presheaf naturality/appLE facts;
  none about this cohomological identity.
- `msearch.py loogle`, query `Sheaf.H.map, AlgebraicGeometry.Etale.cohomologyMap`:
  no hits, unknown identifier `Sheaf.H.map` in its search index.
- `msearch.py grep`, regex `edgeMap|baseChange.*cohomology|cohomology.*baseChange` in
  Mathlib `CategoryTheory`: no hits.
- `rg` with `edgeMap|edge_map|cohomology.*[Bb]aseChange|[Bb]aseChange.*cohomology|
  lem-weil-pbc-edge-map-base-change` in the source `WeilConjectures` and project
  `lean/Sheaf`: found the existing low-degree edge results, finite-edge bijectivity in
  `CohomologyClopen`, unrelated tensor/hypercohomology base-change statements, and this
  item's citation in `FinitePushforwardAssertions`; no declaration of this identity.
  The upstream edge formula in `EdgeMap` is the same formula written here, so it is
  used directly rather than defining an edge map again.

Validation: `scompile.py J1 lem-weil-pbc-edge-map-base-change` on the single module passed
in 3.2 seconds with exit code zero and no warnings. Every universe and binder is explicit.

## Second reading by J1

Independent second reading on 2026-10-12. I opened the item node, all nine statement
dependency nodes, their recorded signatures and relevant implementations, and the full
 delivered Lean module. No mathematical mismatch was found; the Lean and node are unchanged.

Source check: the local Stacks TeX is absent on this machine. I read the upstream
[etale-cohomology.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex),
the section `section-vanishing-torsion`, Situation `situation-what-to-prove`, and
`lemma-finite-pushforward-statements` (tag 0A5D), including its proof. The surrounding
application has an algebraically closed field, separated finite type schemes of dimension
at most one, and a torsion sheaf. This node explicitly extracts the general compatibility
of edge maps used in that application, rather than stating its curve assertions: none of
those application hypotheses belongs in this identity. Its formal proof uses only the
canonical adjunction, naturality, and composition. I also read
[0959](https://stacks.math.columbia.edu/tag/0959), which assumes only a cartesian square
and a finite vertical morphism for the exchange isomorphism. Thus the finite consequence
here correctly has no field, characteristic, dimension, or torsion hypothesis.

Objects, hypotheses, and conclusion clauses, matched in the order of the node:

1. Schemes `X', X, Y', Y` and arrows `g', f', f, g` are exactly the four scheme and
   morphism binders in both declarations. Verdict: correct, with no extra properties.
2. The cartesian square and chosen pullback identification are rendered by
   `sq : IsPullback g' f' f g`. With its fixed arrows the identification with the chosen
   categorical pullback is unique; hence no independent choice is lost. `sq.toCommSq`
   supplies the commuting equality. Verdict: correct.
3. The specified theta is the one in `baseChangeMap ... sq.toCommSq`. I read
   `squareUpperStarIso` in `BaseChange/Square.lean` and `upperStarComp` in
   `UpperLowerStar/Defs.lean`. The latter goes from diagonal inverse image to iterated
   inverse image (the inverse of the node's c). The former is the inverse of the
   `(f',g)` comparison followed by the `(g',f)` comparison, so its hom is exactly
   `c_{f,g'}^{-1}` after `c_{g,f'}`. Verdict: correct orientation and canonical choice.
4. `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` is an arbitrary abelian
   sheaf on the recorded small etale site. I read Mathlib's full-subcategory `Sheaf`
   and `smallEtaleTopology` definitions, not just their names. Verdict: correct.
5. The underived exchange is `(baseChangeMap AddCommGrpCat.{u + 1}
   sq.toCommSq).app F`. Its definition as `mateEquiv` and its adjunct-counit identity
   show that it is precisely the prescribed exchange, with source `g^* f_* F` and
   target `f'_* g'^* F`. Verdict: correct; it is not an arbitrary comparison map.
6. For each edge map the Lean uses `(Sheaf.H.map (adjunction.counit.app E) q).comp
   (cohomologyMap u ((lowerStar ... u).obj E) q)`. I read `lowerStar`, `upperStar`,
   `upperStarLowerStarAdjunction`, `cohomologyMap`, and `Sheaf.H.map`. These are the
   recorded dependency notions, and the same edge formula appears upstream in
   `UpperLowerStar/EdgeMap.lean` and `Sites/CohomologyClopen.lean`. Verdict: correct;
   no duplicate edge definition or private resolution choice is introduced.
7. Every nonnegative degree is `q : ℕ`. The first theorem equates additive homomorphisms
   from `Sheaf.H ((lowerStar ... f).obj F) q` to
   `Sheaf.H ((upperStar ... g').obj F) q`. Reading `.comp` from right to left gives
   `g'^*` after `e_f` on the left and `e_f'` after `H^q(Ex^0)` after `g^*` on the right.
   Verdict: exactly the complete identity with the correct sheaves at each intermediate
   group, for every F and q, and with no hypothesis on f.
8. The finite clause uses `[IsFinite f]` and `hEx : IsIso (...app F)` only. It concludes
   `Function.Bijective e_f ∧ Function.Bijective (e_f' ∘ H^q(Ex^0))`. These are the two
   canonical additive isomorphisms identifying the horizontal maps in theorem one;
   bijectivity is equivalent to existence of the corresponding `AddEquiv` with that
   underlying map. Verdict: complete combined with theorem one, with no assumption of
   finiteness on f' beyond its consequence from the square, and no assertion that the
   horizontal pullbacks are bijective.

Dependencies: I read the recorded inverse-image composition, direct-image, inverse-image,
cartesian-square, exchange, abelian-sheaf, and cohomology-pullback nodes against the upstream
modules listed above. The cohomology-pullback record explicitly chooses the existing Ext
encoding `cohomologyMap`, with the resolution comparison reserved for stage 3; this delivery
uses that encoding consistently. I also opened `KInjectiveResolutions.lean`: its resolution
abbreviation is `QuasiIso f ∧ I.IsKInjective`, using Mathlib's K-injectivity rather than a
second notion. It occurs only in the proof plan, so no unused import is needed.

The worker report's claim that `lem-weil-pbc-cohomology-pullback-functorial` has no Lean
record is stale: the current base records `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.
I opened that module and its signature. Its naturality, composition, and identity clauses
use the same `cohomologyMap` and inverse-image composition as this delivery. Its documented
resolution comparison is not a parameter needed in this resolution-independent signature;
there is no missing notion to supply here. No new definition nodes, dependency modules,
statement correction, or citer-verdict review is part of this delivery.

Edge cases: q = 0 is included and gives the section-level adjunction identity. Zero sheaves
and empty schemes are allowed by the binders; neither declaration has a nonemptiness
assumption. Identity squares use the same canonical composition comparisons. There is no
index set to restrict, no coefficient ring or field specialization, and no restriction on
characteristic. `universe u` is arbitrary; the `u+1` abelian-sheaf encoding is exactly the
recorded dependency convention, and any collection of four schemes can be taken in a common
universe. All variables, schemes, morphisms, and degrees are explicitly bound.

Independent searches, using different wording from the worker:

- LeanSearch: `Leray cohomology comparison and Beck Chevalley transformation compatibility`.
  Service returned Internal Server Error; recorded as unavailable, with no absence verdict.
- LeanFinder: `naturality of the Leray comparison homomorphism under inverse image in a
  pullback square`. Eight hits concerned module-sheaf pullback composition, free-sheaf
  naturality, over-site pullback, and sheafification; none states this cohomological identity.
- Loogle: `"cohomologyMap"`. No indexed match.
- Mathlib grep through msearch: `BeckChevalley|Beck.Chevalley|Leray|leray`. Three hits were
  comments in adjunction mates, bicategorical mates, and over categories; no statement match.
- Direct rg on upstream `WeilConjectures`, project `lean/Sheaf`, and Mathlib's site modules:
  `Leray|leray|edgeMap|edge_map|cohomology_edgeMap_baseChange|bijective_edgeMap_baseChange`.
  I opened the closest upstream declarations: low-degree injectivity and finite-edge
  bijectivity. Neither includes a square or this identity. Project results were spectral
  sequences and applications, not another statement of the node. No existing replacement.

H5/H6/H8/H9 checks: the module contains no definitions, only two theorem proofs `by sorry`.
The module and both declaration docstrings name 0A5D and the exact blueprint identifier;
steps 1--6 are carried by the identity theorem and step 7 by the finite theorem, with the
needed dependency names. No local notation, local instance, private notion, hidden let,
or extra import was introduced. The finite-morphism import supplies `IsFinite`; the square
import supplies all the canonical map notions. All lines are at most 100 characters.

Changes: appended this independent second reading, including the correction to the stale
report-only dependency status. No Lean or node changes were necessary. The maintainer's
signature reader confirms `lean.statement` is verbatim equal to the normalized primary
signature; both theorem names are present in `lean.declarations`. The single-file server
compile passed in 3.4 seconds, exit code zero, with no warnings.
