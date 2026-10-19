## Worker report

The module `Sheaf.Paper.CompleteCompactSupportProetale` states
`AlgebraicGeometry.Scheme.completeCompactSupportProetale_isIso`.  It uses the published
completed-coefficient compact-support map
`AlgebraicGeometry.Scheme.completedCompactSupportExchange` from
`Sheaf.Paper.CompletedCompactSupportExchange`.  The theorem quantifies a commutative
coefficient datum `d`, schemes and the four square morphisms, a compactification and its
base-changed compactification with the supplied proper and open Cartesian squares, and
`IsSeparated f`, `LocallyOfFiniteType f`, and `QuasiCompact f`, a finite generating tuple `(r,a,ha)` (including `r = 0`), a complete-object subcategory
object `K`, and compatible retained etale origins.  Its conclusion has two clauses:

* `IsIso (completedCompactSupportExchange ...)` is the isomorphism assertion for the
  ordered proper-exchange/open-comparison composite;
* for every object `H` and morphism `k : K.obj ⟶ H.obj`, the displayed equality compares
  source action followed by the exchange at `H` with the exchange at `K` followed by
  target action.  This is the naturality clause in `K`.

The source compact-support square is rendered by
`ChosenCartesianSquare gbar c'.g c.g g` and `OpenImmersionSquare g' c'.i c.i gbar`.
The completed coefficient category is rendered by `AdicCoefficientDatum A`, with
`cbcCompleteProperty d X r a ha` providing intrinsic derived completeness; the retained
witness family is `PbcHasCompatibleEtaleOrigins X d K.obj`.  The exact source map is
rendered by `completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha K`.
The naturality source composite is
```
(d.completedPull g).map
  ((d.push c.g).map ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).map k))
```
and the target composite is
```
(d.push c'.g).map
  ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).map
    ((d.completedPull g').map k))
```
which are exactly the two functorial actions in the node.

Statement dependencies used (all imported in the module) are:

* `Sheaf.Paper.AdicCoefficientDatum`, declarations `AdicCoefficientDatum`,
  `cbcCompleteProperty`, and `PbcHasCompatibleEtaleOrigins`;
* `WeilConjectures.Compactification.BaseChange`, `Compactification.baseChange`;
* `Sheaf.Paper.ProjectionCompactification`,
  `Scheme.proEtaleRingCompactSupportImage`;
* `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`,
  `SheafOfModules.localizedModuleExactIndependent`;
* `Sheaf.Paper.IntrinsicCompletionCompleted`,
  `Scheme.IsCompletedIntrinsicallyDerivedComplete`;
* `Sheaf.Paper.RingedEtaleOriginWitness`,
  `Scheme.EtaleOriginWitness` and `FiniteEtaleOriginWitness`;
* `Sheaf.Paper.CompletedCompactSupportExchange`,
  `Scheme.completedCompactSupportExchange`;
* `Sheaf.Paper.PbcActualStrictPullback`,
  `Scheme.pbcActualStrictCompletedPull`;
* `Sheaf.Paper.CompletedOpenExchangeTransport`,
  `Scheme.completedOpenExchangeComparison`;
* `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`,
  `Etale.compactSupportFiniteTorsion`;
* `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`,
  `ProEtale.StrictTower.normalizedProperOpenCalculus`;
* `Sheaf.Paper.ConstantCompletionEquivalence`,
  `ConstantCompletion.equivalence`;
* `Sheaf.Paper.CompleteProetale`, `Scheme.completeProetale_isIso`;
* `Sheaf.Paper.CompletedExchangeCoherence`, including
  `AdicCoefficientDatum.completedExchange_naturality` and the identity/pasting
  comparisons.

The edge cases checked are the empty generating tuple (`r = 0`, with `Fin 0`), the
identity base-change morphism (the completed identity comparisons in
`CompletedExchangeCoherence`), empty schemes (all predicates are object-property
predicates and do not assume a point), and arbitrary `g` (no flatness, properness or
finite-type hypothesis is added to `g`).  The origins predicate has one witness at every
positive reduction level and imposes no uniform lower bound.  No constructibility or
extra residue-characteristic condition was added.

Searches for an existing declaration were made with:

* `msearch.py ... leanfinder "completed compact support base change isomorphism for derived complete pro-etale complexes"`: eight hits, all ordinary etale/ring base-change or condensed solidification declarations; none states this theorem.
* `msearch.py ... loogle "completedCompactSupportExchange, IsIso, PbcHasCompatibleEtaleOrigins"`: no hits (`completedCompactSupportExchange` is not in the external Loogle environment).
* `msearch.py ... grep "completed.*compact.*support.*exchange" Mathlib`: no hits.
* `rg -n "completeProetale|completedCompactSupportExchange|compact-support base change" /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: only generic compact-support references; no matching declaration.
* `rg -n "completedCompactSupportExchange|completeCompactSupportProetale_isIso" lean/Sheaf`: found only the dependency definition `completedCompactSupportExchange`; no theorem with this statement before this module.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Earlier second reading (a previous round; superseded)

I reread the node and the module after compilation.  The same four schemes, four square
arrows, compactification data, coefficient datum, finite generating tuple, complete object,
and compatible origin hypothesis are all present.  The first conclusion is exactly the
specified ordered exchange map being an isomorphism.  The second conclusion matches each
source and target action in the naturality clause, with composition order checked in the
category.  The separated, locally-finite-type, and quasi-compact hypotheses on `f` are explicit; no
hypothesis on `g` or `g'` was added, and no source clause was changed.
The module compiled cleanly through `scompile.py` (including the expected postponed proof).

## Second reading by Q45

I independently read the node, its blueprint source, the cited Stacks source places,
and the dependency signatures against the Lean. The earlier second-reading paragraph
above is superseded: the original two-clause theorem did NOT state all of this node.
The mathematical node statement is correct and unchanged; no statement_change or unit
change is needed. The complete statement is now distributed among the recorded named
conclusions, rather than merely promised by prose in the primary theorem's docstring.

Object/hypothesis/conclusion checklist, in source order:

1. The coefficient ring is a commutative A and adic datum (A,I), with the recorded
   Noetherian, finitely generated ideal, torsion quotient and perfect positive quotient
   conditions. Lean: `{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`.
   I opened AdicCoefficientDatum and its CompleteCoefficientDatum parent: this is the
   node's datum, not a field, finite ring, constructible category or constant sheaf.
   The completedRing, derived, pull, push and completedPull fields refer to the actual
   inverse-limit coefficient sheaves. Verdict: exact.
2. Four schemes and a cartesian square, with f separated finite type and g arbitrary.
   Lean: the four Scheme.{t} binders and arrows, `[IsSeparated f]
   [LocallyOfFiniteType f] [QuasiCompact f]`, together with properSquare and openSquare.
   Locally finite type plus quasi-compact is finite type. The two stacked cartesian
   squares give the original cartesian square. No property of g or g' is assumed.
   Verdict: exact, with the Cartesian data retained explicitly rather than reconstructed.
3. A supplied compactification c and its base change c', including gbar, quasi-compact
   opens and proper factors. Lean: `Compactification f`, `Compactification f'`,
   `ChosenCartesianSquare gbar c'.g c.g g`, `OpenImmersionSquare g' c'.i c.i gbar`.
   I read Compactification, Refinement, open-square and chosen-square declarations.
   Properness/openness are fields; `c.quasiCompact_openImmersion` derives the needed
   quasi-compact open from QuasiCompact f. The basechanged quasi-compactness is derived
   by `cbcBaseChangeQuasiCompact`; none is an added target hypothesis. Verdict: exact.
4. Actual localized ringed-site extension by zero, and Rf_!^c = Rp_*j_!.
   Lean: the recorded `cbcDerivedOpenShriek d c.i c.isOpenImmersion`, abbreviated only
   as `cbcJ`; `cbcSupport d c` is literally that functor followed by `d.push c.g`.
   I read LocalizedModuleExactIndependent, ProjectionCompactification and the completed
   extension module: the finite constant-coefficient extension is not substituted for
   extension of completed sheaves. Verdict: exact.
5. Intrinsically derived I-complete K and compatible retained bounded-below etale
   origins at every positive reduction. Lean: `(r : ℕ) (a : Fin r → A) (ha : ...)
   (K : (cbcCompleteProperty d X r a ha).FullSubcategory)` and
   `PbcHasCompatibleEtaleOrigins X d K.obj`. The former is the intrinsic Koszul
   condition, through the recorded equivalence; the latter retains origins, their
   identifications, and transition compatibility, with a separate lower bound for
   each level. I opened IntrinsicCompletionCompleted, RingedEtaleOriginWitness and
   BoundedConstructibleComplete. There is no uniform bound or constructibility
   hypothesis. Verdict: exact.
6. The ordered completed exchange is an isomorphism, natural in K.
   Lean: the unchanged primary `completeCompactSupportProetale_isIso` signature:
   `IsIso (completedCompactSupportExchange ...)` and its explicit naturality equation.
   I opened that definition: it is the proper completed exchange followed by the push
   of the completed open comparison. `cbcExchange` is just an abbreviation of this
   declaration. Verdict: exact, and the primary lean.statement remains verbatim.
7. The open comparison is the finite-reduction comparison, Rlim(beta), then inverse
   extension/Rlim comparison, after constant-coefficient restriction. Lean: the imported
   `completedCompactSupportExchange`, `cbcDatumCompletedExchange`, and
   `completedOpenExchangeComparison` supply exactly these ordered maps. I read
   CompletedOpenExchangeTransport, PbcActualStrictPullback and
   ConstantCompletionEquivalence, rather than infer this from their names. The last
   comparison has the inverse direction specified by the node. Verdict: exact.
8. Agreement under canonical compactification comparisons and choice independence.
   Lean: `cbcRefinementMap`, `cbcRefinementMap_isIso`, and
   `cbcCompactificationComparison`; `completeCompactSupportProetale_compactifications`
   states naturality, identity, transitivity, independence of the common refinement
   and its arrows, and the cocycle. `_refinement` states the exchange/refinement
   commuting square. The common-refinement existence is the recorded geometric
   dependency. Verdict: this formerly missing clause is now explicit.
9. Identity and horizontal pasting, with canonical completed pullback identifications.
   Lean: `_identity` uses `d.completedPullId`, and `_horizontal` uses
   `d.completedPullComp` on both ends. Required complete-object witnesses are
   conclusions, not extra hypotheses. I read CompletedExchangeCoherence: it covers
   proper exchange, so importing it alone did not state compact-support coherence.
   Verdict: these formerly missing clauses are now explicit for arbitrary base changes.
10. Vertical pasting, with compactifications of both maps and their composite and
    canonical composition identifications independent of the compatible tower.
    Lean: `cbcTowerCompositionMap` is the specified proper/open mate followed by the
    open and proper compositors. `_vertical` states its source/target invertibility,
    completeness of Rf_!K, and the full pasting equation. `_composition_refinement`
    states invariance under compatible tower refinement; the existing compatible
    tower/cofilteredness dependency removes the choice. The intermediate open and
    quasi-compact instances are derived from the supplied pullback square, not assumed.
    Verdict: these formerly missing clauses are now explicit.

Canonical-helper audit (H4/H5, brief section 1): no independent notion or definition
node was introduced. All added helpers belong to this node's specified comparisons
and are listed in lean.declarations. `cbcRestrictionUnit_existsUnique` determines its
unit uniquely by restriction on every section. Its chosen data are therefore fixed,
not an arbitrary map selected from existence. The pull/restriction map is its adjoint
transpose. The open adjunction, beta, clopen projection and general proper/open gamma
are composed from these normalized units and the existing pull/push compositors.
Refinement and composition use precisely this gamma, including noncartesian refinement
squares. No downstream theorem is assumed in defining these arrows. Every postponed
helper theorem has a source, this blueprint ID, and a natural-language proof. All
new definitions contain real data; no definition body is sorry. No new fact is proved:
theorem proofs are sorry, while abbrevs reuse existing geometric facts and the one
identity-of-arrows transport definition uses equality elimination. No dependency node
needed a new module or lean-only repair, and no new-node/citer audit is applicable.

Sources and assumptions: read the blueprint statement and all eight proof steps,
Stacks proetale.tex Tags 09AE/09AF (localization and extension comparison), 09BP
(extension and limits), 099M/099N (completion and direct image) and 09C9 (proper base
change). The finite-coefficient hypothesis there is used at the positive reduction
levels through the retained origins. It is not imposed on the completed A itself.
The node explicitly supplies its adic hypotheses and drops neither bounded-below
origins nor the quasi-compact open needed for the localization argument. I also read
StrictTowerProperOpenCalculus and its full-square normalized gamma interface, and
coord/pefw-upstream-framework.md with the current 51-module framework. The older
slopmaster2 coefficient formalism alone is insufficient for this node.

Edge cases: Fin 0 is allowed when it generates I = 0. Zero rings/zero objects are not
excluded by Nontrivial or nonvanishing hypotheses. Empty schemes and identity arrows
are allowed. Reduction indices are ℕ internally with quotient I^(n+1); there is no
missing first positive quotient or unintended A/I^0 level. No positive characteristic,
fixed prime, uniform torsion exponent, nonempty indexing family, base field, affine,
Noetherian scheme or qcqs base hypothesis is added. The coefficient universe is t+1
and the pro-etale site retains object universe t+1 and morphism universe t, as in the
recorded datum; no universe equality is forced. Scheme/ring universes can be lifted
together under the project's recorded size convention. The identity and arbitrary
base-change cases are present explicitly in the new equations.

Independent searches used words different from the first reader's:

- LeanFinder: "Adic completion of the proper open shriek exchange coherent for
  compactification refinements and composition"; eight unrelated Tilde, condensed or
  affine-inverse-limit results, no match.
- Loogle: "IsIso, Compactification"; no result (external environment does not expose
  the relevant IsIso name).
- LeanSearch: "Natural compact support base change for adically complete pro etale
  sheaves, independent of compactification"; eight ring-completeness/base-change/
  condensed results, no matching declaration.
- Mathlib grep through msearch: "shriek.*baseChange|compactSupport.*baseChange";
  no result.
- rg on older WeilConjectures, Mathlib, shared lean/Sheaf and the current framework:
  "completed.*(shriek|compact)|complete.*compact.*support|compact.*support.*complet".
  Only the defining completed exchange and its immediate dependencies matched.
  CompactificationCoherence is for a different finite-field/l-adic bounded category;
  strict-tower gamma is on constant coefficients, not the actual completed ring category.
- Exact collision check for cbcRestrictionUnit, cbcCompactificationComparison,
  cbcTowerCompositionMap and completeCompactSupportProetale identity/horizontal/vertical
  in all four source trees: no existing declaration.

Repairs: (1) added explicit identity, horizontal, compactification/refinement, vertical,
and compatible-tower-refinement conclusions; (2) supplied their normalized canonical
maps, avoiding private replacement functors or arbitrary endpoint isomorphisms;
(3) expanded the main docstring to all eight node proof steps and supplied source/proof
docstrings for each new postponed assertion; (4) imported the recorded proof-dependency
modules that the original file omitted; (5) listed every declaration in lean.declarations
and explained the distributed full statement in lean.note. Original correct types,
ordered exchange, primary signature and all non-lean node fields were retained.

Validation: the complete module, including the final derived-instance wrapper, compiled
cleanly through the required scompile.py wrapper (sandbox 5.4s, library 6.6s), with no
errors or warnings beyond the permitted postponed-proof warnings. The final docstring
and metadata edits do not change declarations; they are checked again by delivery.
