## Worker report

The module `Sheaf.Paper.EtaleWitnessTransportData` states
`AlgebraicGeometry.ProEtale.etaleWitnessTransportData`, with its only proof `sorry`.
Its five helpers have real data: two transparent abbreviations for the existing ordinary
D+ categories, the composite H, the natural comparison built from the specified unit,
and the identification for a retained witness built from that comparison and H(alpha).
Every declaration is listed in the item's `lean.declarations`. The theorem docstring
carries all six proof steps of the DAG node. No statement correction or new node is made.
There is no STATEMENT-DISPUTED finding.

### Hypotheses and every conclusion clause

| Node text | Lean rendering |
| --- | --- |
| Fixed finite purity datum, k, ell distinct from p, E, uniformizer and positive n | `P : WeilConjectures.PurityFiniteSetting.{u}` contains the recorded finite-field datum, coefficient datum and its different-characteristic proof, literal finite subextension and positive level. `P.Ring` is the existing quotient by the chosen uniformizer power; `P.Coefficient` is its canonical ULift to u+1. `P.level_pos` is passed to every intrinsic predicate. |
| T and Z finite-type k-schemes | Both `Scheme.{u}`, both `.Over (Spec (.of P.field.k))`, and both `LocallyOfFiniteType` and `QuasiCompact` structure-map instances. No separatedness or nonemptiness is imposed. |
| Ordinary constant-A etale and pro-etale module categories | `witnessEtalePlus` and `witnessProEtalePlus` are exactly `DerivedCategory.Plus (Sheaf ... (ModuleCat.{u+1} A))` on the recorded original small topologies. They merely abbreviate existing categories. The site retains object universe u+1 and arrow universe u. |
| Arbitrary G on D+ | `G : witnessEtalePlus P.Coefficient T ⥤ witnessEtalePlus P.Coefficient Z`. There is no additivity, exactness, triangulatedness or constructible-preservation assumption. |
| H = nu_Z^* G Rnu_T,* | `witnessTransportFunctor` is precisely `comparisonLowerStar.rightDerivedFunctorPlus ⋙ G ⋙ comparisonUpperStar.mapDerivedCategoryPlus`. |
| Integers r <= s | `r s : ℤ`, `_hrs : r ≤ s`, without sign restriction. |
| Arbitrary intrinsically bounded constructible B | First universal quantifier is over every B in ordinary pro-etale D+. The hypothesis is the recorded `Scheme.intrinsicFiniteTorsionConstructible ...` of `(finiteCoefficientIntrinsicRealization T P.Ring).mapDerivedCategory.obj B.obj`. This realization is the existing exact equivalence from ordinary constant-A modules to modules over the constant ring sheaf; thus the hypothesis is precisely intrinsic constructibility, not an etale-origin hypothesis. Every intrinsically bounded constructible ringed-module object is covered by this equivalence and lies in D+. |
| Existence of B_e in Db_c and alpha | First conjunct under that hypothesis is `∃ B_e : witnessEtalePlus ..., Etale.DerivedCategory.isBoundedConstructible ... B_e.obj ∧ Nonempty (nu_T^*.obj B_e ≅ B)`. No interval or Tor assumption appears before the existence. |
| Reflection for every such witness | The next conjunct quantifies every B_e with that exact constructibility predicate and every alpha with that source and target. It asserts `DerivedCategory.homologyConcentratedIn r s B_e.obj ↔ WeilConjectures.constructibleInterval ... r s (realization B.obj)`. Since intrinsic constructibility of B is already assumed, the second side is exactly B's cohomological support in [r,s]. |
| Tor reflection for every witness | Under the same universal witness quantifier, a separate implication has premise `Scheme.HasProEtaleTorAmplitude T P.Ring (realization B.obj) r s` and conclusion `Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T r s B_e.obj`. The latter recorded predicate explicitly tests every degree-zero etale module sheaf. No constructibility restriction is placed on test sheaves. |
| Natural isomorphism H nu_T^* ≅ nu_Z^* G on all D+ | `witnessTransportComparison` has exactly this natural-isomorphism type, without constructibility restrictions. It is the inverse of `compactSupportComparisonUnit T A`, whiskered by F and composed with the associator and unitor. This is an actual construction, not a Nonempty or arbitrary choice. |
| Specified comparison unit eta | The theorem's next conjunct says that each inverse component of the comparison is `F.map ((derivedComparisonAdjunctionPlus ... T).unit.app C)` for every C in etale D+. Thus the precise adjunction unit, not a freely specified natural isomorphism, is fixed. |
| Identification delta for each bounded constructible witness | `witnessTransportIdentification` is `H.mapIso alpha` inverse, followed by the natural comparison component at B_e. Its type is `H.obj B ≅ F.obj B_e`. The theorem's third conjunct quantifies every intrinsically bounded constructible B and every bounded constructible B_e with such alpha. |
| Delta inverse formula and characterization | This conjunct says `delta.inv = F.map eta ≫ F.map (Rnu_*.map alpha.hom)`. Lean composition is left to right, so this is exactly the displayed formula in the node. An isomorphism is determined by its inverse; the formula therefore characterizes delta without a separate uniqueness axiom. |
| Naturality for beta and h | Last conjunct quantifies both bounded constructible witnesses, arbitrary `beta : B_e ⟶ B'_e` and `h : B ⟶ B'`. Its hypothesis `alpha.hom ≫ h = nu_T^*.map beta ≫ alpha'.hom` is exactly h alpha = alpha' nu_T^* beta. Its conclusion `H.map h ≫ delta'.hom = delta.hom ≫ F.map beta` is exactly delta' H(h) = F(beta) delta. No map is assumed invertible besides the two alpha witnesses. |

### Dependency declarations read and used

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting`, `.Ring`, `.Coefficient`, `.level_pos` and the
  stated coefficient-prime invertibility consequence. The already published
  `Sheaf.Paper.ConstructibleExceptionalInverseImage` supplies `.ringFinite` and
  `.coefficientFinite`, derived from the existing positive-level finiteness theorem.
- `def-sf-categories`: repaired `Sheaf.SixFunctors.SfCategories`, all ambient and
  coefficient-stage aliases described below. Their component ordinary D+ categories
  are Mathlib's `DerivedCategory.Plus`, used transparently in the item helpers.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparison`, `.proEtaleSiteComparisonModules`; the same functors
  are `ProEtale.comparisonUpperStar`, `.comparisonLowerStar` in their source definitions.
- `def-weil-finite-torsion-constructibility`:
  `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
  `Scheme.intrinsicFiniteTorsionConstructible`; no replacement predicate is defined.
- `def-weil-scheme-morphism-properties` is a convention record, not a declaration.
  Its finite-type convention is the existing `LocallyOfFiniteType` plus `QuasiCompact`.
- `def-weil-constructible-intervals`:
  `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`,
  `WeilConjectures.intrinsicConstructibleIntervalCategory`, a transparent alias of the
  full subcategory of `constructibleInterval`, which the item uses for membership.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites` reexports
  `finiteTorConstructible` and the underlying `Scheme.HasProEtaleTorAmplitude` in
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`. The latter specifies the interval.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` reexports
  `Etale.DerivedCategory.hasTorAmplitudeIn` from the upstream etale coefficients module.
- Proof imports: `Sheaf.Paper.ProEtaleConstructibleOrigin`,
  `ProEtale.constructible_proEtale_origin`; `Sheaf.Paper.ComparisonPullbackExact`,
  `AlgebraicGeometry.comparisonPullbackExact`; `Sheaf.Paper.ComparisonTorAmplitude`,
  `AlgebraicGeometry.finiteCoefficient_comparison_reflects_torAmplitude`.
  `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit` supplies
  `isIso_compactSupportComparisonUnit` and the actual `compactSupportComparisonUnit`.
- The canonical coefficient realization is
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`,
  `finiteCoefficientIntrinsicRealization`, with its existing exact-equivalence theorem
  `finiteCoefficientIntrinsicRealization_exact`. Its scalar map and sheafification
  construction, and `finiteCoefficientIntrinsicDerivedComparison`, were read in full.

### Edge cases

Empty T and Z and the zero object are allowed. Positive level n=1 and the single-degree
interval r=s are included. The interval is inclusive and both bounds can be negative.
Identity witnesses give precisely the component of the natural comparison. For a constant
functor G, the construction still works; no zero-preservation of G is assumed. The beta and
h in the naturality equation can be zero or otherwise noninvertible. Over Z/ell^2 the
residue field in degree zero has a bounded constructible origin but infinite Tor amplitude;
the existence and interval conjuncts do not assert finite Tor in that case. All geometric
and coefficient universes are explicit, with `autoImplicit false`.

### Searches and verification

The required `msearch.py Q75 lem-pur-etale-witness-transport-data` searches were:

- LeanFinder, `Etale proetale bounded constructible origin witnesses interval reflection transported functor unit natural isomorphism`: 8 hits, including `unitCompPartialBijective_natural`, Dold-Kan compatibility and condensed comparisons; none is this statement.
- Loogle, `CategoryTheory.Adjunction.unit, CategoryTheory.Functor.mapIso`: 0 hits.
- Mathlib grep, `comparison.*[Uu]nit|[Ww]itness.*[Tt]ransport`, CategoryTheory: 17 hits concerning monadic comparison and cartesian unit comparisons, not this statement.
- LeanSearch, `Etale proetale constructible derived origins preserve cohomological intervals reflect Tor amplitude`: 8 hits concerning formally etale algebras and the etale site, not this statement.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for witness transport, intrinsic-plus comparisons and the node id found no exact declaration. Nearby `ClosedEtaleTransportBounds` is closed-immersion-specific and only states the final bounds; `TrfWitnessedOpenPullback` concerns pullbacks and open extension, not arbitrary G. The required direct node-id search in upstream returned no match.
- For the dependency repair, searched for every recorded sf-category alias in both Lean roots and read the previous worker report and component definitions. No remaining declaration defines the deleted alias family. `scompile.py --source Sheaf.SixFunctors.SfCategories` returned `Module source unavailable`.

Both final modules were compiled separately in dependency order by the prescribed scompile.py.
The final run was clean, including the private overlay and actual module-name compiles:
SfCategories 5.5 seconds and EtaleWitnessTransportData 8.9 seconds in the library-name pass.
No global build, direct git command, live-source edit or launcher-script change was made.

## Dependency modules

`def-sf-categories`: its recorded module was deleted as unreachable on 2026-10-20,
and the source reader confirms it is unavailable. The dependency module restores the
complete interface as transparent aliases/full subcategories, using every existing component
notion. Only its `lean` field changes; its mathematical statement and dependencies are intact.

The generic ambient categories are `sfAmbientDerivedCategory`, `...Plus`, `...Minus` and
`...Bounded`, on `ringedSiteModules R`; `sfConstantDerivedCategory` uses `constantSheaf`.
Independent site-object, arrow, coefficient, module and localization universes are retained.
Etale allowable torsion uses the recorded `Etale.allowableTorsionSheafProperty` after
`SheafOfModules.toSheaf`. Pro-etale allowable torsion uses the recorded
`Scheme.geometricRingModuleStalkFunctor`, with the quantifier order degree, geometric point,
element, positive annihilator and allowable prime divisors. Both are full subcategories of
D+. For empty P only zero stalk groups qualify (annihilator 1); zero qualifies for any P.

Finite etale constructibility uses `Etale.DerivedCategory.isBoundedConstructible`.
Its Tor and interval subcategories impose exactly the existing Tor predicate and cohomology
vanishing. Finite pro-etale constructibility, finite Tor and intervals alias the recorded
`intrinsicFiniteTorsionConstructible`, `finiteTorConstructibleCategory` and
`intrinsicConstructibleIntervalCategory`. Neither notion is copied or weakened.

Integral Db_c and Db_ctf are reexported `sfIntegralConstructibleCategory` and
`finiteTorConstructibleIntegralCategory`; their definitions retain derived completeness and
one common interval for all finite reductions. `sfIntegralAmbientDerivedCategory` uses
`scalarReductionSource` over the completed sheaf. Rational Db_c is the recorded scalar
localization `sfRationalConstructibleCategory`; algebraic-closure Db_c is
`generalAlgebraicallyClosedConstructibleCategory`. The field finite-Tor aliases are exactly
these categories. Higher intervals intersect the recorded lower and upper standard classes
`sfIntegralStandardClass`, `sfRationalStandardClass`, `sfCommonStageStandardClass`. All Hom
sets, identities and compositions are inherited. The global coefficient conventions,
invertibility convention, n>=1 and ordered-interval usage remain those of the dependency
node. No ordinary constant-ring interpretation is imposed at higher coefficient stages.

## Second reading by Q75

The dispatched-worker instruction forbids starting another agent. This is an explicit author
rereading; I do not claim it is an independent review. The maintainer's independent review
is still required. I reopened both node statements and both final modules and checked the
hypotheses and clauses against the table above. I corrected dot-notation line breaks and
reflowed docstrings after compiler feedback, restricted the witness-normalization and
naturality conjuncts to the bounded constructible witnesses in the node, and restored the
entire deleted category-alias dependency rather than omitting it. I checked the order of
composition: alpha.hom then h in the premise, H(h) then delta' in the conclusion, and
F(eta) then F(Ralpha) for delta inverse. No node-statement mismatch remains. The dependency
rereading checked the allowable-torsion quantifiers, finite test sheaves, completed integral
ambient, uniform reduction intervals and field-stage identity aliases clause by clause.
