## Worker report

The module `Sheaf.Paper.TraceCompactificationCohomology` states
`WeilConjectures.trace_compactification_cohomology`, with its sole theorem proof `sorry`.
The node's statement, dependency lists and proof are unchanged. All ten supporting
constructions have real data; they specialize/restrict the existing categories and
transport the existing canonical maps. No new independent mathematical notion is needed.

Source read: the entire statement and proof of
`literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-thm-trace-formula/lem-trf-compactification-cohomology`;
the current DAG's eight-step proof; the statements and full recorded declarations of
all nine statement dependencies, including the interfaces reexported by their current
recorded modules. The item's repair note concerns the already resolved stage-1 split;
it withdraws no stage-2 interface.

Hypotheses and clauses:

- The finite coefficient convention is the binder
  `T : TraceFormulaCoefficientConventions.{u}`. Its `datum` retains p,a,q,k₀,k;
  `coefficients` retains the prime different from p and its algebraic closure;
  `extension` is an actual finite subextension; `level_pos` is n≥1. The coefficient
  is exactly `T.coefficientRing = Padic.coefficientExtensionRing ... T.level`.
  `traceCompactificationCoefficientFinite` simply supplies its already proved finiteness.
- The separated finite-type geometric scheme and its map a_X are
  `T.geometricBaseChange` and `T.structureMap`, obtained from the specified X₀ by
  the recorded geometric base change. No extra geometric assumptions are added.
- A compactification j:X→Xbar with proper abar and abar∘j=a_X is exactly
  `c : Compactification T.structureMap`, with `c.i`, `c.Z`, `c.g`, and `c.comm`.
  It need not be a dense compactification, and extra proper components are permitted.
- The input category is `(traceCompactificationBounded T).FullSubcategory`.
  Its ambient category is the existing `RefinementFiniteLevelOrigin`, i.e. the recorded
  `EtaleOriginDerivedCategory` specialized to the positive finite coefficient level.
  Each object retains the pro-etale D+ object and the complete pair `(L,alpha)` of
  `EtaleOriginWitness`. The predicate imposes precisely `T.boundedConstructible` on
  the underlying complex in the canonical intrinsic coefficient presentation.
  Morphisms are every ambient morphism between the underlying complexes; no map of
  antecedents, chosen antecedent, or mere existence witness is substituted.
- `traceCompactificationUnderlying` forgets the retained witness through the recorded
  `etaleOriginForgetful`, applies `refinementCoefficientEquivalence.inverse`, and then
  the existing `sfIntrinsicDerivedEquivalence.functor`. This is coefficient realization
  of the same K, not a different sheaf/complex or a new definition of constructibility.
  `traceCompactificationForgetful` only restricts its target to the existing D^b_c.
- Both cohomologies use the fibre over s: `traceCompactificationSections T c` is the
  composite `traceCompactificationForgetful T ⋙ traceCompactificationImages T c ⋙
  T.pointFibre`. The middle functor lifts the existing `sfIntrinsicCompactSupport c`
  to the existing constructible full subcategory over s using the restriction clause
  of `finiteCompactSupportConstructibility`. Its map is the original candidate's map.
  The prime-unit hypothesis is supplied by the recorded `finiteFieldDatumPrimeUnit`.
  The final
  functor is exactly the recorded `pointFiniteFibre` into the existing
  `DerivedCategory.pointFiniteCohomology` full subcategory. Thus its value is also
  the already recorded `T.compactSupportComplex c` on the forgotten object.
  Thus its object is exactly the existing compact-support complex for c, including
  the coefficient module universe and the existing constant-section scalar action.
- The target really is ordinary cohomology of extension by zero: unfolding the recorded
  `sfIntrinsicCompactSupport c A` gives
  `(sfIntrinsicExtensionByZero c.i A).mapDerivedCategory ⋙
  proEtaleConstantDerivedDirectImage c.g A`. Consequently the underlying value of
  `traceCompactificationSections T c` is precisely
  `Fib_s(R(c.g)_* (c.i)_! K) = RΓ(c.Z,(c.i)_!K)`, the formula of the recorded
  `finiteOrdinarySections`, evaluated at the extension by zero and the structure map c.g.
  There is no replacement of ordinary cohomology by a stalk, an arbitrary evaluation,
  or the direct image itself. For the compactification c₀ used to define Ra_X!,
  `traceCompactificationSections T c₀` is RΓ_c(X,-).
- The existential family `C : ∀ c d, traceCompactificationSections T c ≅
  traceCompactificationSections T d` gives in particular the required `C c₀ c`.
  Its type is a natural isomorphism of functors, with actual inverse components;
  naturality holds for every ambient morphism in the witnessed constructible domain.
- The theorem requires `traceCompactificationComparisonLaws T C`, the fully defined
  conjunction of the two following equations. Naming the predicate keeps exported
  theorem type checking small; it introduces no hypothesis or unspecified property.
- Canonicity and change of compactification are its first conjunct: for EVERY common
  refinement e→c and e→d, `(C c d).hom.app O` is the inverse of the prescribed
  refinement isomorphism to c followed by that to d. `traceCompactificationRefinement` is obtained
  from the existing `refinementComparisonAtWitness`, conjugated by the existing
  `sfIntrinsicCompactSupportComparison` and passed through the actual point fibre.
  The outer comparisons are the published constant-section/K-injective-normalized
  coefficient transports. No arbitrary isomorphism is postulated or chosen.
- The second conjunct `(C c d).hom ≫ (C d e).hom = (C c e).hom` is composition compatibility
  under changes of compactification. The common-refinement normalization also covers
  identity refinements and independence of the chosen arrows/common refinement.
  The simultaneous pairwise formulation is the source's final cocycle paragraph.

Dependency declarations used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, its `coefficientRing`,
  `geometricBaseChange`, `structureMap`, `boundedConstructible`, and `compactSupportComplex`.
- `WeilConjectures.Compactification.Refinement`:
  `AlgebraicGeometry.Compactification`, `.Refinement`, and `.category`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`; its exactness instances
  come from `ProEtaleIntrinsicExtensionByZeroExact`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`, via T's predicate.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness` reexports the full original
  witness interface. The existing ringed `AlgebraicGeometry.ProEtale.EtaleOriginWitness`
  is the one already retained by the recorded `EtaleOriginDerivedCategory`; its fixed
  presentation is obtained by the recorded refinement realization. The unrelated
  consumer-specific `FixedEtaleOriginWitness` is not redefined.
- `Sheaf.Paper.EtaleOriginDerivedCategory`:
  `AlgebraicGeometry.ProEtale.EtaleOriginDerivedCategory` and `etaleOriginForgetful`.
- The compact-support dependency's recorded finite-coefficient derived LowerShriek module
  provides `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`.
  The identical intrinsic presentation used by the recorded cohomology is
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`, in
  `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `WeilConjectures.pointFiniteFibre`;
  `Sheaf.Paper.PointSectionsFiniteness`: `pointFiniteSections`.
- `Sheaf.Paper.OrdinaryCompactWeilCohomology` reexports all original finite interfaces
  in `Sheaf.Paper.OrdinaryCompactCohomology`, notably `finiteOrdinarySections`,
  `finiteCompactSections`, `finiteConstructibleImages`, and `finiteConstructibleSections`.
  The final Weil-specialized declaration of the current record does not replace them.
- `Sheaf.Paper.RefinementComparisonIsomorphism`:
  `RefinementFiniteLevelOrigin`, `refinementCoefficientEquivalence`,
  `refinementFiniteLevelFixedObject`, and `refinementComparisonAtWitness`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence`;
  `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange`:
  `AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison`.
- Mathlib `ObjectProperty.lift` and `ObjectProperty.isoMk` supply full-subcategory
  functors/isomorphisms without extra postponed structural lemmas.

Proof imports: the recorded finite constructibility, triangulated closure, derived image,
properness, quasi-separatedness and finite-type modules are imported. The old
`WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek` proof-dependency import is
replaced by the reorganized finite-coefficient module that defines the same declarations.
`Sheaf.Paper.CompactificationCoherence` cannot currently be imported together with the
finite-coefficient dependencies: its proof-only import `ComparisonGlobalCohomology` loads
that retired old module and the compiler reports that the environment already contains
`rightDerivedLowerShriekOfCompactification`. Following the launcher's duplicate-import
repair instruction, this delivery imports the smaller owning
`RefinementComparisonIsomorphism` module needed for its canonical maps. The coherence
proposition remains the cited proof route and is not restated or assumed as a hypothesis.

Edge cases checked before writing and on second reading: K=0; empty X; n=1 (no exponent
reindexing and n=0 is excluded by the SOURCE); proper X with the identity compactification;
non-dense compactifications and extra proper components; repeated compactifications;
identity refinements; composition of refinements; different common refinements and their
arrows; different retained etale witnesses for the same K with every ambient map between
them. No finite-Tor, perfectness, density, Cartesian-refinement, chosen antecedent, or
termwise boundedness hypothesis is present. The sole universe u is the conventions'
original common universe; coefficient ULift is exactly the existing u+1 lift. The
existing T.pointFibre retains its original u+2/u+1 hom universes for the intrinsic
standard localization and the small coefficient-module localization. No new
derived-category instance or equality of site universes is imposed.

Searches made (2026-10-18):

- `msearch.py ... leanfinder "compactly supported etale cohomology is cohomology of
  extension by zero on a proper compactification"`: eight results about scheme limits,
  sections, and condensed sheaves; no derived compactification comparison.
- `msearch.py ... loogle '"lowerShriek"'`: zero hits.
- `msearch.py ... grep 'compactification|compactlySupportedCohomology' AlgebraicGeometry`:
  zero hits.
- `msearch.py ... leansearch "compactly supported etale cohomology on a proper
  compactification is ordinary cohomology of extension by zero"`: eight hits, mostly
  topological/function support; none is this theorem.
- `rg` of the item id and compactificationCohomology/compactification_cohomology in
  the upstream source and `lean/Sheaf`, and of the proposed declaration names in Mathlib,
  upstream, project and `dag/lean_names_upstream.json`: no existing exact statement or
  name collision. Broader rg of compactification/cohomology in the shared pro-etale
  framework found `LowerShriekIndependence.lean`; its complete declarations were read.
  `rightDerivedLowerShriekCompactificationIso` compares direct images precomposed with
  etale pullback on D+, not coefficient cohomology functors on the full category of
  witnessed bounded constructible pro-etale inputs. It neither applies the geometric
  fibre nor states the common-refinement normalization on this domain. It is useful
  proof infrastructure, not an exact existing binding for this node. Existing
  `CompactificationCoherence` and intrinsic realization transports are reused.

No statement dispute or source correction was found.

## Second reading by Q15

Author's second reading, not an independent review (the dispatcher explicitly prohibits
subagents; the maintainer independently reviews the delivery). I reopened the node,
the main-20261015 statement/proof, and the complete generated module. The hypothesis and
clause correspondence is the list above. In particular I checked that bounded
constructibility is on the same realized K, the origin pair is retained, and the full
subcategory imposes no map of origins. The target was unfolded through the ORIGINAL
sfIntrinsicCompactSupport formula: it is the fibre of R(c.g)_* after the recorded exact
(c.i)_!, hence precisely the stated ordinary cohomology on the compactification. The
iso family is normalized at every common refinement and its final equation is the
source's cocycle, so it cannot mean merely existence of unrelated isomorphic objects.
The smaller refinement-construction import avoids the documented old/new LowerShriek
conflict. The final helpers retain the ambient transport, its full-subcategory lift, and
application of T.pointFibre as separate named constructions. The normalization and
cocycle are equations of the forward natural transformations; these determine exactly
the same isomorphism equations because isomorphisms are determined by their forward
maps. No diagnostic commands or tracing options remain. No mathematical hypothesis,
conclusion, coefficient category, or node field other than lean was changed.

Validation: the final complete module passed both scratch and named-module compilation
through scompile.py with no errors or warnings (6.5 s and 11.9 s). The exact comparison-law
predicate is named to avoid expensive export of its fully expanded existential theorem.
The geometric candidates, fibre, canonical refinement maps, and equations are unchanged.
