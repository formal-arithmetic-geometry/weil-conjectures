## Worker report

The module `Sheaf.Paper.ClosedSectionCompactOrigin` states
`AlgebraicGeometry.ClosedSectionCompactOrigin.closed_section_compact_origin`.
The theorem has proof `by sorry`; there are no other postponed theorems.
Every helper definition has real data assembled from the existing functors,
adjunction-normalized comparisons, full-subcategory inclusions and isomorphism composition.
The mathematical statement and proof of the DAG node are unchanged.

The finite datum is the explicit section variable
`P : WeilConjectures.PurityFiniteSetting.{u}`. Its fields retain the finite field,
algebraic closure, coefficient prime distinct from the characteristic, finite coefficient
extension, uniformizer quotient and positive level. The coefficient object throughout is
the existing `P.Coefficient`, the standard `ULift` of that quotient. There is no arbitrary
coefficient-ring parameter and no extra coefficient hypothesis.

Hypothesis-by-hypothesis rendering:

- `B X : Scheme.{u}` and `b : B ⟶ Spec (.of P.field.k)` introduce the two schemes over k;
  X has structure map `f ≫ b`. `IsSeparated b`, `LocallyOfFiniteType b`, `QuasiCompact b`
  state that B is separated and finite type over k. The same three classes on `f`
  state the corresponding hypotheses on the morphism. Their composition gives the
  required separated finite-type k-structure on X. This parameterization covers any
  given k-morphism by replacing its X-structure map with the equal composite.
- `c : Compactification f` is the given compactification, not an existence predicate.
  It is retained in every compact-support functor, beta, sigma, tau and witness.
- `s : B ⟶ X`, `[IsClosedImmersion s]`, `hs : s ≫ f = 𝟙 B` are the closed section.
  `[QuasiCompact s.openComplement.ι]` is precisely its quasi-compact complementary open.
- `M` and `K` are arbitrary `DerivedCategory.Plus` objects of ordinary module-valued
  sheaves on the respective small etale/pro-etale sites, with coefficients in
  `ModuleCat.{u+1} P.Coefficient`. No constructibility, finite Tor amplitude or
  invertibility of a class map is required.
- `theta : C_X.obj M.obj ≅ K.obj` retains the specified comparison isomorphism.
  `ce : etaleSource P s ⟶ M` and `cp : (proSource P s).obj ⟶ K.obj` are the actual
  maps. The Plus inclusion is full, so the former permits every ambient derived map.
  The arrow hypothesis is literally `C_X.map ce ≫ theta.hom = epsilon.hom ≫ cp`.

Clause-by-clause rendering:

- `etaleUnit`, `proUnit`, `etaleSource` and `proSource` are degree-zero objects built
  from `SupportedConstantNormalization.constant` and `.supported` on the two sites.
  They introduce no replacement sheaf, site or ring construction.
- `constantComparison` is chi: the existing exact-derived single-complex comparison
  followed by the single-complex image of the existing scalar-preserving `compareUnit`.
- `supportedComparison` is epsilon: exact-derived single-complex comparison followed
  by the single-complex image of the actual `gamma` counit mate. Its inverse uses
  the existing `site_normalization` invertibility theorem, never a choice of an iso.
- `etaleClosedIso` and `proClosedIso` identify the proper compact-support functors
  with closed direct image, via the existing proper identifications, exact-derived
  comparison and degree-zero comparison. `closedPushExact` is a term-valued instance
  applying the recorded complement theorem to `s.openComplement.ι`; it proves no
  new theorem and introduces no exactness assumption. `proClosedIso` includes chi
  at its input, as required when evaluating the origin compositor at `originUnit`.
- `etaleSigma` first compares c with the standing compactification, then applies
  F^e to the inverse closed identification, the recorded etale compositor,
  `rightDerivedLowerShriekPlusCongr hs`, and the recorded identity comparison.
- `proSigma` applies F^p for exactly c to the inverse proper/exact closed
  identification, compares the outer candidate canonically on the retained origin
  object, then applies `originCompositionAmbient`, equality transport for hs,
  `originCompactSupportId` and chi. Thus sigma is independently assembled from
  composition and identity normalization on each site; it is not defined by the
  square whose equality the theorem asserts.
- `compactComparison` is the specified inverse-direction beta of
  `compactSupportSiteComparison`, with the canonical Plus/unbounded compatibility
  before it. It uses no new choice of an isomorphism.
- The first conjunct of the theorem is exactly the source-normalization equation:
  `beta_source ≫ F^p.map epsilon.hom ≫ sigma_p.hom = C_B.map sigma_e.hom ≫ chi.hom`.
  The full inclusion of D+ into D accounts for `DerivedCategory.Plus.ι.map`.
- `etaleTau` is `sigma_e.inv ≫ F^e.map ce`. `proTau` is
  `sigma_p.inv ≫ F^p.map cp`. Neither is declared an isomorphism.
- `targetComparison` is psi, literally `compactComparison ≪≫ F^p.mapIso theta`.
  Its return type is an actual isomorphism with target the unbounded candidate
  applied to K, so invertibility is retained by construction, not separately
  asserted as a tautological conjunct.
- The conclusion `DerivedCategory.TStructure.t.plus (F^e.obj M.obj)` states the
  required boundedness of the unbounded etale compact-support output. It is not
  an extra input assumption. The final equality is exactly
  `C_B.map tau_e ≫ psi.hom = chi.hom ≫ tau_p`.
- `sourceWitness` is the actual `Scheme.FixedEtaleOriginWitness` with complex
  `etaleUnit` and isomorphism chi. `targetWitness` has complex the bounded-below
  etale compact-support image of the same M, and isomorphism psi followed by the
  canonical compatibility with the pro-etale D+ output. Thus the two witnesses and
  the actual `etaleTau` are available as data; no existential antecedent replaces
  any of them. The final equality identifies that actual representative with tau_p.

The theorem docstring records all ten proof steps of the node, including the compatible
tower t=js, the actual open-adjoint normalization, direct-image composite and identity
compatibility, and cancellation only of sigma, never of the class maps.

Dependencies read and used (module, declarations):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, `.coefficientCommRing`, `.constantEtale`.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `AlgebraicGeometry.ProEtale.siteComparisonDerivedPullbackPlus`; the same
  `comparisonUpperStar.mapDerivedCategory` gives its unbounded ambient version.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, `.category`; the underlying
  `Compactification`, `.hasCompactification` and `HasCompactification.of_eq` are reused.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `AlgebraicGeometry.ProEtale.compactSupportSiteComparison` and its Plus version.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness` (complex plus specified iso).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: ordinary module-valued
  `DerivedCategory`, `DerivedCategory.Plus` and the standard t-structure predicate.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the recorded intrinsic
  module-coefficient realization. The statement explicitly calls for the ordinary
  fixed-scalar presentation, so it uses `Sheaf (ProEt.topology T) (ModuleCat A)`
  just as the recorded compact-support comparison and fixed witness do.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, its Plus
  restriction and `rightDerivedLowerShriekOfCompactificationPlusCompatibility`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: the recorded intrinsic
  `sfIntrinsicCompactSupport`. The ordinary fixed-scalar realization retained in
  its note and in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`
  is the candidate used here, as required by this node's explicit ordinary-category clause.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons` and the public upstream
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  `rightDerivedLowerShriekOfCompactificationPlusIso`,
  `rightDerivedLowerShriekPlusCompIso`, `rightDerivedLowerShriekPlusCongr`,
  `rightDerivedLowerShriekPlusId`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `originCompositionAmbient`, `originCompactSupport`, `originCompactSupportId`;
  `comparisonUpperStarPlusEtaleOrigin` retains the constant origin object.
- `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization`:
  `constant`, `supported`, `compareUnit`, `gamma`, `site_normalization`.
- `Sheaf.Paper.ComparisonPullbackExact`: exact ordinary inverse image, used through
  the derived functors already supplied by the dependency interface.
- `def-sf-origin-candidate-comparison` owns the existing plain definition
  `AlgebraicGeometry.ProEtale.towerCandidateComparison` in
  `Sheaf.Paper.ProEtaleCompositionTowerNormalization`. The normalization theorem
  remains a proof dependency only; its statement is not needed for this construction.
- `def-sf-compact-support-site-comparison-construction` owns the existing plain
  `compactSupportSiteComparison` and its Plus version in
  `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`.
- `def-pur-supported-constant-exchange-maps` owns the existing plain constant,
  supported, compareUnit and gamma constructions in
  `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`. The requested local instance
  `coefficientFinite` combines this positive-level finiteness theorem with
  `Finite.of_equiv P.Ring Equiv.ulift.symm`. It adds no coefficient hypothesis
  and imports no compact-support site-coherence module or theorem.
- Proper/exact identifications are the existing
  `Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`,
  `ProEtale.rightDerivedLowerShriekIsoOfIsProper`,
  `ProEtale.preservesFiniteColimits_lowerStar_of_isCompl`,
  `Functor.rightDerivedFunctorIsoMapDerivedCategory`, and
  `Functor.mapDerivedCategorySingleFunctor`.

Every recorded, stated proof dependency is imported. The old pro-etale closed-exact
module attachment is the forwarding module for its FiniteCoefficient counterpart;
the latter is imported directly for the actual constant-module declaration, and the
recorded forwarding module is also imported as a proof dependency.

Sources opened: current `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-rank-one-thom.proof.md`, Step 1; local Stacks `more-etale.tex`,
`lemma-shriek-proper-and-open` (0F7B) and `lemma-shriek-composition` (0F7J).
The archived path in the node's source field was left unchanged; the current blueprint
was used to check the intended global morphism.

Edge cases checked by reading the formulae:

- ce and cp can both be zero; neither sigma nor beta requires their invertibility.
  No `IsIso` instance for ce, cp or tau is introduced.
- M=K=0 is permitted, with any specified theta and compatible class maps.
- Empty B is permitted (a morphism X to empty B forces X empty); all sites,
  degree-zero objects, compactification maps and zero arrows still have their types.
- s=id and f=id are allowed, and the published composition and identity comparisons
  determine both sigmas. The complementary open may be empty.
- No nonempty or connected base, dimension, constructibility, finite-Tor or
  cohomological-dimension hypothesis is present.
- The coefficient level is any positive level and may be ramified; no divisibility
  restriction on the level or field characteristic has been added.
- Scheme/site object universe u+1 and morphism universe u remain distinct.

Searches actually run:

- `msearch.py ... leanfinder "identity normalized compact support image of a closed
  section with etale origin"`: eight unrelated Mathlib hits (standard etale
  presentations, normalization maps and bump functions); no theorem matching this node.
- `msearch.py ... leansearch "compact support closed section identity comparison"`:
  eight topology/function compact-support hits; no match for derived compact support.
- `msearch.py ... loogle "Compactification, rightDerivedLowerShriekPlusCompIso"`:
  zero hits with diagnostic `unknown identifier 'Compactification'`; this is not
  evidence of absence of project declarations. They were found by source inspection.
- `msearch.py ... grep "closedSection|closed_section|compact.*[Oo]rigin"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg -n` of `closedSection|closed_section|lem-pur-closed-section-compact-origin|
  compact.*[Oo]rigin` in both `lean/WeilConjectures` and `lean/Sheaf` found related
  affine/support helpers, compact-support coherence and the line-zero-class
  specialization; none states the arbitrary closed-section result. The literal
  item-id hits are references in downstream docstrings, not declarations of this node.
- Read `LineZeroClassEtaleRealization` to check the existing specialized normalizations;
  it requires a rank-one vector bundle and the Cartier class, and cannot supply
  the arbitrary section and arbitrary ce/cp of this item. The new helpers use its
  underlying dependency constructions, not its specialized statement.
- Current server source of `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
  was read with `scompile.py --source` and agrees with the interface used here.

No statement dispute, mathematical correction, new node or dependency-interface repair.
Only lean and the three explicitly described additions of already-landed definition
owners differ in the node copy. No theorem was added to stmt_deps. No upstream file
was edited.

Validation: the module compiled with the prescribed `scompile.py` both as its sandbox
module and under its delivered library module path, with no errors or warnings.

## Repair of returned delivery 1d27ba1b1136

The saved packet passed the initial required deliver2.py --no-push check, but its
JSON still added the two theorem statement dependencies flagged by the independent
review. The repair therefore addresses that review rather than treating a mechanical
pass as sufficient.

1. H2, tower candidate comparison: removed the added statement citation of
   lem-trf-proetale-composition-tower-normalization and cited its existing definition
   owner def-sf-origin-candidate-comparison instead. The module import remains because
   it supplies towerCandidateComparison and the theorem is already a proof dependency.
2. H2, coefficient finiteness: removed the added statement citation of
   lem-pur-compact-support-site-coherence and its module import. Inlined the exact
   positive-level quotient finiteness plus Equiv.ulift construction as the requested
   local instance coefficientFinite. No new postponed theorem or assumption is added.
3. Advisory: cited the existing definition owners
   def-sf-compact-support-site-comparison-construction and
   def-pur-supported-constant-exchange-maps. Their recorded signatures and concrete
   constructions were read and agree with the existing calls.

The theorem signature, all source and target maps, both independently constructed
sigmas, the ten proof steps, the mathematical node statement and all base proof
dependencies are unchanged. The new definition citations follow brief-stage2.md §5's
permission to cite an already landed definition owner requested by a return.

Repair validation: prescribed scompile.py compiled both Sheaf.Stage2.Sandbox0
(21.4 s) and Sheaf.Paper.ClosedSectionCompactOrigin (18.9 s) cleanly. The local
coefficient instance is a direct term, as explicitly requested in this return;
no file-local notation or private replacement of a dependency is introduced.
Self-check against the current base confirms that every node field except lean and
the three requested landed definition-owner citations is byte-for-byte equal as
JSON data. The theorem signature still equals lean.statement verbatim, the sole
sorry is the node theorem, every added citation owns an existing definition, and
all Lean lines satisfy the 100-character limit.

The repaired-packet dry run first rejected coefficientFinite in lean.declarations:
a local instance is not a public declaration exported by the module. Removed only
that entry from the public declaration list; the requested local instance remains
in the source. The preflight accepted all three landed definition-owner citations.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
