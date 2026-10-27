## Worker report

Q04 states `lem-trf-source-section-stalk-cone-comparison` in
`Sheaf.Paper.SourceSectionStalkConeComparison`. The one postponed theorem is
`WeilConjectures.trfSourceSectionStalkConeComparison`; its docstring gives all seven
proof steps. Three helper definitions contain actual compositions of published
maps. Two structures package this node's comparison families and conclusions;
they introduce no independent mathematical notion or additional assumption.
The node is unchanged except for `lean`.

Hypotheses and coefficient conventions:

- `FiniteFieldDatum.{u}` supplies the specified algebraic closure of a finite field;
  `Spec (.of D.k)` is s. `l`, `[Fact l.Prime]`, `_hl : l ≠ D.p`, and
  `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` give the
  coefficient datum. We use its constituents rather than the whole coefficient
  convention bundle, which also contains an irrelevant geometric X0.
- The residue-field `Invertible` instance and stalk-unit `hS` express the node's
  explicit assumption that ell is invertible on the schemes. Both concern only
  Spec k and the same integer ell. They are the two published APIs' expressions
  of invertibility, with no finite-Tor, term-boundedness or extra geometric condition.
- `α : D.k ≃+* D.k` is any field automorphism; every occurrence of delta is
  `Spec.map (CommRingCat.ofHom α.toRingHom)`.
- `sfIntegralConstructibleCategory l E (Spec (.of D.k))` is exactly the recorded
  derived-complete bounded constructible category. The representative `P` ranges
  over `integralOperationsGoodComplex` (flat terms and K-flat), and `q` over EVERY
  isomorphism `DerivedCategory.Q.obj P.obj ≅ N.obj`. The representative complex
  itself need not have bounded terms.
- The quotient exponent is `n + 1`, so index zero is A_1. Quotients, the completed
  coefficient sheaf, transitions and scalar actions are the published constructions.
  Their ULift accommodates the small site's object universe u+1 and morphism
  universe u; no equality between those universes is imposed.

Clause-by-clause rendering:

1. `trfQuotientTower`, `trfQuotientStalkTower`, `trfQuotientSectionTower` are the
   strict Q_n and their stalk/section towers. `integralOperationsRoos` is the
   published signed mapping cocone H, with unshifted `mappingCocone.fst` and
   shifted `mappingCocone.snd`. `integralOperationsRoosMap` acts separately on
   the two coordinates. No second cone or quotient construction is defined.
2. `B.I` and `B.hI` specify a coherent integral pullback calculus, retaining the
   actual unit and compositor. `trfSourceSectionC` inserts the inverse identity
   unit and the inverse of `integralComparisonComposition id delta`, followed
   only by the canonical `id_comp` transport. Thus its endomorphism of J_delta
   is precisely c after the stated identification of J_id with sections.
3. `B.σ` is a natural isomorphism on integral module sections. `restriction`
   fixes its values to `pointRestrictionRaw ... none`, the actual restriction,
   distinguished inverse-image insertion and coefficient transport.
   `B.ρ` is a natural isomorphism of derived sections; `restrictionDerived`
   identifies its localization with σ on every complex using the recorded
   `mapDerivedCategoryFactors` and `trfIntegralSectionsFactors`.
4. `trfSourceSectionJ` is literally `ρ.hom.app N` followed by sections of
   `inverseImagePullbackComparisonDerived`. It uses that canonical chosen-resolution
   comparison, not an arbitrary map. `representatives` asserts it is invertible
   on the stated complete constructible domain.
5. `B.e` is a strict natural tower isomorphism. `germNormalization` uses the
   recorded `TrfQuotientGermNormalized`, fixing identity stalks, pullback-unit germs
   and all strict tower coordinates. `finiteGerm` uses this SAME normalization
   for delta and asserts that finite restriction followed by the specified
   `inverseImageFiniteComparisonComplex` and finite stalk comparison gives
   `proEtaleCoefficientModuleGerm delta ... (proEtaleConstantGermNeighbourhood delta) x`.
   This is [s,delta,a], with the identity section object on the source. It does
   not confuse the pullback-unit source lift with the target delta lift.
6. `B.a₀` is a natural chain map into the identity stalk cone. `identityCoordinate`
   fixes its unshifted projection to the colimit coprojection of the actual
   `unrestrictedTowerUnit` section: [s,id,zbar_n]. `identityShifted` fixes the
   other projection to zero. The first equality in `representatives` identifies
   its localization with Γ(q), the inverse actual identity unit, and the specified
   `trfQuotientStalkRealizationArrow`. Thus it is the ACTUAL completion-unit
   normalization, not an unrelated choice of cone augmentation.
7. `trfSourceSectionConeLift` composes restriction/insertion, the published
   zero-homotopy `inverseImageRoosComparisonComplex`, the sectionwise product map
   `scalarRoosMap`, and H of the same finite germ map. The second equality in
   `representatives` identifies its localization with Γ(q), j, c, and e_delta.
   The last equality is equality of ENTIRE strict chain maps from Γ(P), between
   that specific lift and `B.a₀.app P ≫ integralOperationsRoosMap (B.R.hom.app P)`.
8. `B.R` is a strict natural tower isomorphism and `reparamGerm` fixes every
   degree and level to the published `proEtaleStalkReparam id α`. On the identity
   germ from clause 6 it gives [s,delta,zbar_n]. Its cone map is diagonal, so
   clause 6 and the entire chain equality force the shifted coordinate to zero
   on BOTH sides. This is an assertion on arbitrary sections, including noncycles.
9. `chainNaturality` quantifies over arbitrary chain maps. `derivedNaturality`
   quantifies over EVERY morphism of the derived constructible full subcategory,
   not only maps induced by chosen representatives. `realizations` asserts each
   specified e is invertible for every N,P,q. All representative identities hold
   for every q; together with natural tower maps and localization these retain
   compatibility with canonical resolution changes and roofs. No assertion that
   reductions detect arbitrary derived morphisms is made.

`HEq` in section-coordinate fields compares the identical underlying sections
when the APIs present their transported module structures differently. It retains
literal equality of their values; the central equality is an ordinary equality
of morphisms of complexes. Explicit object endpoints in functor maps avoid
expensive inference of coefficient categories.

Dependency declarations used (recorded interfaces read with their docstrings):

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `TraceFormulaCoefficientConventions`, with `FiniteFieldDatum` and the existing
  Padic coefficient rings used directly as above.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `integralDerivedPullback`,
  `integralOperationsGoodComplex`, `integralOperationsLevelPullback`,
  `integralOperationsRoos`, `integralOperationsRoosMap`, `integralTowerModules`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFibreIntegralAmbient` and the exact
  `pointIntegralSections` (the same small-Hom derived coefficient convention).
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`:
  `geometricRingModuleStalkFunctor`, with its recorded finite coefficient stalks.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (supplied by D).
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the existing completed ring.
- `Sheaf.Paper.TraceBoundedQuotientStalkRealization`:
  `trfQuotientStalkRealizationArrow`, `TrfQuotientGermNormalized`, the three
  quotient tower functors, `trfCompletedPointFibre`, `trfIntegralModuleQ`,
  `trfIntegralSectionsFactors`.
- `Sheaf.Paper.TraceStalkCompositorTowerRealization`:
  `trfStalkCompositorTowerRealization`, with the reexported
  `IntegralComparisonSystem`, `IntegralComparisonRealizationCoherence`,
  `integralComparisonUnit`, `integralComparisonComposition`.
- `Sheaf.Paper.GermReparametrizationDerivedDescent`:
  `trfGermReparametrizationDerivedDescent` and canonical strict germ reparametrization.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived` and its public upstream
  `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageIntegralModules`, `inverseImageIntegralDerived`,
  `inverseImageFiniteComparisonComplex`, `inverseImageRoosComparisonComplex`,
  `inverseImagePullbackComparisonDerived`.
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`:
  the recorded normalization of the specified kappa (proof dependency too).
- Proof interfaces imported: `PointAutomorphismRestrictionNatural`
  (`pointRestrictionRaw`, `point_automorphism_restriction_natural`),
  `ProEtale.IsoSectionwiseInverseImage`, `CompletionUnitStrictQuotientModel`,
  `ProEtalePullbackStalkCoherence`, `QuotientTensorInsertion`. All recorded
  proof modules are imported, directly or through their public owning dependencies.

Edge cases checked: alpha=id retains the actual identity unit and its equality
transport; N=0 gives zero in both coordinates; n=0 is the first positive quotient;
all integer degrees including negative ones and noncycle sections occur. No
uniform bound on terms, finite Tor amplitude, Frobenius restriction, arbitrary
replacement cone map, or reduction-detection assertion is imposed. Stacks
sites.tex Tags 0F4F and 05V1 were read, as was the current blueprint's Local
powers (b). No node fault or STATEMENT-DISPUTED flag remains.

Searches for existing declarations:

- msearch.py leanfinder: "Restriction of point sections along a field automorphism
  agrees with reparametrized geometric stalks on both coordinates of the completion
  quotient cone": eight ordinary scheme/topological stalk results, no match.
- msearch.py leansearch: "Completion unit global sections geometric stalk
  reparametrization chain map": eight general section/stalk results, no match.
- msearch.py loogle: `CochainComplex.mappingCocone.lift`: eight generic cone-lift
  constructors and projection identities, no source-section comparison.
- msearch.py grep: `mappingCocone.lift|proEtaleStalkReparam`: generic mapping-cocone
  hits only. `sourceSection|stalk.*cone|restriction.*cone` in AlgebraicGeometry:
  no matches.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for the proposed declarations,
  restriction/cone combinations, and grep of the exact node id: no existing
  statement. Nearby `PointConeLiftsChainNaturality` is Frobenius-specific;
  `CompletedStalkReparametrizationCoherence` is downstream and was not imported.
  Existing strict cone and completion-unit helpers were inspected and reused
  through the canonical published constructions, without another cone definition.

Validation: `scompile.py Q04 lem-trf-source-section-stalk-cone-comparison
lean/Sheaf/Paper/SourceSectionStalkConeComparison.lean` compiled both its sandbox
and actual module (46.7 s and 22.5 s) cleanly. No global build or direct git
operation was run. Earlier timeouts were repaired by explicit category endpoints
and heterogeneous comparisons of transported section values, without changing
any mathematical clause or the 60-second limit.

## Second reading by Q04

(Rewritten by the maintainer's second reader NT-cc review of 62b3bf49: the delivered
section was by the same worker and did not match the clauses itself.)

Node clauses and their Lean, each checked against the dependency declarations:

1. Coefficient datum k = Fbar_q, l != char k, E/Q_l finite: `D : FiniteFieldDatum.{u}`,
   `[Fact l.Prime]`, `_hl : l ≠ D.p`, `E : Type u` finite over `ℚ_[l]`. Same as the
   stmt_deps bounded-quotient realization, compositor realization, germ reparametrization. OK.
2. l invertible on s: residue-field `Invertible` instance (for the compositor calculus)
   and `hS` stalk units (for kappa = `inverseImagePullbackComparisonDerived ... hS hS`).
   Both true for s = Spec k with l != p; no stronger assumption. OK.
3. alpha in Aut(k), delta = Spec(alpha): `α : D.k ≃+* D.k`,
   `Spec.map (CommRingCat.ofHom α.toRingHom)` everywhere; alpha arbitrary. OK.
4. N in D^b_c(s,R), q : Q -> N any flat-term K-flat representative: every clause quantifies
   `N : sfIntegralConstructibleCategory`, `P : integralOperationsGoodComplex`, every
   `q : Q.obj P.obj ≅ N.obj`. OK.
5. rho = restriction along delta, inverse-image insertion, sheafification: `B.σ` pinned
   pointwise to `pointRestrictionRaw g none` (restriction along `pointRestrictionArrow g`
   in the coordinates where the distinguished coprojection is the identity);
   `B.ρ` pinned on every `Q.obj P` (hence on all objects, by naturality) as its
   localization. Isomorphisms by type. OK.
6. j = Gamma(kappa^delta) rho, kappa the specified chosen-resolution comparison:
   `trfSourceSectionJ` = `ρ.hom.app N ≫ Γ(inverseImagePullbackComparisonDerived)`;
   invertibility on the complete domain in `representatives`. OK.
7. c = Gamma(chi_{id,delta,N}^{-1}) after the identity-unit identification:
   `trfSourceSectionC` = unit⁻¹, compositor(id, delta)⁻¹, eqToHom(id ≫ g = g), all from
   the coherent `IntegralComparisonSystem` exactly as in the dependency
   trfStalkCompositorTowerRealization (same ∃ I with `IntegralComparisonRealizationCoherence`). OK.
8. e_u of lem-trf-bounded-quotient-stalk-realization: `B.e v` pinned for every v by
   `TrfQuotientGermNormalized` (the dependency's own normalization) and
   `trfQuotientStalkRealizationArrow` invertible. OK.
9. Finite formula a -> [s,delta,a] with source lift id_s, target lift delta: `finiteGerm`
   (δ normalized for B.e delta; image of restricted, inserted x is
   `proEtaleCoefficientModuleGerm delta ... (proEtaleConstantGermNeighbourhood delta) x`,
   the neighbourhood (s, delta)). OK.
10. e_id Gamma(q)(z) = (0, ([s,id,zbar_n])_n) via the actual completion unit:
    first conjunct of `representatives` (q, identity unit inverse, realization arrow =
    Q(a₀)), `identityCoordinate` (unshifted coordinate = identity germ of 1 ⊗ z),
    `identityShifted` (shifted coordinate 0 in all degrees). OK.
11. e_delta c j Gamma(q) = (0,([s,delta,zbar_n])_n) = H(R) e_id Gamma(q), entire chain maps:
    second conjunct (localization identity with `trfSourceSectionConeLift`, the
    chosen-resolution zero-homotopy lift z -> (0, theta_n z) followed by the diagonal e
    map) and third conjunct (strict equality ConeLift = a₀ ≫ H(R)), with `B.R` pinned
    to `proEtaleStalkReparam id α` in every level and degree as in the dependency. OK.
12. Invariance and naturality for all derived morphisms: `chainNaturality`,
    `derivedNaturality` (every morphism of the full subcategory), all q. No detection
    claim. OK.

Edge cases: alpha = id (eqToHom transport retained), N = 0, n = 0 is A_1 (exponent n+1),
negative degrees and non-cycles (statements are on all sections), universes: one u as in
all dependencies, ULifts of the published interfaces only.

Searches: as in the worker report; in addition grep of lean/Sheaf for users of
`pointRestrictionRaw|pointRestrictionSections` and of `proEtaleStalkReparam`: the
point-restriction Roos/system modules (lem-trf-point-restriction-whole-roos-square,
-system-chain-map, lem-trf-point-system-roos-transport) concern the Frobenius integral
model on point systems, without germ coordinates or the completion unit; the
reparametrization users are its owners and the dependencies. No duplicate.

Change made: `identityCoordinate` used `unrestrictedTowerUnit`, a declaration owned only by
the theorem node lem-weil-integral-reduction-tower-well-defined, which the item does not
cite. It is replaced by its defining sectionwise value
`unrestrictedTowerTensorSection ... (P.X i) U 1 x` (definition node
def-sf-unrestricted-reduction-complex-constructions; equality by the published
`unrestrictedTowerUnit_condition`). Same mathematics; per-file compile clean (32.4 s).
