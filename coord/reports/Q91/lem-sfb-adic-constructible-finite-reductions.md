## Worker report

Q91, stage 2 repair, 2026-10-17. This packet repairs the immutable-head return
`e5a2367f45b2`, points H3, H4 and H9. It states
`AlgebraicGeometry.Scheme.adic_constructible_finite_reductions` in
`lean/Sheaf/Paper/AdicConstructibleFiniteReductions.lean`. The main theorem and the
named construction/existence lemmas have `sorry` proofs. All definitions have real data;
choices of maps are made only from unique sectionwise or K-flat normalizations, and the
geometric algebraic lift is the existing universally specified inverse-image construction.

The initial prescribed dry run was run on the retained packet before repairs. It reached
preflight and reported the stale `lean.statement` when the file had meanwhile been repaired.
The packet has been retained and repaired, not restarted or re-pushed unchanged.

### Returned points

- H3: replace `A : Type u` by `A : Type (max v (u + 1))`, with independent, explicitly
  bound `u v`. `N : adicFiniteAmbient.{u,v} X A` is exactly
  `ConstantCompletion.D (ConstantCompletion.constant
  (coefficientProEtaleModelTopology.{u,v} X) A)`. Both the etale categories and the quotient
  categories use the same standard localization and coefficient universe. No coefficient
  ring is shrunk or replaced by a finite ring. The Type-u-only `proEtaleDerivedCategory`,
  `HasProEtaleTorAmplitude`, `etaleOriginRealization` and fixed-scalar APIs are no longer
  used to restrict the theorem. The Tor and constructibility dependencies receive the
  equivalent generalized interfaces described below.
- H4: the module publicly imports `Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison`.
  `adicFiniteComparisonData`, `adicFinitePullback`, and its computation comparison use
  the recorded `smallModelProEtaleComparison.{u,v} X` directly. Its left adjoint is the
  recorded `smallModelComparisonPullback`; its algebraic lift and canonical constant map
  come from `ConstantCompletion.inverseImageData_exists` and `constantMap`. The earlier
  report's claim to use `smallModelProEtaleComparison` through `comparisonUpperStar` was
  incorrect. The dependency list below describes the repaired file.
- H9: the unused public `LocallyClosedStratification` import is removed from the item.
  The constructibility dependency module genuinely uses that existing structure through
  its owning module's public import.

### Hypotheses and every conclusion clause

1. `X : Scheme.{u}` and `[IsNoetherian X]` express the finite affine Noetherian cover.
   `A : Type (max v (u+1))`, `[CommRing A]`, `[IsNoetherianRing A]`, and `J : Ideal A`
   express arbitrary commutative Noetherian coefficients and their ideal. There is no
   finiteness-as-a-set, regularity, perfection or flatness assumption.
2. `N : adicFiniteAmbient.{u,v} X A` is the unbounded derived category of modules over
   the actual constant ring sheaf on the equivalent coefficient-sized small pro-etale
   site. `adicFiniteComplete X A J N` uses the recorded `ConstantCompletion.IsComplete`
   for the kernel of the actual constant quotient `A → A/J^1`. Thus it is exactly local
   derived `J`-completeness, with all objects and slices retained by AsSmall.
3. `adicFiniteCoeff J n = A/J^(n+1)`. The natural index zero is the first positive
   exponent, canonically `A/J`; no zero-power conclusion is asserted. Quotient maps,
   ordered factor maps and their equalities are Mathlib's `Ideal.Quotient.mk`,
   `factorPow`, `factor_comp_mk` and `factor_comp`.
4. `C : adicFiniteEtale.{u,v} X J 0` is the etale residue object.
   `IsCoefficientBoundedConstructibleEtale X (adicFiniteCoeff J 0) C` requires all its
   cohomology sheaves to be constructible and to vanish outside one finite interval.
   Constructibility uses the existing `LocallyClosedStratification` on every affine open,
   constructibility of each stratum, actual etale inverse image on equivalent small sites,
   and covering sieves trivializing to constant finitely generated modules. On our
   Noetherian X this affine-local definition equals the node's finite global stratification
   condition. It does not impose finite underlying coefficient or stalk sets.
5. `e : (adicFinitePullback X (adicFiniteCoeff J 0)).obj C ≅ adicFiniteReduction X J N 0`
   is the given residue marking, oriented like alpha. Inverting it gives the orientation
   in the prose. `a b : ℤ`, `hab : a ≤ b`, and `hTor` test the existing total tensor on
   every K-flat representative of C and every degree-zero module sheaf outside `[a,b]`.
   K-flat resolutions exist, so this is the same derived-tensor condition, without a
   vacuous test or a chosen resolution.
6. Each `adicFiniteReduction X J N n` is the existing universal derived extension
   `ConstantCompletion.extend` along the actual quotient. The named normalization lemmas
   specify the canonical maps that the node's own statement calls the quotient transition,
   rho and the scalar/pullback comparison. Ordinary scalar units are fixed by insertion;
   ordinary composition is fixed on pure tensors. Their derived units and isomorphisms
   are uniquely fixed by these maps under the universal K-flat comparisons. The comparison
   with nu is fixed by ordinary insertion and its flat-term K-flat computation square.
   These are construction interfaces for this node's stated maps, not arbitrary maps or
   unconstrained `Nonempty` isomorphisms, nor additional mathematical hypotheses.
7. The first conclusion supplies `HasProduct (adicFiniteUnderlying X J N)` and the
   recorded `IsDerivedLimit (adicFiniteTransition X J N) N`. Underlying means actual exact
   restriction to A. The transition is its canonical derived quotient unit followed by
   canonical balancing and restriction composition. This is exactly `N ≃ R lim N_n`,
   expressed by the existing Milnor-triangle property. Product existence is a conclusion.
8. The second conjunct says `IsZero` of the standard homology of N for every
   `q < a ∨ b < q`, with the same interval. The third says every positive reduction has
   `HasCoefficientProEtaleTorAmplitude X (A/J^(n+1)) ... a b`, the recorded Tor notion
   on the equivalent site, with the same all-module-sheaf tests.
9. The existential `Cn`, `alpha` and `beta` retains all bounded etale quotient complexes,
   their specified pro-etale isomorphisms, and the quotient isomorphisms. Every `Cn n`
   satisfies bounded constructibility and the same Tor interval. `hzero : Cn 0 = C` and
   the equation using `eqToIso hzero` say that `alpha 0` is precisely the supplied marking,
   not an independently chosen residue isomorphism.
10. Beta is supplied for all ordered pairs, with canonical `adicFiniteExtensionComp`
    in its `r ≥ m ≥ n` cocycle. This is the adjacent beta system together with its
    iterates; equal indices enforce unit normalization. The last equation is
    `nu*(beta) ≫ alpha_n = comparison.inv ≫ extension(alpha_m) ≫ rho`.
    `adicFiniteComparison` is exactly the canonical source identification. Thus it
    renders the node's alpha compatibility, including its retained residue marking.

The main theorem's ten-step natural-language proof is retained in full from the node:
K-flat balancing; Tor propagation through the ideal filtration; completeness and Milnor
bounds; constructibility under nilpotent reduction; etale origins; and unique full-faithful
lifts of beta and their cocycle. Each postponed construction lemma has its own proof
explanation and source/blueprint docstring. These helpers specify the canonical maps already
named in the item's statement and proof; they are listed in its `lean.declarations`.

### Dependency declarations used

- Scheme and Noetherian ring: Mathlib `AlgebraicGeometry.Scheme`, `IsNoetherianRing`,
  and `IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
- Original pro-etale/etale sites and their coefficient-sized models:
  `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`,
  `coefficientProEtaleSiteModel`, `coefficientProEtaleModelTopology`;
  `Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison`,
  `smallModelComparisonEtaleTopology`, `smallModelComparisonInclusion`,
  `smallModelComparisonPullback`, `smallModelComparisonPushforward`,
  `smallModelProEtaleComparison` and its finite-limit preservation.
- Constant sheaves and modules: Mathlib `CategoryTheory.constantSheaf`,
  `SheafOfModules`, `SheafOfModules.restrictScalars`, and `CategoryTheory.ringedSiteModules`.
  `Sheaf.Paper.ConstantCompletionEquivalence` supplies the genuine constant rings, quotient
  maps, `Mod`, `Cx`, `D`, `Q`, `change`, `extend`, `extendComparison`, `res`, `dres`,
  `resFactors`, scalar insertion, `inverseImageData_exists`, `pull`, `derivedPull` and
  `constantMap`. Its `IsComplete` wraps the recorded
  `CategoryTheory.IsLocallyDerivedRingedIdealComplete` via the unique kernel ideal.
- Derived scalar extension: the recorded
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` in
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`, through the
  universally specified `ConstantCompletion.derivedExtension`. No second derived tensor
  is defined. The Tor test uses `CategoryTheory.ringedKoszulTensor`, the existing total
  tensor, on the recorded `CochainComplex.IsKFlatIndependentCoefficients`.
- Constructible strata and finiteness: the recorded
  `AlgebraicGeometry.Scheme.LocallyClosedStratification` and Mathlib `Module.Finite`.
  Generalized constructible etale sheaves and their full categories are the §1(B)
  dependency module below, retaining the originally recorded module publicly.
- Tor amplitude: the §1(B) dependency module below publicly retains
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude` and supplies the identical predicate
  on the coefficient-sized site. Both etale and pro-etale tests use the same generic
  representative-level condition.
- Derived limit: `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
  `CategoryTheory.IsDerivedLimit`. Actual quotients and ideal powers are Mathlib's
  recorded matches in `Ideal.Quotient` and `Ideal`.

The three added statement dependencies are landed nodes:
`def-weil-proetale-inverse-image` owns the coefficient-sized pro-etale model;
`lem-weil-pbc-constant-completion-equivalence` owns the generic constant-ring localizations,
completeness, scalar operations and algebraic lifts;
`def-pe-etale-constructible-module` owns constructibility and the bounded/full categories.
A read-only traversal of each complete statement/proof closure found no path back to this
item (168, 623 and 110 visited nodes, respectively). Proof-only imports from the original
packet are retained as the stage-3 proof plan. No target or natural-language node statement
has been changed, and no new definition node is needed.

### Sources, searches and edge cases

Read the original packet, current shared DAG records, the returned immutable-head review,
the recorded interfaces and the generalized small-model interfaces, parent
`AdicResidueLissePerfectLift` (coefficient universe `max v (u+1)`) and sibling
`AdicStratifiedPerfect` (coefficient universe `u+1`). Reopened
`literature/stacks-project/proetale.tex`, lemma-describe-constructible-complexes, Tag 09C2,
and its proof, together with its constructible derived-comparison input Tag 09AL. The
coefficient-size generalization is presentation transport of exactly these objects.

The retained packet had already run the required LeanFinder, Loogle, LeanSearch and grep
searches for the finite-reduction theorem, finding no exact match. Fresh repair searches:

- `msearch.py ... leanfinder`: "Tor amplitude of a complex of module sheaves on a site
  tested on every K-flat representative and every module in degree zero". Eight hits,
  the standard `DerivedCategory.isGE/isLE` and single-complex lemmas; no exact interface.
- `msearch.py ... leanfinder`: "constructible sheaf of modules over a Noetherian ring
  affine locally finite constructible locally closed stratification and etale locally
  constant finitely generated models". Eight hits concern `SheafOfModules.IsFiniteType`,
  local generators and finite presentation; none gives the constructible etale notion.
- `msearch.py ... loogle`: `"CochainComplex.IsKFlat", "GrothendieckTopology"`: zero hits.
- `msearch.py ... grep`: `HasCoefficientModelTorAmplitude|IsCoefficientConstructibleEtaleModule|
  adicFiniteExtendComp`: zero Mathlib hits.
- `rg` for these names in upstream `WeilConjectures` and shared `lean/Sheaf`: no hits.
  Concept searches found and reused `ConstantCompletion`, the recorded small comparison,
  `ConstructibleNoetherianEtaleModules`, existing locally constant finite-module models,
  and the independent-coefficient K-flat APIs. The original fixed-scalar witness helpers
  and upstream constructible predicates require coefficients in `u+1`; they do not give
  the independent-v interface. Searches are also retained by the launcher search log.

Checked: empty X, zero object, zero ring, J=0, J=top, exponent one, a=b, nonfinite
quotients such as k[s], singular Noetherian rings, and the two actual consumer universe
choices. Empty strata/covering families over empty schemes are permitted. Module values
remain finitely generated rather than finite sets. The site models retain all objects,
arrows, covers and slices by equivalence; their universe enlargement adds no mathematical
hypothesis. No `STATEMENT-DISPUTED` issue or statement correction is present.

### Validation

All compilation uses the required `scompile.py` wrapper, separately per file and in
import order. No global build, direct live compilation, git command, push or delivery
was performed by the worker. Final scompile.py passed for all three files with no errors or warnings. The main module
compiled in 11.0 seconds as a sandbox and 11.6 seconds at its library path; both dependency
modules compiled in under 3 seconds each. The full theorem, every canonical-map helper and
both dependency interfaces were checked.

The last universe diagnostic was an imported high-priority successor-universe
sheafification instance. As in the existing ProEtaleMilnorSequence module, the item disables
that instance within the file and uses the general small-site theorem instead. The Tor
dependency also exposes the two exact-size model sheafification instances. This changes
no site, coefficient, class hypothesis or mathematical condition.

The required `deliver2.py Q91 lem-sfb-adic-constructible-finite-reductions --no-push`
printed `OK (dry run): commit 80a2cf8450 passes the preflight and compiles; nothing pushed`.
The final self-check confirmed the permitted JSON field deltas, complete declaration
inventories, 100-column Lean lines, and removal of every temporary #check probe.
The packet is ready for the separate independent second reader; it has not been delivered.

## Dependency modules

`def-weil-proetale-tor-amplitude`:
`Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` publicly retains the recorded
original predicates and generalizes their interface to
`HasCoefficientProEtaleTorAmplitude` and its finite-interval version with
`A : Type (max v (u+1))`. The original declaration `HasProEtaleTorAmplitude` required
`A : Type u`, and so could not express this node at its consumers' coefficient sizes.
`HasCoefficientModelTorAmplitude` tests every K-flat representative and every degree-zero
module using the existing total tensor; `coefficientModelCohomology` selects the same
standard localization. The mathematical Tor condition is unchanged. Only this node's
`lean` record is changed; no old declaration is replaced or duplicated.

`def-pe-etale-constructible-module`:
`Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules` publicly retains
`ConstructibleNoetherianEtaleModules` and supplies its affine-local notion and both full
categories on coefficient-sized etale models. The recorded interface tied coefficients
to `u+1` and used `Etale.upperStar` with the same size restriction. The replacement
interface transports base change to the existing AsSmall models, takes its actual Kan
extension/sheafification inverse image, and trivializes on the localized equivalent sites.
Constant scalar restriction keeps the additive sheaf. Strata are the recorded structure;
constant values are `Module.Finite`. Its continuity helper is the transport of the same
etale base-change continuity, with a complete proof docstring. Only the `lean` field is
changed, and its required note records the reason and the identical generalized notion.

## Earlier second reading (a previous round; superseded)

The saved packet contained a second reading of the old Type-u statement. The maintainer
returned that head for its coefficient-size restriction and incorrect comparison dependency
claim; that reading does not validate this repaired packet. This worker has performed the
clause-by-clause self-check above. A separate second reader must independently read the
three current modules and the two dependency repairs before delivering. No independent
second reading of these repairs is claimed here.

## Second reading by Q91

Independent second reader, 2026-10-17. I read the current node, all three delivered
modules, both dependency nodes, their previous recorded interfaces, and the immutable-head
return in `coord/returns/Q91.md`. There is no maintenance repair-note file for this item.
This reading validates the repaired packet, not the earlier Type-u packet. No further
Lean or node edit was needed; this report section is the second reader's change.

### Source and clause-by-clause reading

I first read `proetale.tex`, the setup and definition immediately before
`lemma-describe-constructible-complexes` (09C1), the whole statement and proof of 09C2,
and `lemma-compare-constructible-derived` (09AL). The setup assumes an arbitrary
Noetherian coefficient ring and an ideal, not a finite coefficient ring. 09C2 assumes
quasi-compactness; our node explicitly specializes to a Noetherian scheme and fixes the
residue Tor interval. The additional marked etale tower is the full-faithfulness
transport explained in the node's proof. I also read `etale-cohomology.tex`, the
paragraph before `definition-constructible` and clause (3) (03RW), for the repaired
constructibility definition.

The following is my object, hypothesis and conclusion checklist. Every entry passes.

1. **Scheme and finiteness hypothesis.** The node introduces a scheme X with a finite
   affine Noetherian cover. Lean has `(X : Scheme.{u}) [IsNoetherian X]`.
   Mathlib's `IsNoetherian` is locally Noetherian plus compact, and
   `isNoetherian_iff_of_finite_iSup_eq_top` gives precisely the node's cover condition.
   There is no separatedness, finite type over a field, or nonemptiness hypothesis.
2. **Coefficients and ideal.** The node introduces a commutative Noetherian ring A and
   an arbitrary ideal J. Lean has `(A : Type (max v (u + 1))) [CommRing A]
   [IsNoetherianRing A] (J : Ideal A)`. The explicitly bound independent `v` repairs
   the returned size restriction. `IsNoetherianRing` is the recorded Mathlib notion;
   there is no field, finite-set, principal-ideal, proper-ideal, regularity or
   completeness assumption on A.
3. **Ambient object.** The node's N is in the unbounded derived category of modules
   over the actual constant A sheaf on the small pro-etale site. Lean has
   `N : adicFiniteAmbient.{u, v} X A`, unfolding to `ConstantCompletion.D
   (constant (coefficientProEtaleModelTopology.{u,v} X) A)`. I opened `constant`,
   `Mod`, `D` and `Q`: these use Mathlib's constant sheaf, `ringedSiteModules`, and
   the standard quasi-isomorphism localization, not a different category or Abelian
   structure. The AsSmall model retains the original site by equivalence.
4. **Local derived completeness.** The node assumes local derived J-completeness of
   N. Lean's `hcomplete : adicFiniteComplete X A J N` uses `ConstantCompletion.IsComplete`
   at the actual quotient map to A/J^1. I opened the uniquely sectionwise specified
   `kernelIdeal` and `IsLocallyDerivedRingedIdealComplete`: the latter tests derived
   internal Hom from localization at every ideal section on every slice. Thus the
   hypothesis is local completeness for J times the constant A sheaf, with no bound
   on N assumed.
5. **Residue origin, constructibility and given marking.** Lean has
   `C : adicFiniteEtale X J 0`, `hC : IsCoefficientBoundedConstructibleEtale ... C`,
   and `e : (adicFinitePullback ...).obj C ≅ adicFiniteReduction X J N 0`.
   C is over A/J^1; inversion of e gives the orientation of the displayed residue
   isomorphism in the node. The constructibility predicate uses the recorded finite
   scheme stratification, an explicit constructible-subset clause, actual inverse
   image along each stratum immersion, and locally constant `Module.Finite` models.
   It also requires cohomology to vanish outside one integer interval. On Noetherian
   X its affine-local definition agrees with the node's finite global stratification:
   choose a finite affine cover and refine its strata by the successive differences
   of those opens, then use the finitely many resulting locally closed pieces.
6. **Specified Tor interval.** Lean's `(a b : ℤ) (hab : a ≤ b)` and `hTor` render
   exactly the node's ordered interval and its tests against every degree-zero etale
   module sheaf. `HasCoefficientModelTorAmplitude` quantifies over every K-flat
   representative isomorphic to C and every module M, with `q < a ∨ b < q` as the
   excluded degrees. I opened the independent-coefficient K-flat resolution theorem
   and total tensor interface: representatives exist, and their ordinary total tensors
   compute the derived tensor. The test is not vacuous or confined to finite modules.
7. **All positive quotient reductions and their maps.** `adicFiniteCoeff J n` is
   A/J^(n+1), `adicFiniteQuotient` is `Ideal.Quotient.mk`, and `adicFiniteFactor`
   is the recorded `factorPow`. This reindexes the node's n >= 1 by Lean naturals.
   `adicFiniteReduction` is the universal derived scalar extension along that map.
   `adicFiniteRho` is derived tensor balancing. `adicFiniteUnderlying` uses exact
   scalar restriction to A; `adicFiniteTransition` uses the derived quotient unit,
   rho, and restriction composition. No transition or normalization is an arbitrary
   argument to the theorem.
8. **Derived limit.** The first conjunct supplies product existence and
   `IsDerivedLimit (adicFiniteTransition X J N) N` for the underlying A-module
   objects. I opened the recorded `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
   in the shared clone: it is precisely existence of the node's Roos triangle.
   The conclusion therefore states that N is a derived limit of its quotient tower.
9. **Cohomology bound of N.** The second conjunct is
   `∀ q : ℤ, (q < a ∨ b < q) → IsZero ((coefficientModelCohomology ... q).obj N)`.
   It uses the standard localization's homology functor and the original endpoints,
   with no extra degree at the upper end.
10. **Tor bounds of every reduction.** The third conjunct asserts
    `HasCoefficientProEtaleTorAmplitude X (adicFiniteCoeff J n)
    (adicFiniteReduction X J N n) a b` for every natural n. It retains the quotient
    scalar action, every module-sheaf test, and the same interval.
11. **Etale quotient objects and their markings.** The existential Cn, alpha, beta
    supplies a bounded constructible etale A/J^(n+1)-object for every n, its
    pro-etale isomorphism alpha, and its quotient comparison beta. Both the bounded
    constructibility and Tor conditions are asserted for every Cn, not only its
    first member. There is no assertion that A/J^n is perfect as an A-module.
12. **Retained input.** `∃ hzero : Cn 0 = C` and the equation
    `pullback.map (eqToIso hzero).hom ≫ e.hom = (alpha 0).hom` preserve both the
    given residue object and the given residue marking, rather than merely asserting
    an unrelated isomorphic first term.
13. **Cocycle.** Beta is supplied for all ordered pairs `n ≤ m`; the equation for
    `r, m, n` uses `adicFiniteExtensionComp` with `adicFiniteFactorComp`.
    This is the adjacent system and its iterates, including equal-index cases,
    with precisely the canonical tensor reassociation in the node.
14. **Alpha compatibility.** The final equation has left side
    `pullback.map beta.hom ≫ alpha_n.hom`; its right side is the inverse canonical
    scalar/pullback comparison, scalar extension of alpha_m, and rho. Their sources
    and targets match the node's equation after its implicit canonical identification.
    The quantifier covers every ordered pair, including adjacent and identity maps.

### Dependency repairs and canonical data

I read the recorded `smallModelComparisonEtaleSite`, its topology, the transported
inclusion, `smallModelComparisonPullback`, pushforward and `smallModelProEtaleComparison`,
and the coefficient-sized pro-etale model. The item imports and directly uses that
adjunction in `adicFiniteComparisonData` and `adicFinitePullback`. This fixes H4 of
the return, without substituting the upstream fixed-coefficient comparison.

For `def-weil-proetale-tor-amplitude`, I compared its whole node statement with both
the original `HasProEtaleTorAmplitude` and the delivered coefficient-sized interface.
The original requires A in the scheme universe and cannot type the returned consumers.
The repair has the same module-sheaf Tor tests on equivalent sites and also retains
the finite-amplitude existential. Its sheafification instances construct the existing
size-correct instances. There are no new ring or scheme hypotheses. Only `lean` changes.

For `def-pe-etale-constructible-module`, I compared its full node statement with
`ConstructibleNoetherianEtaleModules` and the delivered module, against 03RW(3) and
09AL. The old interface fixes coefficients to u+1. The repaired interface keeps
arbitrary schemes, affine-local constructible locally closed strata, finite generation,
actual etale restriction, and both full subcategories. Its local covering-sieve
condition on every object is equivalent to etale local constancy: testing the final
object gives a trivializing cover of the scheme, and base change gives covers of all
other objects. The constant-scalar restriction keeps the additive sheaf and its
linear maps. The continuity theorem transports the genuine base-change functor;
it is a named postponed theorem with source and proof docstring. Only `lean` changes.

I also checked the unit, restriction-composition, tensor-composition and
scalar/pullback-comparison helpers in the item. Each chosen map is determined by a
unique sectionwise insertion, pure-tensor formula, or K-flat computation square.
`InverseImageData` and the derived functors retain their algebraic or derived universal
properties from the recorded dependency. Thus these choices are permitted universal
constructions, not hollow data or bare unconstrained isomorphisms. Every new theorem
has proof `sorry`; definitions contain actual constructions. All helper declarations
are inventoried in `lean.declarations`. The main docstring contains the node's ten
proof steps, including the local stratification refinements in Steps 6 and 8.

I opened the two returned consumers' signatures. `AdicResidueLissePerfectLift` uses
exactly the independent `max v (u+1)` coefficient models and standard localization
used here. `AdicStratifiedPerfect` uses coefficients of size u+1, covered by v=0.
No size equality between u and v is required by the item or repaired predicates.
The old Type-u Tor and derived-category declarations impose no binder here.

### Independent searches and edge cases

Fresh prescribed searches, with receipts in `searches.jsonl`:

- LeanFinder: "Derived complete complex whose residue has constructible cohomology
  and finite Tor dimension has compatible constructible finite quotient reductions".
  Eight hits: derived-category fraction factorizations, bounded representatives and
  injective derived-functor vanishing; no matching theorem.
- Loogle: `"IsDerivedLimit", "Tor"`. Zero hits.
- LeanSearch: "A derived adically complete sheaf complex is the derived inverse limit
  of its constructible quotient reductions with a uniform Tor interval". Eight hits
  concerning ordinary module adic completion, not this sheaf-derived statement.
- LeanFinder: "Locally constant sheaf of finitely generated modules on finite
  constructible strata of an affine open scheme, and Tor amplitude tested using K-flat
  tensor representatives". Eight hits concerning general finite type/presentation and
  condensed modules; no matching stratified etale notion or Tor predicate.
- Independent `rg` searches in Mathlib, upstream `WeilConjectures` and shared
  `lean/Sheaf` used `adic_constructible`, `describe.constructible.complex`,
  `finite.reductions`, and the three new coefficient predicate names. The latter
  have no existing hits. The finite-reduction hits are completed-coefficient,
  finite-coefficient, purity or consumer constructions. I opened the pertinent
  `FiniteTorAmplitude`, `AdicResidueLissePerfectLift` and `AdicStratifiedPerfect`
  interfaces; none states this arbitrary-Noetherian-ring conclusion. The existing
  constructibility and Tor interfaces are reused and generalized under section 1(B),
  rather than treated as absent notions. No new definition node is needed.

Edge cases checked against the actual definitions: empty X (empty strata allowed),
zero complex, zero coefficient ring, J=0, J=top, the first positive quotient at n=0,
equal endpoints a=b, equal-index beta, arbitrary characteristic, singular Noetherian
coefficients, and infinite residue rings such as k[s]. J=top forces the complete
object to vanish, consistent with all conclusions. No module-value finiteness-as-a-set
or nonzero hypothesis excludes these cases. The tower index is always the positive
quotient sequence; no empty-index assumption is introduced. Independently bound u and
v cover both returned consumer sizes.

### Changes and validation

No mathematical mismatch remains in the repaired packet, and no source-based statement
correction is needed. I preserved the Lean and JSON files. I verified verbatim
`lean.statement` signatures, all declaration inventories, source/blueprint docstrings,
100-column Lean lines and explicitly bound universes/variables. The two dependency JSON
files differ from the shared base only in `lean`. A fresh traversal of the three added
statement-dependency closures visited 110, 168 and 623 nodes respectively, with no path
back to this item.

All three delivered files passed my fresh `scompile.py` invocation, separately and in
dependency order, with no errors or warnings. The main library-path compile took
11.6 seconds; the dependency modules took 1.9 and 2.7 seconds. The wrapper was invoked
from the sandbox after correcting an initial relative-path invocation from the shared
read-only checkout. There was no direct compiler, global build, live edit or git command.
The required dry run and final delivery follow this reading.

Second-reader dry run: `deliver2.py Q91 lem-sfb-adic-constructible-finite-reductions
--no-push` printed `OK (dry run): commit fc7cfb4f38 passes the preflight and compiles;
nothing pushed`. The prescribed wrapper handled the worktree and shared-fetch queues.
