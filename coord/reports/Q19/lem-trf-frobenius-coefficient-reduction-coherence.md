## Worker report

The delivery states the coefficient-reduction coherence node. All theorem proofs are sorry;
all definitions have real data. Helpers give the canonical quotient normalization and the
unit-normalized finite pullback/reduction comparison in the existing completed-integral and
constant finite coefficient presentations. No independent mathematical notion is introduced.

Hypothesis correspondence:

- The global finite-field datum is D : FiniteFieldDatum. Its p, a, q, k0 and k are the
  recorded ones. X₀ : Over (Spec (CommRingCat.of D.k₀)), LocallyOfFiniteType, QuasiCompact
  and IsSeparated give precisely the separated finite-type model, and
  (D.geometricFiber X₀).left is its specified base change to k.
- l : ℕ, Fact l.Prime and Fact (l ≠ D.p) give the coefficient prime condition.
  E : Type u, Field E, Algebra ℚ_[l] E and FiniteDimensional ℚ_[l] E give the finite
  extension. Padic.coefficientExtensionRing l E (n+1) is the recorded valuation-ring
  quotient by the recorded uniformizer power. It is not replaced by ZMod or an
  unramified coefficient ring. Both scheme and coefficient data remain in arbitrary u;
  the pro-etale site still has object size u+1 and Hom size u.
- K : sfIntegralConstructibleCategory l E X contains derived completeness,
  constructibility of every positive reduction and its common bounded interval.
  _hK explicitly asserts finiteTorConstructible of every reduction, retaining the
  extra Dᵇ_ctf hypothesis. The repeated _hL in the naturality clause gives the same
  domain for its second object. The coefficient reductions are always over the
  completedIntegralCommRingSheafUnrestricted, never a discrete constant integral ring.
- P, Q and e, d quantify over every good representative and its identification;
  they do not require any additional existence or a special resolution choice.
- a,b : ℕ and h : a ≤ b enumerate every b+1 ≥ a+1 ≥ 1, including equal levels.
  r,s,m and their lower bounds enumerate precisely the positive powers in the node.

Clause correspondence:

- frobeniusIntegralReduction_coherent states T(alpha_b), then the canonical finite
  pullback/reduction comparison and pullback of eta, equals eta at integral pullback
  followed by alpha_a. Here alpha is exactly integralPullbackReductionIso, whose first
  factor is the projection-adjoint integralPullbackFiniteComparison of the dependency.
- frobeniusIntegralReduction_natural is the full naturality square for any morphism
  of the allowed integral objects and arbitrary good representatives on both ends.
- frobeniusIntegralReduction_composition intertwines the existing normalized integral
  composition with integralFiniteCanonicalPullbackComposition along g^r and g^s.
- frobeniusFiniteComposition_reduction states the quotient square for that same finite
  composition, so composition and reduction are compatible simultaneously.
- frobeniusSchemeGalois_reduction states T(kappa_b), then the geometric pullback
  reduction identification, equals the scheme pullback reduction identification
  followed by kappa_a. The eta factors on both sides identify T(K_b) with K_a.
  frobeniusCoherenceKappa selects the witness of schemeGaloisComparison together with
  its section-normalized absolute-Frobenius/factorization characterization, at every
  m ≥ 1. It does not introduce an arbitrary isomorphism as a hypothesis.

Canonical helper normalization:

- frobeniusReductionRingMap is an abbreviation of the existing
  flatModelReductionRingMap; frobeniusReduction is the existing universal derived
  change of rings applied to that map.
- frobeniusReductionNormalization is selected from a unique-existence theorem whose
  equation identifies it on every K-flat computation with the published reductionBalance.
  That balance sends the two scalar factors to their product, with inverse inserting 1.
- The finite pullback/reduction comparison is the specialization of
  `AlgebraicGeometry.Scheme.proEtaleReductionPullbackIso` from
  `Sheaf.Paper.FourCorners`, with the two constant coefficient maps and their
  canonical inverse-image comparisons. Its coefficient-square proof is exactly
  `proEtaleConstantInverseImageMap_naturality`; the displayed comparison is the
  inverse of the generic FourCorners orientation. The component helper is its
  application to an object. No flatness of a coefficient quotient is imposed,
  and the previously duplicated ordinary/counit/unique-existence helpers are absent.
- frobeniusCoherenceInvertible reuses schemeFrobeniusCoefficientInvertible to supply
  the invertibility required by integral pullback from l ≠ p. Its Fact binder is
  exactly that original condition. The finite coefficient witness reuses
  Padic.finite_coefficientExtensionRing. The annihilator lemma supplies the existing
  schemeGaloisComparison hypothesis from the DVR quotient, including ramification.

Dependency declarations used:

- Sheaf.SixFunctors.SchemeFrobenius: FiniteFieldDatum.schemeFrobeniusIterate,
  geometricGaloisFrobenius, schemeFrobeniusCoefficientInvertible.
- Sheaf.Paper.SfIntegralConstructible: sfIntegralConstructibleCategory.
- Sheaf.Paper.AdicCoefficientDatum: reductionDerivedChange, reductionChange,
  reductionTensorSection, reductionBalance, reductionScalarComplexCounit.
- Sheaf.Paper.DerivedPullbackTensorHom: constructibleIntegralPullback.
- Sheaf.Paper.IntegralOperationsPreserveConstructible: integralPullbackFiniteComparison
  and integralOperations_preserve_constructible, used through integralPullbackReductionIso.
- Sheaf.Paper.IntegralPullbackComposition: integralPullbackReductionIso,
  IntegralPullbackCompositionFamily, integralPullbackComposition.
- Sheaf.Paper.IntegralFinitePullbackComposition: integralFiniteCanonicalPullbackComposition.
- Sheaf.SixFunctors.SchemeGaloisComparison: FiniteFieldDatum.schemeGaloisComparison;
  it retains the absolute-Frobenius-site and factorization normalizations from
  Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite and FrobeniusFactorization.
- Sheaf.Paper.FrobeniusCoefficientReductionMap: frobeniusReductionRingMap, whose data is the recorded flatModelReductionRingMap.
- Sheaf.Paper.FourCorners: proEtaleReductionPullbackIso, specialized with constant coefficient maps.
- Sheaf.Paper.FiniteTorAmplitude: finiteTorConstructible.

The finite coefficient and geometric data of def-trf-coefficient-conventions are
unbundled using those same recorded definitions. Its large convenience module also
imports compact-support constructions which this statement does not use; a compile
through it reached unrelated current source failures in IntegralCompactSupportCoefficientData
(IsIso openRestrictionMap and IsIso completedPullMap). The smaller imports above retain
the actual definitions of every datum used here; no second convention is defined.
The existing landed finite-Tor, finite quotient, four-corners, and composition-family
definition nodes are included in stmt_deps because their declared interfaces occur in
the delivered constructions and clause statements.
The proof dependency lem-trf-scheme-galois-coefficient-change has no recorded Lean module
in the base read for this delivery. No nonexistent import is added: the last theorem
states its required quotient specialization here and its docstring supplies the
sectionwise proof argument. All other proof dependencies are imported directly or
through their published owning interfaces; the normalized tower, slice operations and
well-definedness proof modules are explicitly imported for the proof plan.

Edge cases read before writing: K = 0, the empty scheme, a = b, level one,
r = s = m = 1, nonflat A₂ → A₁, ramified E, and nonreduced finite-type models.
Nothing excludes any of these. Zero powers and exponent zero are not required by this node.
Equal-index quotient maps and tower normalizations are canonical identity identifications;
the same formulas apply without an extra strict inequality. The two Frobenius actions
are the recorded scheme maps; geometric Frobenius is not assumed to be k-linear.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches performed:

- msearch.py leanfinder, “Frobenius pullback comparison commutes with derived coefficient
  quotient reduction tower”: eight perfection/coefficient Frobenius results, no match.
- msearch.py loogle, “CategoryTheory.NatTrans.naturality”: nine generic naturality and
  cone results; these presuppose the transformations that the node needs to construct.
- msearch.py leansearch, “Derived coefficient reduction commutes with Frobenius pullback”:
  eight perfection and Witt-vector identities, no match.
- msearch.py grep, “pullback.*reduc|reduc.*pullback”, CategoryTheory: adhesive pullback
  results, not this derived Frobenius coefficient comparison.
- rg over the upstream WeilConjectures and project lean/Sheaf: found the published
  integralPullbackReductionIso and integral composition interfaces; no exact coherence
  theorem. Upstream Frobenius/coefficient hits concern Weil-sheaf stalks and actions.
- grep of the item id in upstream WeilConjectures: no match.
- rg of all proposed main/helper names in dag/lean_names_upstream.json, upstream sources,
  and lean/Sheaf: no conflicting declaration.

## New nodes

- `def-trf-frobenius-coefficient-reduction-map` in
  `Sheaf.Paper.FrobeniusCoefficientReductionMap` owns the constant coefficient
  quotient map used by the item. Its body is the existing
  `flatModelReductionRingMap`; it introduces no arbitrary map and has real data.
- `def-trf-integral-pullback-composition-family` records the existing definition
  `WeilConjectures.IntegralPullbackCompositionFamily` at definition level, so the
  item can use the composition family without making its statement dependency a
  theorem node.

## Dependency modules

No dependency module repair was needed. The returned `lem-sf-reduction-flat-model`
interface was used only for its recorded definition, so the item now cites the new
owned map definition instead. The finite pullback interface is supplied by the
published `def-weil-pbc-four-corners` declaration, and the integral composition
family is cited through its new definition-level node.

## Returned-delivery repairs

1. Removed the direct `lem-sf-reduction-flat-model` statement dependency from the
   item and added the new map definition node in `sec-trace-formula`.
2. Removed the copied `frobeniusOrdinaryReductionPullback` and
   `frobeniusFiniteReductionPullback` unique-existence statements and all ordinary
   counit helper copies. The remaining finite comparison is the exact specialization
   of `proEtaleReductionPullbackIso`, using the naturality equation for constant
   inverse-image maps, with the orientation reversed to match the item.
3. Added `def-weil-pbc-four-corners` to `stmt_deps` and compiled both the new map
   module and the repaired coherence module through `scompile.py`.

## Author check

Author self-check, with the node, blueprint proof clause (2), and delivered module open;
the maintainer supplies the independent review of this direct delivery. I checked the
hypotheses and every clause against the correspondence above. In particular the integral
ring is completed, the quotient keeps its finite scalar action, the nonflat quotient is
derived, all positive levels and powers occur, and kappa is the dependency’s normalized
comparison. The naturality and both composition squares are explicit rather than left in
prose. I retained separatedness explicitly, although the canonical helper constructions
apply more generally. Compiler-driven changes concern universe annotations and the
selection of coefficient-sized site instances, not mathematical restrictions.

## Verification

scompile.py Q19 lem-trf-frobenius-coefficient-reduction-coherence compiled the final
module both as its isolated sandbox module (13.9 seconds) and at its published module
name (14.9 seconds), with no errors or warnings and the default limits. All theorem
proofs remain sorry. The final files keep imported instances unchanged and use explicit site/coefficient
universes. The item signature was compared verbatim with the final file; its node changes
are the repaired lean record and additions of the two definition-level dependencies.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (maintainer review of 9733ae76e951)

- The base records prop-trf-scheme-galois-comparison as
  `WeilConjectures.FiniteFieldDatum.canonicalSchemeGaloisComparison`
  (Sheaf.SixFunctors.SelectedSchemeGaloisComparison). The local re-selection
  `frobeniusCoherenceKappa` from `schemeGaloisComparison` duplicated it (H4); it is removed
  and `frobeniusSchemeGalois_reduction` uses the recorded declaration at A_(b+1) and A_(a+1),
  with the annihilator `frobeniusCoherenceAnnihilator`. The import is now
  Sheaf.SixFunctors.SelectedSchemeGaloisComparison (it re-exports SchemeGaloisComparison).
- `frobeniusReductionRingMap` now states its type
  `proEtaleConstantRing X A_(b+1) ⟶ proEtaleConstantRing X A_(a+1)`; the body is unchanged.
- def-trf-integral-pullback-composition-family: its statement now says what its Lean record
  is (the type of composition families, not the normalized family) and cites the definition
  nodes of the integral constructible category and integral pullback in stmt_deps.
- Both modules compile per file with nt_compile.py, no errors or warnings.

