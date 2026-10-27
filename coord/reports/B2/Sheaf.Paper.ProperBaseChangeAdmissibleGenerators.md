## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.properBaseChange_admissible_generators`
in its existing module, with its signature unchanged. The proved support module
`Sheaf.Paper.CondensedCoefficientIsoExchange` supplies
`AlgebraicGeometry.ProEtale.CondensedRing.condensedAmbientExchange_coefficientIso`.
It transfers the actual ambient exchange through a coefficient ring isomorphism
using the normalized scalar/geometric rectangle. Its scalar equivalence,
constructibility and normalization steps are factored into private lemmas to avoid
repeated expansion of derived and tensor structures. These optimizations made all
kernel checks pass; the final delivery probe still took 64.4 seconds in one file,
so the self-contained, fully proved transport argument has its own module. The helper
`rational_exchange` identifies the existing bounded rational exchange with the exact
ambient mate in the goal. The finite and integral cases use their existing theorem
clauses. Existing coefficient-presentation helpers handle universe lifting and the
degree-one Z_ell and Q_ell cases. Private interfaces use unbundled complexes and
explicit predicate conversions to avoid expanding full-subcategory structures during
kernel checking. The finite case reuses the source theorem's named coefficient
instances. The scalar proof's tensor caches are scoped to that proof. The final case
analysis uses a proved private structure with the raw exchange as its field. All added
imports are proof imports.

Updated the item's docstring and DAG proof to match this argument and the current
admissibility predicate. No other existing module or node is changed.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtale.CondensedRing.properBaseChange_admissible_generators`
(node `lem-sfb-proper-base-change-admissible-generators`).

Added 0 holes; split off 0 unproved obligations. The new coefficient-isomorphism
helper is fully proved. No sorry remains in either delivered module.
The imported stated dependencies retain their own proof obligations where applicable.

## No longer needed

No original public import is removed and no module is withdrawn.
The current admissibility predicate excludes the full continuous-map algebraic closure.
Consequently this proof does not use the old planned dependencies
`det-sf-comp-continuous-algcl-local-free` (Sheaf.Paper.ContinuousAlgClLocalFree),
`lem-real-compact-matrix-coefficient-descent`, or
`det-sf-comp-continuous-algcl-heart-finiteness`
(Sheaf.Paper.ContinuousAlgClProperHeartFiniteness). They are removed from this node's
proof dependency list; the adopted source declaration of compact-matrix descent is
preserved.

The combined rational module Sheaf.Paper.ProperBaseChangeRational and direct dependency
`det-thm-sfb-proper-base-change-rational` are unnecessary here: the existing upstream
bounded proper-base-change natural transformations supply precisely the needed clause.
The original direct dependency `lem-weil-pbc-coefficient-exchange-mates` is replaced
by the already proved normalized scalar/geometric rectangle and comparison helpers.
It remains available to the imported finite-coefficient proof; this is not a claim
that its module is globally unused. No claim of target-closure module withdrawal is made.

## Where the brief, the DAG or earlier work was wrong

The old docstring and proof step 2 included the full continuous-map algebraic closure,
but the current LocalizingAdmissibleCoefficients explicitly excludes it. The actual
statement already refers to that predicate and needs no signature repair.

The rational planned theorem uses ordinary bounded constructibility and bundled
Over schemes, whereas this item uses finite constant scalar models and a chosen
Cartesian source with no specified k-structure. The proof supplies the constructibility
comparison and derives the missing source structure and finiteness from properness,
rather than adding hypotheses. The finite and integral presentation mismatches are
resolved by existing coefficient-isomorphism helpers.

## New nodes

`lem-sfb-condensed-coefficient-iso-exchange` records the fully proved, general
coefficient-transport step in `Sheaf.Paper.CondensedCoefficientIsoExchange`. It
requires neither properness nor coefficient admissibility and reduces transport
to the existing constructibility and normalized-mate rectangle results. The item
uses it as a proof import. This is a proved helper, not a new proof obligation.
No change record is needed: only the assigned existing module and its own node,
and this new support module and node, are changed.

## Related modules compiled before delivery

41 related module(s) compiled against this delivery by deliver3.py: 38 OK, 3 SLOW.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.CondensedCoefficientIsoExchange": "056647188024c675c9b7443080a1277a7c183f66", "Sheaf.Paper.ProperBaseChangeAdmissibleGenerators": "84b1159cbcd3b9fdaf9c7ece6514a59fc5288e1e"}, "results": {"Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded": {"hash": "d2fc5b1116689ece42eba428627c270ff7c0dfeb", "status": "OK"}, "Sheaf.Paper.CondensedCompositorRealizationData": {"hash": "a0c7b3b8f4c75aba5a0683ba8ad1d550af600aee", "status": "OK"}, "Sheaf.Paper.CondensedCompositorRealizationSquare": {"hash": "e3186c1b28171ea2655f06c3eb4fb103ac186cb7", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitComparisons": {"hash": "d15a0f84ad12ce316c6c1d36de6f3af07d8f56d8", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitRealizationSupport": {"hash": "111fd16030a7b4501af4c65bee2afe0e37d3ee76", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitUnits": {"hash": "f6992093322faef0c8d2cc2c308093e13e78eae6", "status": "OK"}, "Sheaf.Paper.DetThmSfCtfStabilityInternalHom": {"hash": "f73d937b2756c373eab636c8603d0ad7c5e7ff0e", "status": "OK"}, "Sheaf.Paper.IntegralLocalizingProperBaseChange": {"hash": "cedadcc703c7a6e378a60fb85ececdd2131d7280", "status": "OK"}, "Sheaf.Paper.IntegralOpenImageProperFormulas": {"hash": "8657bfbd9f9cc15e6b0a7031f8e52b76c53d176e", "status": "OK"}, "Sheaf.Paper.PodCtfAdjunctions": {"hash": "a89f60a7fa14c7ba491ce0c5d863cf58621aa87d", "status": "OK"}, "Sheaf.Paper.RationalAffineTensorCalculus": {"hash": "d011e06c3809ad598674b2ea10c06d16b07c32e6", "status": "OK"}, "Sheaf.Paper.RationalP1LocalizingPreservation": {"hash": "db20b041128438a221f469857c6ecf4d4f16d5bd", "status": "OK"}, "Sheaf.Paper.RationalP1Triangle": {"hash": "d1e2d798a7453c8ae09756e0efc410fa7b065150", "status": "OK"}, "Sheaf.Paper.RationalP1UnitCounit": {"hash": "70aaae1b8af1c46a532c35488aeb106cd872de43", "status": "OK"}, "Sheaf.PoincareDuality.ConstructibleSheafBiduality": {"hash": "426a09c60ff3e13f195891f717442eba5f3ac382", "status": "OK"}, "Sheaf.SixFunctors.CtfStabilityDirectImages": {"hash": "5dbcae17fe4067cf95ad64f9fe0c3ebd39b6eeec", "status": "OK"}, "Sheaf.SixFunctors.DetSfCompCompositionBaseChange": {"hash": "fc62f18c40fac2b827b60e8c0c2050614e50d192", "status": "OK"}, "Sheaf.SixFunctors.IntegralAffinePurityInduction": {"hash": "12925cc3097778defc1b951a00be8a14c37b704c", "status": "SLOW"}, "Sheaf.SixFunctors.IntegralKernelContractions": {"hash": "17bfbffcc2e994d2ad929ba87230637d47e5d5ce", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelFirstAmbientFormula": {"hash": "456d1456e7fda7321c8f7c050ee258c1c19647f9", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelFirstContraction": {"hash": "6df44a0fdfe6464a389e88905bace36b87ee6be8", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelFirstTransport": {"hash": "56a3d2f1272a1525fa724b523bcf8d796f55a1cf", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelSecondContraction": {"hash": "9afd502e3a7846b31488050e250cb3ae0856489f", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelSecondContractionPostcomp": {"hash": "18abbf37005c1fef052a625cc00bff358256e38b", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelTateComparison": {"hash": "c4081fb57e247257434cc179cb57f9c0983e7d4f", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelUnitCounit": {"hash": "b95742fb5c4fe10c4cddfc0f863b93043b12acba", "status": "OK"}, "Sheaf.SixFunctors.IntegralProjectiveLineAdjunction": {"hash": "7d38ace701be07f1d9b47cda8a5ab57b3fe125a5", "status": "OK"}, "Sheaf.SixFunctors.IntegralRestrictionLine": {"hash": "5b9663b68e18383f6e0596b71b5c72d13e52f7e1", "status": "OK"}, "Sheaf.SixFunctors.IntegralTateLineConstructible": {"hash": "2b4871f78eaf55fdd14d4d4ffc43554b4a9ed4f2", "status": "OK"}, "Sheaf.SmoothPurity.OpenDimensionObstruction": {"hash": "c86784ccdd356b78502c055c8a230a48dc22cb72", "status": "OK"}, "Sheaf.SmoothPurity.TraceExistence": {"hash": "8254b2cf476dd6d0b90a82ae7bf52e95b429a1c1", "status": "OK"}, "Sheaf.Targets.AffineSpaceRationalLine": {"hash": "da9fc3ba6bf52ed9ce679b2e0e04d8214173ecf0", "status": "SLOW"}, "WeilConjectures": {"hash": "9d8fc9f1ee8988b99c0925efedd56ce1f42e0f81", "status": "OK"}, "WeilConjectures.PoincareDuality.Verdier": {"hash": "29b344f3846fb46b6f3d8752273487590bf52f59", "status": "OK"}, "WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence": {"hash": "a2437880f64dd09a7ac2d667fc49ec1195ae2891", "status": "OK"}, "WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek": {"hash": "836f4dc6f6a12beb37db6d09436d277f4d978e79", "status": "OK"}, "WeilConjectures.TraceFormula.Additivity": {"hash": "0d3c569a39f4043b0ace381ae0b435cbf2e53afc", "status": "SLOW"}, "WeilConjectures.TraceFormula.Basic": {"hash": "267f034ddffbd1e108a1e77a74f4e97df618ea80", "status": "OK"}, "WeilConjectures.TraceFormula.CompactCohomology": {"hash": "c0a15d41674171dd9cfb5a618e12d0330892e3aa", "status": "OK"}, "WeilConjectures.TraceFormula.CompactCohomologyFibres": {"hash": "0bd743ee04a439178b9b9c21780441a4a85940ae", "status": "OK"}, "WeilConjectures.TraceFormula.Stalk": {"hash": "8f5de351c2cf7f3c9401402393fd4506a7e12de1", "status": "OK"}}, "seconds": 301, "time": "2026-10-28T06:38:32+0800", "transitive": 38, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
