## What changed

Replaced the sole sorry of `CategoryTheory.ringedSitePerfectDuality` with a complete
representative-level argument. It uses the fixed outer K-injective replacement of
Hom(K,I(O[0])), transports canonical biduality and evaluation along P ≅ QK, and proves
invertibility componentwise. All existing signatures and public imports are unchanged.

Proved the local perfectness of that representative. The ordinary dual has bounds
[-b,-a]; its degree n is canonically Hom(E^(-n),O), so dualizing each specified
finite-free splitting supplies its termwise package. The comparison to the restricted
fixed global representative uses exact-source Hom, the canonical derived restriction
comparison, and K-injective lifting through the exact extension-by-zero adjunction.

Proved independent-universe versions of the existing single-degree, stupid-tail and
bounded exact-source Hom arguments. Proved internal-Hom exactness for a finite-free
retract directly: evaluation at 1, the finite biproduct comparison, exactness of finite
sums, and retract stability of homology, monomorphisms and epimorphisms. No existing
helper statement or definition was modified.

Canonical biduality is proved from evaluation by a generic closed-category argument.
The covering-slice evaluation theorem is now proved as well: exact restriction commutes
with homology, the cover criterion detects quasi-isomorphisms, and right fractions
extend this detection to arbitrary derived morphisms. The strict-source derived theorem is also proved, including finite-term dualizability,
K-flatness, Hom augmentation comparison, canonical normalization and transport in the
arbitrary derived target. Only the separate ordinary finite diagonal evaluation
calculation remains open.

## Proved and sorry left

Decomposition: 1 original hole closed, 1 added, net 0. The original declaration
`CategoryTheory.ringedSitePerfectDuality` (lem-sfb-ringed-site-perfect-duality) has no
sorry. The only added hole is the entire public theorem
`CategoryTheory.ringedSiteOrdinaryEvaluation_isIso`
(lem-sfb-ordinary-perfect-evaluation). This is the bounded finite-projective source
calculation in the final paragraph of Stacks 08JJ. It still needs the ordinary finite
diagonal tensor evaluation calculation, uniformly
for arbitrary unbounded evaluation complexes. The derived normalization, Hom
augmentation comparison, K-flatness, and target transport are all proved in
`CategoryTheory.ringedSiteStrictPerfectEvaluation`. Cover-local detection and transport
are
proved in `CategoryTheory.ringedSitePerfectEvaluation_model`.

The following new public theorems are completely proved, without sorry:

- `CategoryTheory.ringedSitePerfectDual_localModel`
- `CategoryTheory.ringedSitePerfect_ordinaryDual`
- `CategoryTheory.ringedSitePerfectDual_localComparison`
- `CategoryTheory.ringedSitePerfect_termHomExact`
- `CategoryTheory.quasiIso_homComplex_map_of_single_degree_exact_termOfUniverses`
- `CategoryTheory.exists_homComplex_stupid_tail_shortExactOfUniverses`
- `CategoryTheory.quasiIso_homComplex_map_of_bounded_exact_termsOfUniverses`
- `CategoryTheory.ringedSitePerfectBidual_model`
- `CategoryTheory.ringedSitePerfectEvaluation_model`
- `CategoryTheory.ringedSiteStrictPerfectEvaluation`

All private helpers are proved. The bidual argument constructs coevaluation from inverse
evaluation, verifies both pairing triangles, and identifies each Yoneda map of the
specified bidual with a composite of Hom-set equivalences. Empty intervals, rank zero,
odd degrees, characteristic two, and independent site universes are retained. The
remaining theorem treats a globally bounded finite-projective complex; the original
local source, covering descent, dual-perfectness and categorical biduality arguments
are implemented here.

All twelve final delivery modules compiled together with exit code 0, with no warnings.
The strict evaluation module compiles in 17.4 seconds, the local evaluation module in
27.5 seconds, and the item in 6.6 seconds in an uncached sandbox check. The subsequent
full check also passed after updating only the item proof docstring; server load made
that item compile take 36.1 seconds. No
file or proof is split to satisfy the compile limit: the finite-term K-flat helper
and its derived wrapper remain together in the strict evaluation module.
The delivery dry run performs its own compiler and axiom checks.

## No longer needed

The following direct proof imports were removed from the item. Their mathematical content
remains needed by the split calculations, whose nodes retain the dependencies; no module
is claimed globally pruned:

- `Sheaf.Algebra.Homology.HomComplex`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Mathlib.CategoryTheory.Sites.LocalProperties`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`

The provisional model files also had inherited imports unrelated to their own proof plans.
Removed these direct imports from `RingedSitePerfectDualLocalModel`:

- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Mathlib.CategoryTheory.Sites.LocalProperties`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`

Removed these from `RingedSitePerfectEvaluationModel`:

- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`

The bidual node no longer uses its former independent signed-complex calculation,
second ordinary-Hom comparison, or second cover-local descent argument: evaluation
already gives an exact pairing. Its proof dependencies now contain only the evaluation
model, the closed structure, and the canonical maps. Its former direct dependencies
`lem-sc-finite-free-internal-hom-exact`,
`lem-pc-bounded-exact-term-hom-quasi-iso`, `def-pur-hom-complex`, `def-pur-sheaf-hom`,
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-sfb-sheaf-cover-local-isomorphism`, `prop-pur-kinjective-resolutions-exist`,
`lem-weil-pbc-kinjective-hom-derived`, and `def-weil-abstract-derived-category`
are not used by that proof. They remain used in the proved local comparison or the
bounded evaluation calculation.
No library module is claimed globally pruned.

The parent's direct proof dependencies are now the three model nodes and its actual
representative/localization/canonical-map dependencies. Its obsolete direct tool approvals
were removed except prop-pur-kinjective-resolutions-exist. The withdrawn parent approvals are: `lem-weil-pbc-ringed-internal-hom-exact-restriction`, `lem-sc-finite-free-internal-hom-exact`, `lem-pc-bounded-exact-term-hom-quasi-iso`, `lem-pc-kflat-resolution`, `lem-pc-bounded-above-flat-kflat-site`, `lem-weil-pbc-site-derived-tensor-descent`, `lem-pur-site-restriction-module-adjunction-exact`, `lem-weil-pbc-kinjective-hom-derived`, `lem-pur-kinjective-restrict-localized`. Used tools are recorded in the new nodes; the equal-universe bounded exact-source
Hom tool is replaced by its proved independent-universe version. No unit statement
or realized unit step was bypassed; the unit's realized lists are empty.

The proved evaluation-model module additionally no longer imports these planned
calculation tools directly; the bounded calculation is isolated in its strict-source lemma:

- `Sheaf.Algebra.Homology.HomComplex`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`

For covering descent the right-fraction argument replaces the planned K-injective
representative argument. Thus the evaluation-model node no longer directly needs
`prop-pur-kinjective-resolutions-exist` or `lem-weil-pbc-kinjective-hom-derived`.
The local dual comparison still uses those results. No module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

Several planned helper signatures use fewer independent universes than the item.
The equal-universe exact-source Hom lemmas could not simply be applied at arbitrary
c,v,r. This delivery generalizes their actual proofs, rather than specializing the
item or adding an unproved replacement. Finite-free internal-Hom exactness is likewise
proved at independent universes. The localized-system extension/restriction adjunction
supplies the independent-universe preservation of K-injectives needed here.

The literal local-model definition requires actual quasi-isomorphisms into the chosen
representative. The Hom representative itself need not be K-injective; taking its
fixed outer K-injective replacement makes the derived comparison lift to such maps.
The bounded flatness/K-flat interfaces are now used successfully with the
independent universes, after explicitly supplying finite biproducts and the
Grothendieck abelian instance. The ordinary finite diagonal evaluation still needs
its independent-universe component calculation. No arbitrary witness from mere existence is
used as definition data. Intermittent
compile-server no-response results were checked before retrying.

On resumption the reference-clock metadata changed externally: the earlier observed
`.budget.start` was 1792425598.8371773; this continuation observed 1792432283.952846.
The retained earlier dry run reported 22 minutes, while the continuation dry run
`scratch/dry-run-current.log` reported 9 minutes. No budget metadata was edited.
Useful proof work continued; this records the reset for the launcher owner.

## New nodes

`lem-sfb-perfect-dual-local-model` proves local perfectness of the fixed outer dual
representative by combining the next two results on each member of the original cover.

`lem-sfb-perfect-ordinary-dual` proves the reflected bounds and finite-free-retract
package of the explicitly constructed ordinary dual. Source: Stacks 08JJ.

`lem-sfb-perfect-dual-local-comparison` proves the actual quasi-isomorphism from that
ordinary dual into the restricted global fixed representative. Source: Stacks 08JJ,
08JB, 08FI and 070I. It asserts neither boundedness nor the termwise package.

`lem-sfb-perfect-term-hom-exact` proves exactness of internal Hom from a finite-free
retract at independent universes, as required by the bounded comparison.

`lem-pc-universes-single-degree-exact-term-hom-quasi-iso` generalizes the existing
single-degree exact-source Hom proof to independent site and coefficient universes.

`lem-pc-universes-stupid-tail-hom-short-exact` generalizes the degreewise-split stupid
truncation Hom short exact sequence; all its maps and exactness proofs are explicit.

`lem-pc-universes-bounded-exact-term-hom-quasi-iso` combines those two lemmas by bounded
stupid truncation induction, using the existing proof's naturality and five-lemma route.

`lem-sfb-perfect-bidual-model` proves canonical bidual invertibility from evaluation.
The separate signed local bidual calculation is unnecessary.

`lem-sfb-perfect-evaluation-model` now proves restriction transport and cover-local
invertibility detection, using exact homology comparisons and derived right fractions.
Its statement and all existing consumer signatures are unchanged.

`lem-sfb-strict-perfect-evaluation` is proved from the ordinary calculation and the
existing representative normalization. It supplies a real derivation through
K-flatness of the dual, exact-source Hom comparisons, a K-flat target replacement,
and naturality in the target. Its finite-term K-flatness helper is proved privately.

`lem-sfb-ordinary-perfect-evaluation` is the only open new node. It states just the
ordinary finite diagonal tensor/Hom calculation from Stacks 08JJ, with no derived
closed structure, restriction, coverings, dual-perfectness, or bidual conclusion.
Its docstring and node give the dual-basis/retract proof, including empty supports,
zero ranks, zero rings and arbitrary unbounded target complexes. It is strictly
part of the original argument. No existing definition, statement or consumer
changed; no definition/statement change record is required.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
