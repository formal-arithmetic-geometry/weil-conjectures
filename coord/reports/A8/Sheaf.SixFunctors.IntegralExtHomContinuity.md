## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralExtHomContinuous` using
existing integral locally finitely presented Hom continuity, the compatible locally
closed costalk calculation, finite sheaf extension towers and bounded truncation
devissage. The theorem text, universes, canonical comparison and public imports are
preserved. No definition, existing signature or other module is changed. The added zero-object
notation scope and declaration-local elaboration context are documented in
`coord/changes/A8-integral-ext-hom-proof-context.md`.

The norm on E is induced from its given embedding into the algebraic closure.
An explicit normalization of `integralCoeff` before applying the dependent theorem
avoids expanding the entire sheaf/module structure during coefficient comparison.
The original complete candidate exceeded the compile limit; the normalized complete
proof compiled in 15.3 seconds. The resumed complete proof compiled in 8.4 seconds. Delivery preflight checks the final packet.
All compilation uses lcompile.py or the checks invoked by deliver3.py.

Updated the existing DAG node's proof, proof dependencies and proof origin to match
the Lean argument; removed obsolete top-level tool-use entries. The unit record is
unchanged. The costalk calculation retains the prescribed closed-support fibre route,
and the length-one resolution computes the integral finite-amplitude dual argument.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.ProEtale.CondensedRing.integralExtHomContinuous`
(node `det-lem-int-ext-continuity`). Added 0 holes. No `sorry` remains in the delivered
Lean module. No new theorem is split off. This is a proof from existing declarations,
not a decomposition or relocation of a hole. Existing dependencies retain their
own proof status; no claim is made to have proved the whole import closure here.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`
- `Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections`
- `Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Sheaf.CategoryTheory.SheafTensor`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.FormalClosedSupportDerived`
- `Sheaf.Paper.IntegralStratumHomFormula`
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FreeSheafFlat`
- `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `Sheaf.Paper.IntegralHeartDualizable`

The following old direct proof dependencies are no longer needed at this node:

- `def-pur-ringed-site-zeroth-hypercohomology`
- `def-sbc-standard-tstructure-derived-category`
- `def-sfb-modobj-internal-hom`
- `def-sfb-modobj-symmetric-tensor`
- `def-sfb-module-upper-lower-adjunction`
- `det-lem-bounded-continuity-direct-image`
- `det-lem-formal-closed-support-derived`
- `det-lem-int-ext-formula`
- `det-lem-int-integral-heart-dualizable`
- `det-pe-bounded-continuity-sections`
- `lem-pc-right-derived-functor-triangulated`
- `lem-sc-source-kflat-tensor-left-triangulated`
- `lem-sc-source-tor-amplitude-flat-model`
- `lem-sf-derived-homology-long-exact`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-sfb-modobj-flat-resolutions`
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`
- `lem-weil-pbc-five-lemma`
- `lem-weil-pbc-free-sheaf-flat`
- `lem-weil-pbc-kinjective-functorial-existence`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `sk-def-sfb-derived-tensor-hom`
- `sk-def-sfb-sheaf-tensor`
- `sk-prop-sfb-cartesian-coefficients`
- `thm-sp-truncation-e2`

The finite extension tower replaces the separate integral-stratum filtration theorem.
The local costalk model encapsulates the closed-support/direct-image comparison, so
no internal derived dual, bounded flat model, K-injective resolution or five-lemma
ladder is constructed again in this module. Generic bounded truncation devissage
handles the bounded constructible complex after the sheaf case. Some of the removed
direct imports remain transitive dependencies of these existing tools; these are
route-specific pruning claims, not claims that every such module leaves the targets.
All three original public imports are retained. Each added proof import supplies a
lemma actually used: integral local continuity, extension towers, the general local
piece helper, constant-model finite presentation, constant-model isomorphism/zero
closure, or the general bounded devissage theorem.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had a complete proof candidate but no report, node update or
successful delivery. Its direct application of integral_lfp_hom_continuity forced
an expensive definitional coefficient comparison. Normalizing the scalar abbreviation
first fixes that without changing any shared definition or increasing the file limit.
The earlier initial dry run reported a missing report. A later dry run requested
a change record for the added zero-object scope; this is documented in
`coord/changes/A8-integral-ext-hom-proof-context.md`. No public signature changes.

The existing local-piece module's public theorem specializes to field coefficients,
but its proved private locally_closed_generators_continuity helper is general in the
coefficient ring. Importing that proof context with `import all` allows the integral
local continuity theorem to supply the required hypothesis. No field-only theorem is
applied to integral coefficients. Constant-model constructibility is transported to
local finite presentation; it is never replaced by local finite freeness.

The bounded object is reduced through its actual cohomology sheaves, finite extension
towers and the same closed-costalk cocone. Zero coefficients, empty schemes and zero
complexes are covered by the zero-model and existing tower arguments. The comparison
is always the canonical map from the original termwise colimit cocone.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
