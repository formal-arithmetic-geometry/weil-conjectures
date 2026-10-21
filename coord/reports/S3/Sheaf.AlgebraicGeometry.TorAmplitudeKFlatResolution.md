## What changed

Repair retry of C-32078 after the two interrupted delivery attempts: reapplied the reviewed proof to the current source after the upstream sync. Rechecked against the current sheaf-dag source on 2026-10-22: the main theorem signature, node statement, statement dependencies, and refreshed lean_audit are preserved verbatim. The retained packet incorporates the current source rather than reverting the upstream sync. Preserved the current theorem signature and refreshed node audit/review metadata. The current filtered-colimit import is WeilConjectures.Algebra.Homology.FilteredColimitsTensor; the construction does not use it. All four packet modules and the two current downstream modules compiled through server-only lcompile.py. The unchanged downstream sources were checked as temporary sandbox copies and are not delivered. This retry re-read the current return and rework records, recopied the theorem signature verbatim from the current shared source, and refreshed every non-worker-owned node field from the current node. A fresh server-only lcompile.py --all check passed for all four packet modules (cached compiled results).

Proved the scalar-restriction additive instance and assembled the Tor-amplitude characterization from the existing flat K-flat resolution, tensor-cokernel flatness, and universal ringed-topos pullback declarations. Added a constructed scalar-restriction equivalence, its derived tensor comparison, and the lower good truncation K-flatness theorem. The lower-truncation argument proves pure tensor exactness by an abelian diagram chase, uses a bounded-above flat kernel, and totalizes a short exact sequence using exact coproducts.

Moved the existing scalar interface to TorModelRestriction, publicly re-exported by the item. The coefficient object retains its exact value; its abbreviation becomes a semireducible definition to avoid expanding constant-ring sheafification during elaboration. Change record: coord/changes/tor-model-restriction-interface.md. No consumer requires a source adaptation.

## Proved and sorry left

Closed both original holes: AlgebraicGeometry.Etale.torModelRestriction_additive and AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE_iff_exists_kFlat_flat_model. Holes closed: 2 of 2; holes added: 0; holes remaining in the four delivered modules: 0. The new restriction, tensor-comparison, and lower-truncation declarations are also proved. All four modules compiled again through lcompile.py on 2026-10-22: lower truncation 12.0 seconds, restriction 8.3 seconds, tensor comparison 41.1 seconds, and the item 19.3 seconds. A second run with LCOMPILE_NO_LOCAL=1 passed for all four modules and both unchanged consumers on the project server. Server-only checks also passed for the unchanged consumers PunctualTensorBaseChange (18.3 seconds) and PrimeTorsionCoefficientReduction (38.0 seconds). The main theorem's original signature is unchanged. Existing unproved dependency declarations are used as intended by stage 3.

## No longer needed

Removed direct imports Sheaf.CategoryTheory.TruncationsAndHomotopyColimits, Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES, Sheaf.Paper.EtaleKFlatCriteria, and WeilConjectures.Algebra.Homology.FilteredColimitsTensor. Mathlib good truncation replaces def-kun-truncations. The independent bounded-above flat criterion and the explicit kernel/totalization proof replace lem-kun-kflat-criteria, lem-weil-pbc-site-flat-quotient-tensor-ses, and lem-pc-module-filtered-colimits-tensor. The latter two tool_uses approvals are removed. The long exact homology sequence remains needed by the new lower-truncation node, so lem-weil-pbc-complex-ses-homology-long-exact is moved there rather than pruned globally. The current DAG additionally cites lem-kun-lower-truncation-flat-model (Sheaf.Paper.EtaleLowerTruncationFlatModel) and lem-kun-kflat-short-exact-quotient (Sheaf.Algebra.Homology.KFlatShortExactQuotient). This proof does not import either: Mathlib supplies the truncation quasi-isomorphism and term identifications, and the delivered independent-universe lower-truncation theorem proves the flat kernel and exact total tensor argument directly. Those existing modules and declarations are preserved; only this node's proof edges are replaced. The original public imports are re-exported through TorModelRestriction. No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The coefficient encodings in the recorded derived category and ringed-site K-flat predicate require an explicit tensor-compatible equivalence; additivity alone does not identify their derived tensors. The packet supplies that comparison using the existing constant-module realization and its tensor comparison. Ordinary good truncation alone also does not prove K-flatness: the bounded-above flat kernel and exact total-tensor sequence are supplied explicitly. The assigned statement and its universal pullback quantifiers are unchanged.

## New nodes

lem-kun-tor-model-restriction: canonical scalar restriction, its explicit realization-restriction identity, and equivalence. It also attaches the moved scalar definitions and proved additive instance.

lem-kun-tor-model-tensor-comparison: localization of the total tensor with a degree-zero sheaf computes the fixed etale derived tensor through canonical scalar restriction. The generic equivalence arguments are private proved helpers in the same module.

lem-kun-kflat-lower-truncation: a lower good truncation of a flat-term K-flat complex remains K-flat when its boundary opcycles are flat. It is valid at independent site and coefficient universes and uses the existing bounded-above flat criterion.

Change record: coord/changes/tor-model-restriction-interface.md.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
