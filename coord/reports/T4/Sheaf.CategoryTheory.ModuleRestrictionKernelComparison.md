## What changed

Completed all proofs in `Sheaf.CategoryTheory.ModuleRestrictionKernelComparison`.
The actual kernel functors, canonical comparisons, and every existing public statement remain
unchanged. Added proved private helpers for finite-limit preservation, restriction surjectivity,
forgotten injective acyclicity, acyclic-complex comparison, and derived-unit normalization.
No definition, public interface, or target statement was repaired or weakened.
The scoped proof commands are documented in
`coord/changes/T4-module-restriction-kernel-proof-context.md`, as required by the
conservative preflight interface check. Every downstream module keeps its public interface;
no consumer adaptation is needed.

The shorter route uses the existing source-library classical derived exact sequence to prove
kernel acyclicity, and Leray acyclicity to prove all three quasi-isomorphisms. It proves the
representative equations explicitly from the defining base-change unit equation, including the
specified direction of the factor isomorphisms and the supplied equation for q.
The item's DAG proof and proof dependencies now describe this route.

## Proved and sorry left

Closed seven original holes, all in namespace `CategoryTheory.ModuleRestrictionKernel`:

- `sAdditiveProof`
- `s₀AdditiveProof`
- `sLeftExact`
- `s₀LeftExact`
- `kernelIdentity_naturality`
- `moduleEnoughInjectivesProof`
- `moduleRestrictionKernelComparison`

Holes added: zero. Holes remaining in the delivered module: zero. No result was split off.
All private helpers are proved. The last theorem includes surjectivity, positive-degree kernel
acyclicity, invertibility, degree-zero normalization, short exact rows and their morphism,
all three quasi-isomorphisms, and both kinds of representative normalization.

## No longer needed

Removed these original direct proof imports:

- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`: the stronger localized-generator
  theorem (`lem-pur-ringed-site-grothendieck-abelian`) is unnecessary; the existing small-site
  `SheafOfModules.isGrothendieckAbelian` suffices.
- `Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction`: its commutative-sheaf/precoverage
  interface does not directly accept the actual constant RingCat sheaf. The short free-Yoneda
  proof works directly in that category. Its node `lem-pur-ringed-site-injective-mono-restriction`
  is no longer a declared dependency of this item.
- `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`: its node
  `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` is unnecessary. The already
  proved arbitrary-site module-injective acyclicity theorem supplies the needed fact directly.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: redundant direct import;
  the public evaluation interface already imports it and installs exactness of forgetting.
  The mathematical dependency remains.
- `Sheaf.CategoryTheory.RingedSiteModules`: its wrapper is unused; the actual Modules category
  comes from the public constant-module interface. Its definition node remains a statement
  dependency, and the category remains Mathlib's SheafOfModules.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: no precoverage conversion is needed. The item keeps
  its arbitrary Grothendieck topology. The sites definition remains a statement dependency.

Also removed trial direct Mathlib imports of `ModuleCat.Presheaf.Limits`,
`ModuleCat.Sheaf.Limits`, and `ModuleCat.Presheaf.Generator`; the required APIs are publicly
available through the source Grothendieck theorem import.

The former direct proof dependencies `lem-weil-pbc-dplus-injective-representative` and
`lem-weil-pbc-kinjective-hom-derived` are unnecessary: the theorem quantifies over supplied
representatives and q, and the generic base-change theorem handles invertibility.
`lem-weil-pbc-complex-ses-homology-long-exact`,
`lem-weil-pbc-complex-ses-long-exact-naturality`, and `lem-weil-pbc-five-lemma` are replaced by
the existing classical derived-sequence and acyclic-complex APIs. This is pruning of this
item's direct argument; it does not assert those facts are absent from the APIs' own proofs.
The two obsolete top-level tool-use approvals for the localized-generator and general
module/abelian evaluation-comparison nodes were removed. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan's precoverage/CommRingCat restriction theorem requires conversion of the
actual constant RingCat sheaf. Its free-Yoneda argument applies directly, without that extra
interface work. Likewise the stronger localized-generator result is not needed just to obtain
enough injectives. These are shorter routes, not defects in the mathematical statement.

The original explicit five-lemma ladder is unnecessary after kernel acyclicity: the existing
Leray acyclicity theorem gives the kernel and evaluation quasi-isomorphisms uniformly.
No injectivity of a forgotten module sheaf or flatness over the integers is used.
Edge cases retain the actual kernels: m = identity gives zero kernels, the zero ring gives zero
module objects, and nonflat coefficients do not affect the acyclicity argument.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
