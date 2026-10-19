## What changed

Proved `AlgebraicGeometry.ProEtale.shortExact_sectionsWithSupport` in
`Sheaf.AlgebraicGeometry.PurSupportExact`, with its signature and the construction
`supportedSectionsComplex` unchanged. The private proved helper
`restriction_surjective` implements the blueprint's free-module monomorphism and
injective extension argument. The source library's canonical restriction adjunction
identifies its unit directly with restriction; uniqueness of left adjoints carries
epicity to the specified unit. The existing invertible supported-closed comparison
constructs the first chain map. Evaluation of the kernel and the degreewise criterion
prove short exactness, including both required canonical-map equations.

Only proof imports changed. Updated the existing node's proof, proof dependencies,
and proof origin to follow this implementation. Removed its three obsolete direct
tool approvals; the closed-essential-image result remains a transitive dependency
of the existing supported-closed comparison. No statement or definition changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.shortExact_sectionsWithSupport`
(node `lem-pur-support-exact`). Added 0 holes, split off 0 statements, and left 0
holes in the delivered module. The private helper is fully proved. This is a proof
from existing declarations, including the existing supported-comparison theorem;
it does not assert that those dependencies are all sorry-free.

Edge cases: the free-basis injection needs no nontriviality of R; empty represented
Hom sets cause no exception. If U=X, the supported kernel is zero; if U is empty,
the unit has zero target. A complex concentrated in a single degree uses the same
argument. Quasi-compactness is used exactly for the closed-comparison isomorphism.

## No longer needed

Removed these seven direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation`

The proof no longer directly uses these declared proof dependencies:

- `lem-weil-proetale-weakly-etale-localization`: the source restriction adjunction
  already computes the unit on the actual pro-etale category.
- `lem-pur-proetale-open-unit-evaluation`,
  `prop-weil-pbc-proetale-constant-ring-map`, and
  `def-weil-proetale-inverse-image`: the item is stated using ModuleCat-valued
  sheaves; their direct restriction adjunction avoids transport through intrinsic
  module sheaves and coefficient identifications.
- `def-weil-presheaf-modules-sheafification`,
  `lem-weil-pbc-ringed-site-module-sheafification-exact`, and
  `def-weil-sheaf-of-modules-category`: ordinary ModuleCat-valued sheafification
  and its existing finite-limit preservation supply the needed construction.
- `lem-weil-pbc-free-yoneda-presheaf-module`: use the already-proved source
  `freeModuleYonedaHom` and its generator identity, and calculate the restriction
  compatibility explicitly in the private helper.
- `lem-exc-proetale-closed-essential-image`: its needed consequence is already
  stated by `finiteSupportedClosedComparison_isIso`, which the proof uses.

These are removals of direct dependencies; some modules remain transitively
imported by the unchanged public interface. No unit statement or realized proof
step was bypassed: the free-module, injective-lifting, kernel, and degreewise
arguments are all retained. Added the existing
`def-sfb-finite-extension-by-zero-adjunction` dependency only for its proved
restriction-computation clause and canonical adjunction comparison, not for an
alternative extension-by-zero proof of the item.

## Where the brief, the DAG or earlier work was wrong

The plan's coefficient-comparison and intrinsic-module evaluation interface is
unnecessary for this ModuleCat-valued statement. The source already has the exact
restriction adjunction on these sheaves, including its unit formula definitionally.
No mathematical error in the item statement was found. There are no new nodes,
interface repairs or consumer adaptations.

The original namespace openings and all public imports are preserved; the proof uses
qualified `Opposite.op` names. No interface change record or consumer adaptation is needed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
