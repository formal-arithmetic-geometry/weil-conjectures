## What changed

Completed the retained finite-free approximation proof of
`AlgebraicGeometry.Etale.isIso_finiteConstantProjectionMap`, without changing its statement
or the canonical map definition. Three supporting modules prove the bounded finite free
case, finite free approximation triangles, and degreewise comparison. The finite free case
uses existing dualizability theorems. The main proof supplies the common upper amplitude
bound and assembles the approximation argument.

The main module has a private, proved tensor upper-bound helper stated for a general
coefficient category. This avoids the expensive comparison between concrete module-sheaf
monoidal instances described by the source library's TensorStructure module. Arithmetic
rewrites touch only the degree bounds. Obsolete instance exclusions from the retained
sandbox were removed because their generated instance name is unavailable in the current
compiled library. All four modules compile without those exclusions.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Etale.isIso_finiteConstantProjectionMap`
(node `lem-sf-projection-finite-constant`).

All three new supporting theorems are proved:

- `AlgebraicGeometry.Etale.isIso_projectionMap_bounded_finiteFree_constant`
  (`lem-sf-projection-bounded-finite-free-constant`).
- `DerivedCategory.exists_finiteFree_approximation_triangle`
  (`lem-sf-finite-free-approximation-triangle`).
- `DerivedCategory.isIso_app_of_approximations`
  (`lem-sf-projection-approximation-comparison`).

No `sorry` remains in the four delivered modules. Holes closed: one; holes added: zero;
net closure: one. Imported existing statements retain their existing proof status.
The complete sandbox compiled through lcompile.py with each file below 60 seconds; the
current-session run took 0.8 seconds each for the finite-free case and the main item;
the two other modules also passed. All four files compiled without warnings.

## No longer needed

The new finite-free helper also drops the unused copied imports
`Mathlib.Algebra.Module.FinitePresentation` and `Mathlib.RingTheory.Noetherian.Defs`;
its statement assumes neither finite presentation nor Noetherianity.

Removed direct proof imports from the item:

- `Mathlib.CategoryTheory.Sites.Sheafification`: supplied through the existing exact-functor API.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf`
  (`lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`): use the existing module-valued
  canonical constant-sheaf comparison.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` and
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
  (`prop-weil-pbc-inverse-image-modules-exact`): use the existing exact upper-star functor.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and
  `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
  (`lem-weil-pbc-module-direct-image-left-exact`): use the existing direct-image instance.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` and
  `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`: use the source library's
  derived tensor and upper-star interfaces.
- `Sheaf.Paper.ProjectionMateExact` (`lem-weil-pbc-ringed-projection-mate-exact`): use the
  source projection unit, shift compatibility and triangulated generation APIs.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: used by the proved
  comparison helper rather than directly by the item.
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four` (`lem-weil-pbc-five-lemma`): the
  existing bounded-complex generation theorem performs the finite induction.
- `Mathlib.RingTheory.Noetherian.Basic` (`lem-weil-pbc-noetherian-submodule-finite`):
  the existing pseudo-coherence criteria supply bounded finite free approximations.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
  (`lem-weil-pbc-module-sheaves-enough-injectives`): use existing Grothendieck-abelian instances.
- `Sheaf.Paper.BoundedFlatReplacement` (`lem-kun-bounded-flat-replacement`) and
  `Sheaf.Paper.EtaleKFlatCriteria` (`lem-kun-kflat-criteria`): use the already proved source
  tensor upper-bound API.
- `Sheaf.CategoryTheory.DerivedCategory.FiniteCDDerivedUpperBound`
  (`lem-sf-finite-cd-derived-upper-bound`): use the existing proved upper-amplitude theorem
  in `Sheaf.CategoryTheory.RightDerivedFunctorUpperBound`.

The source of long exact sequences and cohomological detection remains needed through
supporting modules. No global claim is made that these modules have no other consumers.
The item's obsolete top-level `tool_uses` entries are withdrawn accordingly.

## Where the brief, the DAG or earlier work was wrong

The retained report listed the finite-free theorem as a hole although its Lean proof was
present. That proof is now validated. The main proof originally compared the concrete
module-sheaf monoidal instance with the one inside derivedTensor, causing kernel timeouts.
The source library documents this behavior in TensorStructure. A general-coefficient helper
and explicit arithmetic rewrites remove those comparisons; no definition repair is needed.
The final composition needs the leading projection isomorphism supplied explicitly.

The current blueprint unit has no realized entry for this historical auxiliary lemma.
The auxiliary lemma retains its finite-free approximation route. The finite-free step uses
the proved dualizable projection theorem, which subsumes its finite-sum and truncation proof.
Stacks Tag 0944 supplies the perfect finite-free case; the resolution and approximation
comparison are from the blueprint lemma's third and fourth proof paragraphs.

## New nodes

The three new nodes have self-contained mathematical statements; their `lean.statement`
fields retain the corresponding verbatim Lean signatures.

`lem-sf-projection-bounded-finite-free-constant`: proved by dualizability of constant finite
free terms, bounded complexes, and the source library's projection formula at a dualizable
coefficient. The zero complex and zero ring are included in those library results.

`lem-sf-finite-free-approximation-triangle`: proved using the Noetherian pseudo-coherence
criterion and m-pseudo-coherent approximations, with the cohomology sequence controlling the
cone. The zero ring case is handled separately when identifying finite free modules with
finite powers.

`lem-sf-projection-approximation-comparison`: proved by choosing a cone bound r-d-2,
using both neighboring vanishing degrees and naturality, then detecting isomorphisms on
cohomology. No compatibility of the transformation with shifts is required: the comparison
uses the two functors' own distinguished triangles and the first naturality square.

No existing definition, statement, or public import is changed. The preflight nevertheless
requires a record for the local instance attribute and opened namespace of the private
helper: `coord/changes/R9-finite-constant-proof-context.md`. The attribute is scoped to
that helper and exports no instance. No consumer requires adaptation.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
