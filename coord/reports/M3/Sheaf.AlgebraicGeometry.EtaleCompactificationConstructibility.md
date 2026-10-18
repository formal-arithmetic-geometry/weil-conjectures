## What changed

Proved `AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate`
in the assigned module, without changing its signature, universes, hypotheses, or public imports.
All auxiliary lemmas are private and proved in that same module. No new public declarations,
new modules, definition changes, or forced consumer adaptations are delivered.

The proof follows the geometric route of Stacks Tag 0GL0: relative affine line, induction on
relative affine-space dimension, closed-immersion factorization of an affine morphism, finite
affine source cover and relative Mayer--Vietoris, then affine-local base reduction using
finite-coefficient compact-support base change. The bounded-below passage uses left t-exactness
and bounded truncation devissage from the already proved source library instead of constructing
a spectral sequence, exactly the truncation alternative explicitly offered in the source.
The explicit projective compactifications of affine spaces suffice;
general Nagata compactification is not needed. Updated the existing node's proof and dependencies
to record this implementation.

Added proof imports:

- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage`
- `WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `WeilConjectures.Compactification.Affine`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`

The consolidated file compiled cleanly through `lcompile.py` in 23.2 seconds after import
pruning. The pre-consolidation affine-space, cover, and localization arguments were also
compiled during development. A normalized textual comparison verified that the existing
public theorem signature is unchanged. All lines are at most 100 characters.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate`
(node `lem-weil-pbc-etale-compactification-constructibility`).

The delivered Lean file contains zero `sorry`. Added zero holes and split off zero theorems.
This is a proof from existing declared dependencies, including the affine-line,
quasi-finite, composition, relative Mayer--Vietoris, affine-locality and compact-support
base-change inputs. Their existing unfinished proofs are not changed by this delivery.

Checked edge cases: the affine-space induction has an explicit zero-dimensional base case;
the finite affine cover is padded by the empty affine open, so empty source schemes require
no nonempty-cover assumption; finite coefficients may be the zero ring and no characteristic
is inverted; input complexes need only a lower cohomological bound, since the truncation
comparison is performed separately in each requested degree.

## No longer needed

Removed direct proof imports:

- `Mathlib.AlgebraicGeometry.AffineSpace`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.CategoryTheory.TruncationHypercohomology`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`

These are removals of direct imports, not a claim that all their modules leave the targets'
entire transitive import closure. In particular the constructible Serre and exact pullback
APIs remain used through the proved source library. A read-only import-graph comparison found
zero project modules removed from this item's transitive import closure, so the delivery
claims no modules pruned globally.

Removed direct DAG proof dependencies:

- `def-weil-pbc-direct-image`
- `lem-weil-pbc-etale-shriek-compactification-independence`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-weil-pbc-qcqs-over-affine`
- `thm-nagata-compactification`
- `thm-sp-truncation-e2`

The spectral-sequence node is replaced by the explicit truncation argument. General Nagata
is replaced by explicit affine-space compactifications and precomposition. The separate
Grothendieck-abelian theorem and qcqs-over-affine wrapper are unnecessary because the source
library's category instances and the morphism-permanence API already supply the required
instances. Compactification independence is supplied inside the composition and geometric
inputs; the proof makes no separate application. Direct image is already part of the
candidate's implementation and statement dependencies.

Withdrew obsolete `tool_uses` entries for
`lem-weil-pbc-module-sheaves-grothendieck-abelian` and
`lem-weil-pbc-qcqs-over-affine`, preserving the order of all remaining approvals.
No unit realization or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement, signature repair, definition repair, or tool failure was found.
The planned spectral-sequence machinery and the full Nagata theorem were stronger than needed:
the source library already proves the required bounded devissage, left t-exactness and
explicit affine-space compactifications. The new DAG route records those shorter choices.
The existing constructibility-comparison theorem bridges the public finite-stalk predicate
and the source weak Serre predicate without changing either definition.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
