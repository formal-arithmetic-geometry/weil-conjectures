## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.exists_brownExceptionalAdjoints`
without changing its signature. The refinement-map definition now directly reuses
`compactificationRefinementComponent`, the identical canonical construction. Its
former final equality transport is the component of this functor-level transport
by equality induction. See `coord/changes/H2-brown-refinement-canonical-component.md`. The proof
uses the stated compact generating family, obtains the target Brown structures,
restricts ambient coproduct preservation through full subcategory inclusions, applies
objectwise locally-small Brown representability and Mathlib's partial-adjoint assembly,
and supplies the induced shifts, exactness and counit-compatible uniqueness.

The ambient compactification comparisons lift componentwise to the full localizing
target. Their dense-refinement normalization follows by applying the existing dense
identity-refinement theorem. The existing coherent right-adjoint comparison theorem
then supplies the adjoint comparisons, their uniqueness and both coherence laws.
Updated the item's DAG proof/dependencies to include these two existing supporting
results. No theorem statements or consumer modules are changed. The existing canonical
component module becomes a public import because the definition now references it.
Elaboration selects the adjoint functors as an abstract family with adjunction
witnesses, and explicitly types the uniqueness Hom equivalence, avoiding expansion
of the chosen-right-adjoint construction during inference. Reusing the canonical
refinement component eliminates duplicate transport elaboration. A proved private
`coherentComparisons` wrapper extracts precisely the required counit normalization,
pairwise uniqueness, identity and cocycle from the existing generic comparison
theorem before applying it to the geometric categories.

Validation: the final item compiles through `lcompile.py` without warnings (21.0 seconds). The unused-variable
linter is disabled for the original instance binders `triY` and `comm`, whose names
must remain unchanged with the theorem signature. Its theorem signature is unchanged
byte for byte, and the item has no `sorry` tokens. The unchanged direct consumer
`Sheaf.Paper.MateOpenRestriction` compiles against the delivered module in a
scratch overlay (58.1 seconds); no consumer adaptation is necessary.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.CondensedRing.exists_brownExceptionalAdjoints`
(node `det-sf-existence-brown`). Zero holes remain in the item; zero holes are added.
No decomposition and no new public theorem or axiom is introduced. Existing imported
statements may retain their own holes, as intended for this stage; in particular,
`CategoryTheory.brownHypotheses` and
`AlgebraicGeometry.ProEtale.CondensedRing.compactification_coherence_cocycle`
remain external proof dependencies.

## No longer needed

The private `CompactificationCoherenceCocycle` import is promoted to public
because the canonical map definition now uses it directly.

Removed the direct proof import
`WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint`; the recorded
locally-small objectwise representability theorem is the suitable universe-aware
interface and still uses the generic Brown theorem internally.
Removed `Mathlib.CategoryTheory.Yoneda` as a separate import: the objectwise Brown
module publicly imports it. Also removed redundant private imports
`Sheaf.Compactification.BoundaryRefinement` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`: both
are already public dependencies of `LocalizingExceptionalAdjoint`. No dependency
modules are withdrawn.

Removed obsolete direct tool-use entries `lem-pc-brown-representability-right-adjoint`
and `lem-trf-adjoint-mate` from the item's node. The former remains needed by the
objectwise representability theorem, and the latter is replaced here by the already
recorded coherent-family comparison theorem. All ten existing proof dependencies
are retained; no part of the unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's comparison step omitted an explicit use of the already proved dense
identity-refinement normalization: the common-refinement equation alone has an
extra identity-refinement factor. This proof uses
`lem-sfb-compactification-refinement-component-id` to remove it. It also records
`det-def-localizing-closure-existence` for the ambient coproduct/full-subcategory
restriction argument and its universe reindexing. Neither is a new statement.

The unit-id collision noted by the previous DAG review is unchanged. The current
six-functors-basics blueprint proof (1)-(3) is followed; no unit record is altered.
The source Brown hypothesis theorem already carries a statement-dispute comment
about arbitrary-field compactness. This delivery uses its existing stated target
structural conclusions and the item's explicit source compact generators, without
changing or attempting to repair that separately assigned dependency.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
