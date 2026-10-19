## What changed

Implemented the six-step Brown argument in Sheaf.Paper.BrownExceptionalAdjoint.
The proof constructs the target Brown structures, restricts the ambient exact functors
and coproduct preservation, applies Brown representability, equips the right adjoints
with the adjunction-induced shifts, proves counit-compatible uniqueness, and transports
compactification comparisons by conjugation. Identity and cocycle laws for the right
adjoints follow from conjugateEquiv_id and conjugateEquiv_comp.

Added the proved module Sheaf.Paper.CompactificationRefinementIdentity. Its theorem
compactificationRefinementComponent_id proves the identity normalization needed for
common-refinement comparisons. It uses the identity clause of the existing
localizingRefinement_coherence theorem for dense compactifications and arbitrary
unbounded K. Private helpers prove the generic total right-derived left unit law from
the universal property, then specialize it using the underived module compositor's
left unit law. No new sorry is left in this module.

The Brown refinement-map definition directly uses the coherence module's canonical
component. The old formula differs only by the functor-category eqToHom component
equation. The public signature stays identical. The coherence module becomes a public
import because this public definition uses its canonical component. The change record
is coord/changes/T6-brown-refinement-map.md. The required `tools/downstream.py --uses` scan completed on retry: 44 modules
are downstream, and the only textual user of the changed definition is the item
module itself (two occurrences). No consumer adaptation is needed. The change record lists all 44 downstream modules
and their current holders, as well as the item itself.

## Proved and sorry left

Closed the one original hole in
AlgebraicGeometry.ProEtale.CondensedRing.exists_brownExceptionalAdjoints
(node det-sf-existence-brown), from the existing declared dependencies and the proved
identity-normalization theorem. Holes closed: 1. Holes added: 0. Remaining direct
sorries in the delivered Lean modules: 0. No split-off obligation remains.

Also proved
AlgebraicGeometry.ProEtale.CondensedRing.compactificationRefinementComponent_id
(node lem-sf-compactification-refinement-identity).
Private helpers closure_closedUnderIsomorphisms, closure_closedUnderSums,
restricted_preservesColimits, counitCompatibleIsoUnique,
coherentRightAdjointComparisons, derivedId_fac, derivedId_fac', derivedId_inv_app,
derived_left_unit, refinementLowerStarId_eq, derivedNatIso_comp, derivedNatIso_eq,
and refined_comp_unit have complete proofs. The private derivedId definition is an
explicit composite of canonical isomorphisms.

The imported project theorems may themselves still depend on sorry; this delivery
proves the item from those existing declarations as stage 3 requires. It does not
claim an axiom-free transitive proof of Brown representability.

Validation: the resumed session recompiled both delivered modules through `lcompile.py --all`
without errors or warnings (identity normalization 1.5 seconds; Brown theorem 19.6 seconds).
The assigned theorem signature is byte-for-byte identical to the current shared source;
both modules contain zero direct `sorry` and all Lean lines have at most 100 characters.
The unchanged named instance binders in the Brown statement trigger unused-variable
lint, suppressed only for that theorem without changing its statement.

The initial resumed dry run compiled both modules and passed preflight (CODEX review).
Its identity-module axiom probe received no response from the compile server; the delivery
tool records that the merge runs it again. After that dry run, the target structural
argument was revised to avoid applying the disputed full brownHypotheses theorem, and
both revised modules compiled successfully. The revised delivery passed its required
dry run: both compiles, both axiom probes and CODEX-class preflight succeeded.
On 2026-10-19 the final resumed session repeated the required dry run against
current sources; it returned OK at dry-run commit e925c37201 with CODEX review.
The session also reconfirmed the unchanged theorem text, zero direct holes and
100-character line limit in both delivered Lean modules.

## No longer needed

Removed the direct proof dependency lem-galois-yoneda-fully-faithful and its standalone
Mathlib.CategoryTheory.Yoneda import: the existing adjunction shift and conjugation APIs
provide the needed Yoneda argument. Removed the redundant direct import
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible;
the public statement imports already expose its required definitions. The direct import
Sheaf.Compactification.BoundaryRefinement is retained as a unit-route dependency.
Also removed the retained redundant direct imports `Mathlib.Algebra.CharP.Algebra`
from the Brown module and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` from the new identity module:
the required characteristic and coefficient APIs are public transitive imports.
No whole library module is claimed pruned.

The full brownHypotheses theorem is unused. Its module
Sheaf.SixFunctorsBasics.BrownHypotheses remains imported to preserve the specified unit
route; only its ambient structural conclusion is needed and is proved directly from
localizingClosure_exists and DerivedCategory.locallySmall. No compactness assertion
for the target category is used. The source compact generation is an explicit hypothesis.
The new proof import
WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory supplies the
DerivedCategory.locallySmall instance (lem-pc-derived-category-locally-small).

The ambient distinguished-triangle conjunct of compactification_localizing is unused:
the ambient triangulated functor instance restricts by the full-subcategory lift instance.
Its membership and coproduct-preservation conjuncts remain needed. No other declared
proof dependency is bypassed. Added det-def-localizing-closure-existence for the ambient
coproduct instances used in restricting preservation of sums.

## Where the brief, the DAG or earlier work was wrong

The current brownHypotheses declaration is marked STATEMENT-DISPUTED because
compactness for an arbitrary positive-characteristic base field lacks the required
cohomological-dimension bound. This Brown item assumes source compact generation and
needs only target ambient structures. The proof now derives those structural facts
directly and never applies the disputed theorem. The existing unit-route import stays.

The current compactification_coherence_cocycle theorem exposes common-refinement
normalization, but not identity normalization of compactificationRefinementComponent
itself. Common-refinement normalization alone cannot imply that identity. An earlier
retained attempt expected an extra conjunct from a stale restoration of the coherence
module. That restoration is not delivered; the coherence module is unchanged.
The normalization is now proved from localizingRefinement_coherence and the actual
compositor definition. Only its dense geometric specialization is needed by Brown,
so the new lemma uses exactly those hypotheses instead of introducing an obligation
for arbitrary boundary compactifications and arbitrary geometric settings.

The unit record sk-prop-sf-existence describes the older smooth-purity statement.
The assigned node and current main-20261015 six-functors blueprint specify the Brown
argument implemented here; no unit or target statement is changed.

Edge cases for identity normalization include the empty scheme and zero complex.
No nonzero coefficient, boundedness or localizing-membership assumption on K is used.
Its map is the canonical constructed component, so no arbitrary automorphism is chosen.

## New nodes

lem-sf-compactification-refinement-identity, in
lean/Sheaf/Paper/CompactificationRefinementIdentity.lean, proves the identity part of
det-sf-comp-coherence-cocycle proof step 4 in the dense geometric setting used by Brown.
It states no adjoint existence, uniqueness, exactness or cocycle. Its two proof steps
use the existing open-refinement identity and the derived compositor unit calculation.
This new node is proved in the delivery and leaves no obligation for another worker.
The definition change record is coord/changes/T6-brown-refinement-map.md.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
