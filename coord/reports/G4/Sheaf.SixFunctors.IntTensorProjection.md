## What changed

Proved locallyClosedImmersionTensorProjection by composing the open and closed
immersion natural bifunctor formulas, including derived pullback composition.
Its signature is unchanged. Added the proved modules OpenImmersionTensorProjection
and ClosedImmersionTensorProjection. All imports added to the assigned module are
proof-only; its public imports are unchanged.

The closed case uses the existing normalized canonical closed projection family,
its naturality, and exact derived factorization. The open case builds the Hom-set
equivalence chain from the existing open internal-Hom formula and adjunctions.
Three proved private helpers construct Yoneda isomorphisms and check naturality in
both inputs and the output. An actual vanishing-ideal construction supplies the
closed complement; Noetherianity of the ambient scheme supplies quasi-compactness.
No new definition chooses data from a mere unproved existence assertion.

## Proved and sorry left

Closed original hole:
AlgebraicGeometry.ProEtale.CondensedRing.locallyClosedImmersionTensorProjection
(node det-lem-int-tensor-projection), 1 of 1 original holes.

Also proved, with no holes:

- AlgebraicGeometry.ProEtale.CondensedRing.openImmersionTensorProjection
  (lem-sfb-open-immersion-derived-tensor-projection).
- AlgebraicGeometry.ProEtale.CondensedRing.closedImmersionTensorProjection
  (lem-sfb-closed-immersion-derived-tensor-projection).

Holes added: zero. Holes left in all three delivered Lean modules: zero.
Existing imported obligations, including openClosedInternalHomFormulas, retain
their own holes; this delivery proves the assigned statement from those recorded
declarations. No new obligation is handed off.

Validation: the earlier lcompile.py --all compiled all three modules without errors
or warnings: closed case 0.9 s, open case 6.2 s, assigned module 4.2 s. The resumed
required dry run passed at commit 9d2520ab91 with CODEX review class. Its axiom
probes for the assigned and open modules received no server response within 184 s
and 207 s; the tool records that merge reruns them. A separate resumed --all retry
received no server response for the first (closed) module within 301 s and stopped
without compiling; it reported no Lean diagnostic. These server-response timeouts
are not successful fresh axiom checks.

## No longer needed

Removed direct proof imports from the assigned module:

- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
- WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
- Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
- Sheaf.Paper.ModuleObjects
- Sheaf.CategoryTheory.RingedSiteModules
- Sheaf.CategoryTheory.SheafTensor
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
- Sheaf.CategoryTheory.ModulePullbackTensorIso
- Sheaf.Algebra.Homology.KFlat
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- Sheaf.CategoryTheory.MultivariableDerivedCalculus

Old proof dependencies no longer directly used by the assigned node:

- sk-def-sfb-module-objects
- def-weil-sheaf-of-modules-category
- lem-sfb-alpha-iso
- def-sfb-module-upper-star
- def-sfb-module-lower-star
- def-sfb-module-open-lower-shriek
- sk-def-sfb-sheaf-tensor
- def-pur-sheaf-tensor-product
- def-sfb-module-linear-open-lower-shriek
- sk-def-sfb-dc-setting
- lem-weil-pbc-finite-type-over-noetherian
- lem-weil-pbc-noetherian-open-subscheme-noetherian
- lem-weil-pbc-proetale-ringed-open-closed
- lem-weil-pbc-proetale-immersion-limit-preservation
- lem-weil-pbc-ringed-topoi-module-pullback-tensor
- def-sfb-module-upper-lower-adjunction
- lem-weil-pbc-left-adjoint-preserves-colimits
- def-pc-tensor-complex-sheaves
- def-pc-kflat-complex
- def-pc-flat-sheaf-modules
- lem-pc-kflat-resolution
- lem-weil-pbc-site-derived-tensor-descent
- def-sfb-derived-tensor-modules
- lem-sfb-derived-tensor-modules-derived
- lem-sfb-multivariable-derived-calculus
- lem-weil-pbc-localization-universal-property

All old top-level tool_uses entries are withdrawn from the assigned node. These tools
may remain transitively needed by CondensedOpenClosedInternalHom or the open case;
this does not claim global unreachability. The unit's open/closed/composition route is
kept. sk-lem-int-tensor has no realized node attachments; no realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The old plan repeated theory
already contained in the existing normalized closed projection declaration. Reusing
it avoids repeating the K-flat and localization construction. The existing open
internal-Hom formula gives the shorter adjunction/Yoneda route recorded in the new
open node. No existing definition, signature, visibility or target statement changed.

## New nodes

lem-sfb-open-immersion-derived-tensor-projection: open immersion case, fully proved
by the Hom-equivalence/Yoneda argument, including all three naturality checks.

lem-sfb-closed-immersion-derived-tensor-projection: closed immersion case, fully proved
from normalized projection, pointwise detection and exact derived factorization.
Both inherit sec-six-functors-basics and sk-lem-int-tensor. Whole-blueprint searches
for projection formula, open immersion tensor, and closed immersion tensor found no
separate blueprint node with either derived condensed-module statement; the finite
coefficient and abelian-sheaf projection statements have different coefficients or
categories. Both nodes record their precise parent-proof paragraphs. There are no
definition change records or forced consumer adaptations.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
