## What changed

Proved CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestriction with its original
signature. Its four proved clauses construct the normalized derived comparison, simultaneous
injective resolutions, the explicit cochain comparison, and the localization/product assembly.
The cochain proof uses a retraction of the finite-product split envelope to split transitions,
solves one minus shift recursively, identifies its kernel with the ordinary limit, telescopes
the finite-block square, and uses the actual shifted mapping-cone map with both coordinates.

Moved the ten existing definitions unchanged into StrictTowerArithmeticRestrictionDefs to
allow the clause modules to share them without cycles. The parent publicly re-exports the
same names, types, bodies and original five public dependencies. No consumer is adapted.
The definition relocation is recorded in
coord/changes/StrictTowerArithmeticRestrictionDefinitionModule.md.

Repair of returned head c470a2b99: added the missing downstream consumer
Sheaf.SixFunctors.SystemPrimitiveComparisonShift to the change record's Users table.
Its textual restriction match names its own comparison constructor, so the unchanged
definition re-export requires no source adaptation. The delivery tool rebases the
retained proof and metadata onto current sheaf-dag before preflight and push.

## Proved and sorry left

Closed the one original hole:
CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestriction
(lem-sp-strict-tower-arithmetic-restriction).

Also fully proved the new theorems:
CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestrictionComparison,
CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestrictionResolution,
CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestrictionModel, and
CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestrictionCochainModel.
The public restriction_preservesKInjectives helper and every private helper are proved.

Holes closed: 1 of 1 original holes. Holes added: 0. Sorries left in delivered Lean: none.
This is a proof, not a decomposition leaving obligations for another worker.
All six delivered modules compile together without warnings. Separate #print axioms checks
of the parent and all four clause theorems report only propext, Classical.choice, Quot.sound.
The temporary axiom probe is excluded from the delivery. Text comparisons confirm that the
parent signature and relocated definition source are unchanged. Resumed validation on
2026-10-19 recompiled all six modules successfully and independently checked all five clause
and parent axiom reports. The unchanged direct consumers
Sheaf.CategoryTheory.CompactSupportRoosCofinality and
Sheaf.Paper.RationalCompactSupportCoefficientCoherence both compile against the delivered
module overlay (4.3 s and 6.5 s respectively), with no consumer adaptation.

## No longer needed

The original parent proof imports are removed there:
Mathlib.CategoryTheory.Preadditive.Injective.Basic,
Mathlib.Algebra.Homology.DerivedCategory.KInjective,
Mathlib.CategoryTheory.Abelian.FunctorCategory,
Sheaf.Algebra.Homology.KInjectiveProductsTermwise,
Sheaf.Algebra.Homology.KInjectiveProducts,
WeilConjectures.Algebra.Homology.KernelShiftedMappingCone,
WeilConjectures.Algebra.Homology.TowerEvaluationKInjective,
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp,
Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses,
Sheaf.CategoryTheory.RingedSiteModules, and
Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients.
The parent imports only its publicly re-exported definitions and three proved clauses.
Termwise products, evaluation, the kernel-to-cone comparison, and the exact-adjoint API
remain used in the appropriate clause modules. The original five public dependencies stay
exported through Defs; none of their visibility changes is used to prune the target route.

The proof does not use lem-weil-pbc-kinjective-hom-derived: the universal property of the
right derived functor gives the natural comparison and its identity equation directly.
Neither prop-pur-kinjective-resolutions-exist nor the ringed strict-tower existence theorem
is invoked to construct resolutions: the
Grothendieck tower category and its existing K-injective resolution API suffice. Its public
interface remains needed for the parent signature. The free finite-prefix diagram argument
is replaced by the already proved lem-weil-tower-split-envelope. No unit route is bypassed.
Removed obsolete parent tool_uses entries; surviving tool dependencies are recorded on the
clause nodes. No claim is made that another target stops using those modules globally.

Removed redundant Comp and Whiskering imports from Comparison; redundant Comp, Whiskering,
Final and DerivedCategory.KInjective imports from Model; and Final from Resolution.
The definition module has no proof-only imports.

## Where the brief, the DAG or earlier work was wrong

The retained report described a remaining CochainModel hole, but the sandbox already held
an unfinished full proof attempt. Repaired its function extensionality, evaluation/product
identifications, shifted-cone coordinate calculations, and two-out-of-three API application.
That cochain theorem is now completely proved in this delivery.

Earlier retained Resolution had a dangling conjunction. Earlier Model had an unbound rho
and needed the normalized unit equation: arbitrary derived comparison isomorphisms do not
satisfy that equation. These corrections concern new, unlanded statements only; the existing
parent signature is unchanged. The existing natural-language parent statement is unchanged.
The earlier worktree timeouts did not recur in the first resumed dry run; that run reached
the compiler and correctly rejected the unfinished retained cochain proof.

## New nodes

lem-sp-strict-tower-arithmetic-restriction-comparison: the proved normalized natural
isomorphism, identity case, and strict-cone equation from the right-derived universal property.

lem-sp-strict-tower-arithmetic-restriction-resolution: the proved simultaneous resolution
with injective terms and the exact-adjoint preservation helper.

lem-sp-strict-tower-arithmetic-restriction-model: the proved product and localization
assembly, including construction of sigma and sigmae and their normalization equations.

lem-sp-strict-tower-arithmetic-restriction-cochain-model: the proved finite-block square,
normalized kernel comparisons and actual shifted-cone map; no RF, eta or rho hypothesis.

def-sp-strict-tower-arithmetic-restriction-data: attachment for the ten unchanged relocated
definitions and their original public names.

Change record: coord/changes/StrictTowerArithmeticRestrictionDefinitionModule.md.

The resumed metadata review replaces raw Lean code in the new nodes’ mathematical statement
fields by self-contained prose and formulas, retaining their exact Lean signatures in
lean.statement. The resolution dependency now names the general Grothendieck functorial
resolution API actually used, lem-weil-pbc-kinjective-functorial-existence, rather than the
unused sheaf-specific prop-pur-kinjective-resolutions-exist.

The resumed dry run passed compilation and axiom checks but found the retained consumer
inventory incomplete. Regenerated the relocation record from the current downstream
textual-use inventory, including current claim holders. No Lean source or signature
changed in this repair.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
