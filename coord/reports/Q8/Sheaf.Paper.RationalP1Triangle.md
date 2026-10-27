## What changed

`Sheaf.Paper.RationalP1Triangle` now assembles its six conclusions from the explicit ambient
kernel contractions, the integration fields of the referenced coefficient diagram, and the
canonical compactification comparisons. All three existing public declarations, including the
complete statement of `rationalP1_triangle`, retain their signatures and bodies except for the
theorem proof. Existing public imports are retained.

The kernel calculation applies to any pair with `UnitCounitNormalized`. The parent supplies this
property for the selected pair from `unitCounit_existsUnique`; the property fixes both ambient
component formulas, with proof-irrelevant invertibility witnesses. The proof derives both actual
triangles, constructs `Adjunction.CoreUnitCounit`, and retains exactly the specified unit and
counit. Its Brown comparison is proved by equality of the localizing ObjectProperty predicates,
the trivial proper compactification, fully faithful cancellation of the ambient inclusion, and
uniqueness of right adjoints.

`Sheaf.Paper.RationalP1KernelContractions` states the separate geometric calculation of the
canonically normalized components before integration. Its docstring retains the complete
first/second kernel argument and the canonical-map/source normalizations. No adjunction is
assumed. The new node and parent proof records follow this route. No existing definition or
statement is changed, and no downstream adaptation or change record is required.

## Proved and sorry left

Closed in the item: `AlgebraicGeometry.ProEtale.RationalP1.rationalP1_triangle` (node `det-
prop-p1-adjunction-rational-triangle`), by a complete Lean assembly from the new geometric
calculation and existing dependencies. The item has zero remaining `sorry`.

Added: `AlgebraicGeometry.ProEtale.RationalP1.rationalP1_kernel_contractions` (node `lem-
rational-p1-kernel-contractions`), one `sorry` in the new module. This is a decomposition, not a
net proof: one upper hole closed, one strictly smaller geometric calculation left, net zero
holes closed. The independently proved parts are selection of the prescribed normalized pair,
both integral actions being identities, construction of the prescribed adjunction from the two
contractions, and the full Brown comparison.

Validation: the new kernel module compiles without style warnings, and the final parent
module compiles cleanly in 31.3 seconds using that sandbox dependency. Signature/body
comparison confirms that every existing public signature, both definition bodies, and
the complete public import sequence are unchanged.

No definition contains a hole. The new statement has been checked on zero objects and on the
identity/section specialization of its categorical calculation: zero factors give zero maps, and
the canonical section comparison reduces to the right unitor. The rational Tate line is rank one
and its shift is even, so the self-symmetry used in the second contraction has no sign.

## No longer needed

The parent assembly removes these direct proof imports:

- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.CategoryTheory.Monoidal.Mod`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.DiagonalTowerCoefficients`
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`
- `Sheaf.Paper.RationalLocalizingProjectionFormula`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.RingedKunnethFactorizations`
- `Sheaf.Paper.RingedProjectionTensorComposition`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`

The original geometric route is retained in the kernel-contraction child. In particular, ringed
Kunneth factorization, projection/tensor/composition coherence, exchange coherence,
module/ringed comparison, proper localizing projection, diagonal trace base change, adjunction
mates, composite adjunctions and canonical derived pushforward composition remain dependencies
of that calculation. Their removal as direct imports of the assembly module does not prune those
modules from the mathematical task. No library module is withdrawn or globally pruned.

The parent's obsolete direct `tool_uses` entries for those geometric operations are removed
because its proof now calls the child. The parent retains its direct approvals for localizing
closure equality, projective-space properness, and compactification coherence. The existing
unit's first identity, second identity, integration, adjunction, and Brown comparison route all
remain represented.

## Where the brief, the DAG or earlier work was wrong

The declarations in the stated dependency list do not directly give the final ambient
contractions. The ringed results are generic and need transport to the fixed internal-module
maps; the coefficient base-change theorem compares complete families over two base schemes and
needs identification with the two projective models of the self-product. These are geometric
normalization steps, not an application of the generic triangle identities. The new child
records this remaining calculation explicitly. Existing dependency theorems containing `sorry`
were treated as available declarations, as required.

## New nodes

`lem-rational-p1-kernel-contractions` records the first/second geometric contraction before
integration, for every pair normalized by the literal `unitComponent` and `counitComponent`
formulas. It asserts the two kernel equalities before integration, and no adjunction or Brown
comparison. The source is the current blueprint's opening paragraph and First/Second identity
paragraphs. Its proof retains the original four geometric steps and dependencies. Three Mathlib
searches found no matching result. No change record is required.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
