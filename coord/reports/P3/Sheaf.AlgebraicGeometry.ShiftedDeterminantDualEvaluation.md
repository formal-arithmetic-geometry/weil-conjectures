## What changed

Proved `AlgebraicGeometry.shiftedDeterminant_dual_evaluation` with its signature unchanged,
from the new ordinary sheaf evaluation `AlgebraicGeometry.determinant_dual_evaluation`.
The new module is `Sheaf.AlgebraicGeometry.DeterminantDualEvaluation`.
The proof obtains flatness from the ordinary tensor inverse, constructs the comparison
between the derived tensor of singles and the single of the ordinary tensor using K-flatness,
identifies the single of the structure sheaf with the derived unit, and cancels the two shifts.
All four private isomorphism helpers are fully proved; none contains `sorry`.
The single-object comparisons adapt the existing code in upstream
`WeilConjectures.SixFunctors.Etale.Derived.Invertible` to the general monoidal abelian category.
The shift comparison uses upstream K-flat shift commutation directly.

Added proof imports of the new module, `WeilConjectures.CategoryTheory.Abelian.Flat.Basic`
and `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit`.
The existing public imports and all existing definitions and statements are unchanged.
Second reading narrowed the new module's public tensor import to the upstream monoidal
module actually needed by its signature, and put the ring-module exterior pairing
proof import in the new ordinary module where its remaining proof plan uses it.
Updated the item's node proof and dependencies to match the Lean argument.
Both sandbox modules compile without warnings through lcompile.py.

Source read: https://stacks.math.columbia.edu/tag/0BRT, last paragraph of the proof.
The local checkout lacks literature/stacks-project/duality.tex, so the official source was read
online. The new node records the original source path and exact place.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.shiftedDeterminant_dual_evaluation`
(node `lem-sc-shifted-determinant-dual-evaluation`). No sorry remains in the item's module.
Added one hole: `AlgebraicGeometry.determinant_dual_evaluation`
(node `lem-sc-determinant-dual-evaluation`), in its own new module, with a complete
natural-language proof in its docstring. Its proof is exactly `by sorry`.
This is a decomposition (one hole closed, one added), not a claim that the whole
geometric determinant argument is finished. The entire passage from the ordinary
sheaf isomorphism to the shifted derived isomorphism is now proved.
No other holes were added or modified. Existing imported dependencies may still use sorry.

The remaining ordinary theorem is strictly step 1 of the original plan: no derived category,
flatness hypothesis, localization, or shifts occur in it. The Lean proof of the original item
combines it with proved flatness, tensor, unit, and shift comparisons.
Edge cases checked mathematically: d=0 gives multiplication of structure sheaves;
d=1 is the ordinary dual-line evaluation; over a free rank-d module the paired top basis
wedges evaluate to 1; on an empty scheme every involved sheaf is the zero/unit object.
No field, reducedness, nonemptiness, or positive-rank hypothesis is used.

## No longer needed

Second reading removed the new ordinary module's direct public import of
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct in favor of its underlying
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal. Its change-of-rings and
positive-tensor-power declarations are not needed by the new statement. This is no
claim of global pruning: TensorProduct is still reached through TensorClosed.

Removed direct proof imports `Mathlib.LinearAlgebra.ExteriorPower.Pairing` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` from the item's module.
The ring-module pairing node `lem-sc-exterior-power-dual-pairing` is no longer a direct
proof dependency of the shifted theorem; it is still needed below the ordinary evaluation
node. Likewise `def-amb-finite-locally-free-module` and `def-sc-sheaf-exterior-power` remain
statement dependencies and are used in the ordinary geometric step, but their proofs
are not directly applied by the shifted theorem. No claim is made that these nodes or
modules have left the targets' global import closure.
The unit record sk-thm-picard-duality has empty realized statement and step lists;
no required unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's sole ring-module pairing dependency does not provide the sheaf-local construction,
sheafification compatibility, or gluing isomorphism required by its first step. That precise
missing ordinary step is the new theorem. The second step required no new sorry:
upstream already proves K-flat single-complex and localization tensor comparisons.
Flatness need not be reproved stalkwise: ObjectProperty.flat_of_tensorIso gives it from the
ordinary inverse. The direct upstream shiftTensorShiftIso couples its Grothendieck and
derived-category universes, whereas this item quantifies independent u and w. The private
helper reconstructs the comparison from the existing earlier K-flat lemmas, preserving
both universes. Also X.Modules has its own Category instance: the new statement uses
explicitly typed underlying SheafOfModules objects, matching the shared derived category.
No statement was disputed or changed.

Searches: LeanFinder returned ring-module invertibility and exterior-power results;
Loogle returned pairingDual and bijective_pairingDual; grep found no ordinary sheaf
isomorphism. LeanSearch returned Internal Server Error, recorded as unavailable.

## New nodes

`lem-sc-determinant-dual-evaluation` records the ordinary determinant-pairing isomorphism
of step 1 in Sheaf.AlgebraicGeometry.DeterminantDualEvaluation. It depends on existing
scheme, local-freeness, internal-Hom, exterior-sheaf and ordinary tensor definitions, and
uses the existing ring-module exterior pairing node in its local-basis proof. It neither
imports nor depends on the shifted theorem, so introduces no cycle. The only remaining
sorry is its named public theorem. No change record is needed: no existing statement,
definition, or public import changed.


## Second reading by P3

1. Interface: PASS. Diffed the item against the repository; its sole existing theorem's
   signature is byte for byte identical. Existing public imports and docstring are unchanged.
   The other module and node are new. No existing definition or statement was changed and
   no change record is required.
2. Kernel and holes: PASS. Both modules compile through lcompile.py. Scratch-copy
   #print axioms checks on all four private helpers show exactly propext, Classical.choice
   and Quot.sound. Both public evaluation theorems additionally show sorryAx, as expected
   from the named ordinary evaluation and existing imported open statements. No forbidden
   declaration or attribute occurs, and the only new sorry is the public named theorem
   determinant_dual_evaluation, with its complete proof and source in the docstring.
3. Split statement: PASS. The ordinary sheaf evaluation is true for arbitrary schemes and
   finite locally free constant rank d; rank zero is ring multiplication, rank one is line
   evaluation, and empty schemes cause no exception. The local dual bases yield inverse
   determinant transition factors, so their pairing glues. Read exteriorSheaf's actual
   sheafification definition and internal Hom usage. This is only the geometric first step,
   not a restatement: the derived single, unit, flatness and shift work is separately proved.
   Independent searches used LeanFinder "invertible determinant sheaf exterior power dual
   evaluation", Loogle exteriorPower.pairingDual, msearch grep IsInvertible, and rg on the
   library. Mathlib's results are ring-module pairings; determinant_shortExact asserts
   invertibility but supplies no dual identification or sheaf evaluation. No duplicate or
   quick proof of the remaining sheaf gluing theorem was found. Verified the source's
   determinant inversion at https://stacks.math.columbia.edu/tag/0BRT.
4. Route and pruning: PASS after import repair. Read the upstream Etale.Derived.Invertible
   single comparisons and DerivedCategory.Monoidal.Shift. The private helpers faithfully
   specialize these arguments to general monoidal abelian categories, and the custom
   two-shift comparison is necessary because the upstream convenience declaration couples
   the Grothendieck and derived universes. The old proof dependencies not directly used
   are all listed under No longer needed. The unit's realized statement and step lists
   are empty, so no realized unit node is bypassed. The ordinary module needs moduleRings,
   hence its public DerivedHomMayerVietoris import is a signature import, not a proof import.
5. DAG: PASS. Read both nodes and checked proof_deps equals the union of step uses.
   The item's three steps describe precisely the ordinary evaluation, K-flat derived
   comparison, and shift cancellation implemented in Lean. The new node has the required
   source, proof, searches, status, created, blueprint, chapter, unit and verbatim Lean record.
   There is no dependency back to the shifted item.

Changes: narrowed the new ordinary module's public import from
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct to
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal, whose tensor structure is the
one its signature uses. Added a plain Mathlib.LinearAlgebra.ExteriorPower.Pairing import
there, matching the remaining node's ring-module pairing dependency. No proof was rewritten
and no further hole was closed or added. This delivery remains a one-for-one decomposition.
