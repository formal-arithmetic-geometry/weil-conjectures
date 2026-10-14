## What changed

Proved the body of AlgebraicGeometry.openOrdinaryTensor_pure_germ_coordinates_canonical
from the existing pullback-stalk germ formula and the new additive adjunction-unit
compatibility theorem in Sheaf.AlgebraicGeometry.OpenPinnedTensorRestrictionStalkUnit.
Two proved private helpers normalize unit tensors and transport the scalar map.
The existing scalar-extension theorem and all public signatures are unchanged.

## Proved and sorry left

Closed AlgebraicGeometry.openOrdinaryTensor_pure_germ_coordinates_canonical
(node lem-pc-open-ordinary-tensor-pure-germ-coordinates-canonical).
Added one hole: AlgebraicGeometry.openPinnedTensorRestriction_stalk_unit
(node lem-pc-open-pinned-tensor-restriction-stalk-unit).
This is a decomposition: one hole closed, one strictly smaller hole added, net zero.
The remaining statement concerns additive adjunction-unit maps on a generic commuting
open square. It contains no tensor coordinates, complexes, derived-category assumption,
or cartesian base-change data. The tensor-coordinate normalization and scalar transport
are proved in Lean, rather than delegated to the new statement.
The item's module contains no remaining sorry. The previously proved
AlgebraicGeometry.openOrdinaryTensor_pure_germ_coordinates_linear_extension is preserved.

## No longer needed

None. No existing import or dependency module is pruned. The original statement modules
still supply the model and pinned comparison; the semilinearity import is used by the
unchanged scalar-extension proof. No unit-level route is changed (the item's unit has
empty realized statement and step node lists).

## Where the brief, the DAG or earlier work was wrong

The previous plan named only the model and pinned comparison definitions; neither
states the unit compatibility needed to connect their canonical choices. The existing
proved exists_tensorPullback_stalk_iso already supplies the entire pullback-stalk germ
normalization, so that calculation need not be reproved downstream.
The supplied linear-extension proof was already complete: the starting module had one
textual sorry, not two. LeanSearch was unavailable; Loogle, LeanFinder and local searches
ran and located the general adjunction-unit and restriction-germ formulas.
Sources read: Stacks Tags 0096 and 0098 online, the Mathlib mate/uniqueness and stalk
formulas, and the project's pinned comparison and tensor-stalk definitions.

## New nodes

lem-pc-open-pinned-tensor-restriction-stalk-unit:
lean/Sheaf/AlgebraicGeometry/OpenPinnedTensorRestrictionStalkUnit.lean.
The docstring gives the factor-by-factor unit argument and stalk/germ passage.
No flatness or pullback-square hypothesis is required. Empty opens have no point z;
zero sheaves and identity opens need no exceptional treatment. This is below the unit
route and supplies precisely its missing open-unit compatibility calculation.
No statement or definition changes, change records, or forced adaptations.

## Second reading by G1

1. PASS: compared the delivered canonical module with the repository by diff.
   Both public theorem signatures and the existing private semilinearity helper
   signature are byte-identical. The linear-extension proof is unchanged. No
   existing definition, visibility, public import, or statement changed; no change
   record is needed. The only added import in that module is proof-only.
2. PASS: compiled both delivered modules in import order through lcompile.py
   (6.1 s and 29.2 s), with no errors or warnings. A scratch copy with explicit
   #print axioms checks compiled in 30.3 s. Both new private tensor helpers use
   only propext, Classical.choice and Quot.sound. The canonical theorem, preserved
   linear-extension theorem and new unit theorem additionally use sorryAx, as
   expected from the one declared lower hole. The sole textual sorry is the
   public named openPinnedTensorRestriction_stalk_unit theorem. No prohibited
   declaration or data definition was introduced.
3. PASS: read the unit theorem, its docstring and node against the actual four
   factors of openPinnedTensorRestrictionIso and tensorPullbackCompositionIso.
   The inverse directions agree: input open comparison inverse, composition
   comparison inverse, output composition comparison, output open comparison.
   The Mathlib unit_leftAdjointUniq and unit_conjugateEquiv_symm formulas identify
   the units; restriction-germ and pushforward-germ formulas give the stalk maps.
   Identity opens reduce to the same unit, zero modules give zero maps, and
   empty source opens admit no z. No flatness or cartesian hypothesis is needed.
   The lower theorem omits tensor coordinates, scalar-map transport, complexes,
   degrees and base-change data; the proved helpers discharge those calculations.
   This is a genuine decomposition, not a renamed restatement, with net zero
   holes. Independent searches used Loogle query "leftAdjointUniq", "unit",
   LeanFinder query "Compatibility of the unit of a composite adjunction with
   the canonical isomorphism of left adjoints under restriction", and grep query
   comp_unit_app|restrictAdjunction_unit_app_app|restrictFunctorIsoPullback,
   together with rg over lean/Sheaf and Mathlib. The results supply the component
   identities but no theorem stating this pinned open-square stalk equality.
   The existing open-triangle theorem only supplies an existential comparison
   on global sections and cannot replace the specified comparison here. Closing
   the lower hole requires formalizing the multi-factor coherence and germ
   calculation; no short direct proof was found.
4. PASS: the proof first uses the existing proved tensorPullback stalk germ
   formula, then transports the specified scalar maps and applies the lower
   unit compatibility. The retained imports supply the public models, pinned
   comparison, stalk formula and preserved private semilinearity proof. The
   new module's public imports supply names in its statement. Every original
   proof dependency is retained and used, so No longer needed is complete.
   Read dag/units/sk-thm-picard-semicon.json: realized.statement is empty and
   realized.steps contains an empty list. No realized unit step is bypassed.
5. PASS: the existing node changes only proof, proof_deps and proof_origin.
   Its dependency union equals the uses in its three proof steps. The new
   node has the required source, search records, creation and blueprint data,
   chapter and unit matching the parent, and a verbatim Lean statement. Its
   dependency union also agrees with its proof steps; the proof description
   states exactly the remaining unit/germ calculation.

Second reading changed only this report: added independent review and validation
results. No Lean proof, statement, definition, import or DAG repair was necessary.
