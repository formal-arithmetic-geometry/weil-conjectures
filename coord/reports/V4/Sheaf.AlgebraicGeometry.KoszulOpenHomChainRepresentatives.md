## What changed

Proved `AlgebraicGeometry.koszulOpenHom_chain_representatives` with its signature unchanged.
Private, fully proved helpers identify affine derived Hom with module derived Hom, and
module derived Hom from a K-projective complex with the specified module Hom homology.
The latter constructs the cycles quotient, proves its kernel is the coboundaries, and
uses Mathlib's K-projective shifted-Hom equivalence, including its degree-zero normalization.
The main proof establishes projectivity of the exterior-power terms and K-projectivity
of their extension, composes these equivalences with the specified stage isomorphisms,
and lifts derived maps through K-projectivity and the ordinary affine adjunction.

Added proof imports for exterior-power freeness, module projectivity, and the existing
K-projective chain-representative lemma. All original public imports and declarations
are retained. No definitions or statements changed. The cited Stacks sources 06Z0,
0A8H and 08DD were read. Edge cases need no exclusions: zero source, zero target,
zero ring and r=0 use the same equivalences and projectivity instances.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.koszulOpenHom_chain_representatives`
(node `lem-sc-koszul-open-hom-chain-representatives`). No holes remain in this module;
no holes were added elsewhere. Existing affine-equivalence and stage-diagram construction dependencies still
contribute `sorryAx`, as intended by stage 3. All private helpers are fully proved;
the module Hom helpers use only the three permitted axioms.

## No longer needed

Removed the direct proof import `Mathlib.Algebra.Homology.HomotopyCategory.KProjective`;
the needed results are supplied through the existing derived K-projective module.
No DAG nodes or library modules are pruned: all five original proof dependencies
are used, and the original plan is realized without new nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The planned finite-free/K-projective, affine
transport, and normalized Hom-homology steps all work. Searches found Mathlib's
`CohomologyClass.equivOfIsKProjective` and its normalization API; LeanSearch was
unavailable (HTTP internal server error), not a negative mathematical result.

## Second reading by V4

1. **Interface check — pass.** Read the full repository/sandbox diff and compared
   declaration signatures with the delivery parser: no existing signature, visibility,
   docstring, or definition body changed. Only private proved helpers, proof imports,
   and the original theorem proof were added. No change record is required.
2. **Proof check — pass.** Compiled the entire delivery through lcompile.py without
   errors or warnings (51.6 seconds). A scratch copy printed axioms for all eleven
   declarations, including every private helper, and compiled in 51.1 seconds.
   Only propext, Classical.choice, Quot.sound, and existing-dependency sorryAx occur.
   The module Hom helpers have no sorryAx. No sorry or forbidden mechanism occurs
   in the delivered Lean source. No new definition chooses an arbitrary witness
   from an unproved existence theorem: the helper data are constructed from cycles,
   quotient projections, and fully proved bijections. The affine existence theorem
   is used inside a proof, with naturality proving the required normalization.
3. **Split statements — pass, none.** No new public statement or split-off hole was
   introduced. Read the cycle-kernel, quotient, affine transport, and normalized
   K-projective helpers. The zero ring, zero complexes, and r=0 need no extra
   hypotheses: projectivity and the equivalences cover them. Independently searched
   Mathlib with msearch grep for cohomology-class/homology equivalences and searched
   lean/Sheaf and lean/WeilConjectures. Mathlib homologyAddEquiv concerns the
   AddCommGrp-valued Hom complex; it does not replace the module-valued quotient
   normalization required here. Existing Ext helpers concern projective resolutions,
   not this general module Hom complex.
4. **Route and pruning — pass.** The proof uses the existing affine equivalence,
   Mathlib's extended-projective K-projectivity instance and shifted-Hom API, and
   the existing chain-representative theorem. All three public imports support
   original definitions/signatures. All added imports are proof-only and used.
   The removed direct KProjective import is redundant through the new proof import.
   All five old proof_deps remain used, so no node or module is pruned. Read
   sk-thm-picard-duality.json and its realized field; this lower-node proof changes
   neither the unit's statement nor its route or realized record.
5. **Node agreement — repaired, pass.** The original dependency list matches the
   proof, including the bounded-above projective Mathlib node used by instance
   inference. Updated the item's proof steps and proof_origin to describe the
   actual cycle quotient, shifted-Hom degree-zero normalization, affine naturality,
   and existing chain-representative API. No new nodes or statement changes.

Second reading changed only the node's proof description/provenance and this report,
including the precise inherited sorryAx qualification. The Lean proof needed no repair.
