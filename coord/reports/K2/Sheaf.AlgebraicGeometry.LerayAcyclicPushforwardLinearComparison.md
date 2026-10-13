## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison
with a proof from Sheaf.AlgebraicGeometry.LerayAcyclicAdditiveNaturality. The original
signature, universes, hypotheses, visibility, and docstring are unchanged. The new import
is proof-only. The proof restricts scalars along the two stated ring maps and applies
coefficient naturality to multiplication by p.appTop (f.appTop r), using
pushforward_map_smulHom and Scheme.Hom.comp_appTop.

The new additive theorem contains no base scheme T, map f, restricted module structures,
or linear equivalence. It is the additive comparison plus coefficient naturality needed
before the scalar promotion, rather than the original theorem under another name.
Its complete natural-language proof follows Stacks 01F4(1), 01EY and 03FD. The existing
natural topological Leray edge is available, but its module/abelian derived-image and
terminal Ext-model transports did not yield a clean full proof within the time budget.

Both delivered modules compile cleanly with lcompile.py --all. No definitions or
existing statements change; no forced adaptations are needed. The argument covers
q = 0, zero coefficients, the empty scheme, and arbitrary p and f without geometric
hypotheses. No new data is chosen from a holed existence theorem in a definition.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.Modules.
nonempty_linearEquiv_H_pushforward_of_higherDirectImage_vanishing
(lem-pc-m1-leray-acyclic-pushforward-linear-comparison).

Added and left: AlgebraicGeometry.Scheme.Modules.
exists_addEquiv_H_pushforward_natural_of_higherDirectImage_vanishing
(lem-pc-k2-leray-acyclic-additive-naturality), in the new module
Sheaf.AlgebraicGeometry.LerayAcyclicAdditiveNaturality. Its whole proof is `by sorry`.

This is a decomposition: one upper hole closed and one strictly additive lower hole
added, net zero holes. The target module has no remaining sorry, and the delivery
adds no other holes. Existing dependent holes are not claimed proved.

## No longer needed

No original imports were removed. The old direct proof dependency
lem-sc-module-abelian-zariski-cohomology (module
Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology) is no longer a direct
dependency of the parent. It is still needed by the new additive node, so no
module is claimed pruned transitively. The parent now directly depends only on
lem-pc-k2-leray-acyclic-additive-naturality. No unit statement or step is
bypassed. Exploratory private helpers and temporary proof imports were omitted from
the delivered modules because the finalized reduction does not use them.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original plan marked scalar compatibility
as elementary, but its first additive comparison step did not supply a Lean declaration
with the coefficient naturality interface required by that second step. The new node
states that precise missing interface. Existing affine comparisons add hypotheses not
present here, and the existing module Leray sections edge handles the other degeneration.
LeanSearch returned HTTP 500 and is recorded as unavailable. LeanFinder, Loogle,
Mathlib grep and library searches were performed. Blueprint search for Leray found
no exact module-valued additive comparison with this interface.

## New nodes

lem-pc-k2-leray-acyclic-additive-naturality: the additive equivalence together with its
coefficient-endomorphism naturality, sourced to Stacks 01F4(1), 01EY and 03FD. It realizes
the original additive comparison step and leaves scalar linearity to the proved parent.
Its module is lean/Sheaf/AlgebraicGeometry/LerayAcyclicAdditiveNaturality.lean.
No change records are needed because no existing interface changed.


## Second reading by K2

1. Compared the existing module against the repository version with diff. PASS:
   the signature, universes, visibility and docstring are byte-for-byte unchanged.
   Only its proof body and one proof-only import changed. The additive module is
   new; there are no existing definition or interface changes or change records.
2. Compiled both modules with lcompile.py --all. PASS: no errors or warnings.
   The only delivered sorry is the named additive theorem listed above; neither
   module defines data or uses axiom, unsafe, opaque, implemented_by or extern.
   Explicit #print axioms checks show propext, Classical.choice, Quot.sound and
   sorryAx for both declarations. Thus this is a
   decomposition, not an axiom-free proof of the original mathematical result.
3. Read the new statement, docstring and node against Stacks 01F4(1), 01EY
   (especially 20.13.3's coefficient-forgetting comparison), and 03FD. PASS:
   a natural Leray edge gives precisely the asserted additive equivalence and
   endomorphism compatibility. Degree zero is the natural global-section
   identification; zero coefficients and empty schemes give zero groups; for
   the identity map the comparison can be the identity. No extra geometric
   hypothesis is needed. This is the additive/naturality step of the original
   argument, followed by an actual scalar-linearity proof in the parent, rather
   than the original linear statement renamed. Independent LeanFinder, Loogle,
   grep and repository searches found resolution and derived-transformation tools,
   but no ready theorem with this interface. The existing topological Leray edge
   still needs the module/abelian higher-image and terminal Ext identifications;
   closing that glue is not a short repair.
4. Inspected the scalar proof from the top down. PASS: naturality is applied to
   F.smulHom (p.appTop (f.appTop r)); pushforward_map_smulHom and comp_appTop
   give exactly the two restricted scalar actions. Both imports in the parent
   are needed; the new module needs DirectImage.Basic for its statement. Checked
   dag/units/sk-thm-picard-coherence.json: no realized route entry is removed or
   bypassed. Corrected No longer needed to name the old direct proof dependency,
   while explicitly claiming no transitive module pruning.
5. Compared both DAG records with the Lean declarations and reduction. PASS:
   the parent's proof/proof_deps/proof_origin record the additive step and scalar
   promotion; the new node has its source, complete proof plan, search records,
   split status, creation/blueprint/chapter/unit fields and verbatim Lean statement.
   Existing node changes are confined to the permitted stage-3 fields.

Second reading changed only this report: the explicit old-dependency accounting
and the independent checks above. No Lean or node repair was required. One hole
is closed and one is added, net zero; no transitive hole is claimed closed.
