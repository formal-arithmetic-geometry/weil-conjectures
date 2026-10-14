## What changed

Replaced the earlier sandbox restatement by a standard-source reduction. Added
Sheaf.AlgebraicGeometry.StandardAbelianExtSectionDiagram, whose concrete lift extends
an augmentation by injectivity and then by exactness in each successor degree.
No data is chosen from an unproved existence theorem.

In the assigned module, proved forward naturality of the abelian section comparison
directly from the imported public acyclicComparison_naturality theorem. Descend the identity from the supplied source resolution
D.J to the standard source resolution. The augmentation equations show that D.beta
and this descent followed by the concrete standard lift agree after D.J's augmentation.
Extend by zero and apply bounded-below injective homotopy uniqueness, then sections
and homology. Naturality transports the source comparison, and the standard-source
Ext calculation completes the diagram. Postcomposition with identities uses comp_id.

The existing definition abelianEdgeHom is a definitionally equal alias of the named
standardSectionExtHom, whose body and type are exactly the old composite. This avoids
repeating the expanded Ext expression during type checking. Its signature is unchanged.
Change record: coord/changes/D3-abelianEdgeHom-named-composite.md.

Repair of the returned delivery: removed the duplicate private
section_comparison_inv_naturality declaration. The matching existing
abelianResolutionIso_inv_naturality is private in the normalization module, so it
cannot be invoked by import. Instead the forward comparison helper applies the
existing public acyclicComparison_naturality theorem directly, cancels the acyclic
comparison inverse locally, and composes with the fixed Ext/sections isomorphisms.
No duplicated inverse-naturality theorem remains; no other module or visibility changes.
The delivery tool rebuilds its commit on freshly fetched sheaf-dag.

Added the new calculation module as a public import for this alias; added proof imports
AcyclicComparisonNatural and LiftToInjectiveUniqueUpToHomotopy. Updated both existing
node proof routes and added the standard-source node. No other module is adapted.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelianEdge_section_diagram_after_identity
(new-abelian-edge-section-identity).
The already proved abelianEdge_section_diagram remains proved, unchanged in signature.
There are no sorries in the assigned module.

Added one hole:
AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.standard_abelian_ext_section_diagram
(new-standard-abelian-ext-section-diagram), in its own module. It only asserts the
Ext calculation for the standard source resolution and the concrete constructed lift.
The choice-independence arguments for arbitrary source resolutions and arbitrary lifts
are fully proved in Lean in the assigned module. This is a decomposition, not a net
sorry reduction: one hole closed, one hole added.

All other new declarations are proved or concrete definitions. No target statement,
binder, universe or conclusion changes. The remaining theorem includes degree zero,
zero modules and empty schemes; it does not require acyclicity of f_*F or exact module
pullback. Arbitrary K is bounded below because it is indexed by natural numbers.

## No longer needed

Removed the redundant sandbox declaration section_comparison_inv_naturality.
Its fact is already proved privately in ModuleCohomologyExtResolutionNormalization.
The forward helper now uses the imported general acyclicComparison_naturality API.
No import of the repository version was removed. The unused IdentityResolutionHomology
import from the earlier sandbox attempt is removed. Its theorem only concerns identity
scheme maps and does not supply the diagram for arbitrary f.

The earlier sandbox module AbelianResolutionIsoEdgeFactor and its proposed node
new-abelian-resolution-iso-edge-factor are deleted: they merely restated the goal with
the edge map expanded and are not dependencies of this delivery.

The main node removes these direct proof dependencies, routing instead through
new-abelian-edge-section-identity: def-pc-flat-cohomology-comparison,
def-weil-pbc-module-cohomology-fmap, lem-sc-acyclic-comparison-natural,
lem-sc-injective-module-abelian-acyclic-zariski,
lem-weil-pbc-homotopic-maps-equal-cohomology, and
new-module-cohomology-ext-resolution-normalization. They remain needed as statement
or transitive proof dependencies; none of their modules is globally pruned.

No existing DAG dependency is globally dispensable: forgotten-injective acyclicity is
used through the canonical comparison and the remaining standard calculation; acyclic
comparison naturality and homotopy invariance are used in the proved transport argument.
The existing main diagram node now directly uses new-abelian-edge-section-identity;
the latter records the actual standard-source, naturality and homotopy dependencies.
The unit's statement and realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The landing checker correctly rejected the previous duplicate inverse-naturality
statement. Its normalization counterpart is private, so this repair reuses the public
general acyclic comparison API rather than adding an inaccessible theorem alias.

The earlier report did not describe its files: it said the identity-inserted theorem
was still sorry, while the sandbox instead applied a new theorem with the same
mathematical conclusion. Expanding abelianEdgeHom is not a reduction. The current
delivery discards that attempt and proves genuine source-resolution and lift
independence, leaving only the standard-source Ext identification.

The existing identity-inserted node is itself equivalent to the final equality;
identity cancellation alone does not prove substantive compatibility. Its hole is
now closed by the reduction above, without changing its statement.

The library's original module compiled in about 44 seconds. The repeated expanded
Ext composite in the first replacement exceeded 60 seconds. Naming the composite
provides an explicit morphism type for reuse instead of repeating the large reduction;
no compile limit was raised and no existing library module was split.

## New nodes

new-standard-abelian-ext-section-diagram isolates the Ext identification for the fixed
standard source resolution and the explicit injective-extension lift. Unlike the
rejected restatement, it has no arbitrary D.J, D.beta or compatibility hypothesis;
transport from arbitrary choices is the fully proved argument in the assigned file.
Its source is Stacks 01FB and 01F7, with forgotten acyclicity from 03FD and terminal
Ext evaluation from 06XR. Searches for injective-resolution transport found the
existing Mathlib and project naturality/homotopy API but no section-Ext calculation.

## Second reading by D3

1. Compared the delivered module with the repository version. Existing declaration signatures,
   including `abelianEdgeHom` and both diagram theorems, are unchanged; the alias expands to
   the same composite. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`. There are no forbidden declarations
   and no `sorry` in the assigned module. The only remaining hole is the named, documented
   `standard_abelian_ext_section_diagram` split-off node. A scratch axiom probe against the
   sandbox outputs shows only propext, Classical.choice and Quot.sound for the concrete
   constructions; the two diagram theorems additionally use sorryAx through open dependencies.
   Verdict: pass.
3. Checked the split-off statement and edge cases described in its docstring and DAG node; it is
   strictly the standard-source calculation and does not restate the assigned target. Verdict: pass.
4. Checked the proof route against the DAG: comparison naturality and homotopy uniqueness remove
   arbitrary resolution and lift choices, then the standard-source node supplies the calculation.
   The unit route and realized nodes are preserved; removed duplicate inverse-naturality work is
   not used. Verdict: pass.
5. Checked imports and node metadata against the proof. The standard calculation is a public
   statement dependency, while the naturality and homotopy modules are proof-only imports; the
   node proof dependencies match the actual route. Verdict: pass.

Second reading changed only this report, adding the independent checks. The delivered Lean
proofs required no repair. Repeated semantic and local searches found generic Ext/cocycle
representation lemmas, not a ready-made section comparison calculation. No target statement
or existing interface was weakened.

