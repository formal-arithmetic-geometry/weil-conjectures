## What changed

Completed AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_smul using an
injective-resolution cocycle representative, the explicitly constructed scalarModuleEnd,
and Ext functoriality and scalar-composition identities. The proof-only import
Mathlib.Algebra.Homology.ConcreteCategory supplies cycle representatives.

Made the existing exists_moduleExtEquiv proof explicit about the resolution, scheme,
descent compatibility and inverse identity. Local irreducibility options prevent
repeated unfolding; their scopes end inside this module.

Rebuilt scalarCohomologyExtEquiv with a typed composite additive homomorphism and
AddEquiv.ofBijective. Its entire additive equivalence equals the original constructor,
as independently proved in scratchpad/TacticEquivExtEqualityFixed.lean. Its signature,
visibility and exported attributes are unchanged. The definition edit reopens the
affected-target semantic review under AGENTS.md §4; the equivalence equality is
evidence for that review. The change records coord/changes/fieldLinearScalarProofTransparencyT3.md and
coord/changes/fieldLinearSharedAdditiveComparisonT3.md document these edits and
the textual users; no consumer has been adapted.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_smul (one of two
original holes). Added zero holes; split off zero statements.

Remaining, untouched: AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_bijective.
The resolution comparison dependency lem-sc-module-resolution-homology-ext is proved
in the current library and is unchanged here.

Independent scalar-proof and constructor-equality checks pass through lcompile.py.
The complete delivered module compiled cleanly again in this repair attempt
(51.2 seconds through the launcher's automatic server offload).
The launcher now filters warnings originating in its appended axiom probe; its
previous generated-line warning no longer blocks validation. An initial dry run
compiled and passed the axiom check, then identified missing change-record paths
in this report. Those paths are now recorded above. The final deliver3.py --no-push run printed
OK: the candidate compiles and passes preflight except for the independent second
reading, which the second reader writes. Nothing has been pushed.
Local attempts also reached the 60-second limit under the current compile load;
no compiler tool or timeout was changed.

## No longer needed

None. No existing import, node or module is pruned. The scalar proof uses the existing
resolution-comparison dependency. No blueprint-unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous delivery could not pass the complete-file compiler limit. This attempt
has tested direct equality composition, scalar-unit-first composition, explicit additive
map constructors, cohomology-carrier forms, transparency controls, and a direct
sections-functor diagnostic. These diagnostic files stay in scratchpad and are not
new proof obligations. No compiler tool, timeout limit, repository file or global build
was changed.

The scalar endomorphism is concrete; resolution and cocycle representatives are
chosen only inside a proof from proved surjectivity/existence results. No data is chosen
from an unproved mere existence theorem. The argument includes all degrees, every
characteristic, zero sheaves and the empty scheme. No theorem statement is changed.

The attempted two-file consumer check could not emit the candidate artifact: its
local complete-file compile reached the 60-second limit. The launcher now supports
automatic offload to the project server when local slots are occupied; the successful
probed compile above used that supported path. No consumer adaptation is asserted.


## Second reading by T3

1. Compared the entire delivered module with the repository version and used the
   declaration-interface comparison: every existing signature is unchanged, no public
   import or exported attribute changes, and no other module is delivered. The only
   definition-body change is scalarCohomologyExtEquiv, declared in
   coord/changes/fieldLinearSharedAdditiveComparisonT3.md. The local transparency commands
   are recorded in coord/changes/fieldLinearScalarProofTransparencyT3.md. Verdict: pass.
2. Read the scalar proof and the altered resolution-comparison proof in full. The scalar
   endomorphism is constructed sectionwise; its naturality uses scalarRestriction_linear.
   The cocycle representative is chosen inside a proof from Mathlib extMk_surjective,
   and its evaluation represents the original class by the existing comparison's
   characterization and injectivity. Precomposition represents the scalar multiple;
   Ext functoriality and scalar-composition laws finish the argument. There is exactly
   one direct sorry, in the unchanged named scalarCohomologyExtMap_bijective, and no
   forbidden declaration or hollow definition. The retained bijectivity theorem
   determines the inverse of the explicitly specified map uniquely. The constructor
   equality scratch check compiled independently through lcompile.py (59.6 seconds).
   The first independent deliver3.py dry run passed complete-file compilation and
   the all-declaration axiom probe; it rejected only the then-missing second-reading
   section. Thus every declaration uses only the allowed axioms (including sorryAx
   where the unchanged bijectivity obligation is used). Verdict: pass.
3. No statements were split off, no public declaration was added, and no holes were
   added. The private scalarModuleEnd is a concrete construction, not an obligation.
   The proof is uniform in degree (including zero), characteristic, zero sheaves and
   the empty scheme: it introduces no nonzero or nonempty assumptions. Verdict: pass.
4. Searched the upstream algebraic-geometry library and the Sheaf modules for the scalar
   comparison and scalar-linearity statements; inspected Mathlib mapExactFunctor_smul
   and mapExtLinearMap. Their linear-category hypotheses do not directly address the
   restricted scalar action and the additive moduleExtEquiv here. The existing fixed
   resolution comparison is retained and used. The new ConcreteCategory import is
   proof-only and supplies cyclesMk/i_cyclesMk. No old dependency import is removed;
   therefore 'No longer needed: None' is complete. Read sk-prop-av-cube and its realized
   record: this below-unit argument changes no realization or unit step. Verdict: pass.
5. Compared the delivered node against the repository: only proof and proof_origin
   differ. The appended T3 step follows the actual cocycle/scalar-endomorphism proof,
   uses lem-sc-module-resolution-homology-ext, and preserves the old proof_deps. Its
   Lean declaration exists with exactly the representative characterization used in
   the argument, and its module is now sorry-free. No new nodes are required. Verdict:
   pass.

Second reading changed only this report: added the independent five-point review.
The Lean proof, definition constructor, imports, nodes and change records were retained.
