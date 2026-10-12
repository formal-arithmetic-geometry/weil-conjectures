## What changed

Proved `AlgebraicGeometry.Scheme.Modules.module_open_restriction_injectives` with its
signature unchanged. Added two proved private helpers: `restriction_injective` and
`restriction_resolution`. Restriction exactness uses the existing shared finite-limit
and finite-colimit instances from `Sheaf.Paper.DerivedHomMayerVietoris`.
Extension by zero preserves monomorphisms sectionwise by `DirectSum.lmap_injective`;
sheafification preserves them, and the existing extension-by-zero adjunction gives
injectivity of restriction. Direct image uses Mathlib's precise over-site adjunction.
The restricted resolution is explicitly constructed, including its augmentation.
Updated the item's DAG proof, dependencies and origin to match this shorter route.

Validation: the module compiles without warnings through `lcompile.py`.
The two non-Mathlib proof imports have been checked for import cycles.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.Modules.module_open_restriction_injectives`
(node `lem-weil-pbc-module-open-restriction-injectives`).
No holes remain in the delivered module; no holes were added. This proof uses the
existing stated `AlgebraicGeometry.Scheme.Modules.module_extensionByZero_adjunction`,
which remains sorry in its own module. It does not assert a sorry-free transitive proof.

## No longer needed

Removed proof imports:
- `Sheaf.Algebra.Homology.ModuleStalkExact`;
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`;
- `Sheaf.Topology.PresheafModuleStalkFunctor`.

Removed direct proof dependencies:
- `lem-weil-pbc-module-stalk-exact`;
- `lem-weil-pbc-scheme-modules-enough-injectives`;
- `def-weil-pbc-module-stalk`;
- `lem-weil-pbc-module-restriction-open-immersion-colimits`;
- `def-weil-sheaf-of-modules-category` (still a statement dependency).

The existing public imports are retained to preserve the module's public interface.
The stalk definitions are still reached through the extension-by-zero adjunction's
public signature, so this delivery does not claim they leave the global closure.
The scheme restriction/direct-image adjunction is unnecessary: the statement uses the
localized-site functors and Mathlib's `overPushforwardOverAdj` applies directly.
No unit realization or unit proof step is bypassed: this node is below the unit level.

## Where the brief, the DAG or earlier work was wrong

The DAG's stalkwise proof is longer than needed: shared exact restriction instances
already exist. Preservation of monomorphisms by extension by zero suffices for the
injectivity argument, and follows directly from its real presheaf construction.
Enough injectives are unnecessary when an injective resolution is already given.
The original declaration docstring describes that older plan; it was preserved as
existing API, while the updated DAG and this report describe the implemented proof.

## Second reading by M2

1. Compared the entire delivered module with the repository using diff and checked
   the existing theorem signature byte for byte. Verdict: unchanged, with no altered
   definitions, hypotheses, conclusions, target statements, or undeclared changes.
2. Compiled the file locally through lcompile.py without warnings. Scanned for sorry,
   axiom, unsafe, opaque, implemented_by, and extern: none occurs in the delivered
   code. A scratch copy with #print axioms for the public theorem and both private
   helpers compiled and reported only propext, Classical.choice, Quot.sound, and
   sorryAx. The existing imported extension-by-zero adjunction is still open, as
   reported above. The resolution is an explicit structure, not a chosen arbitrary
   witness; its proof fields are inferred from exactness. Verdict: valid proof of
   the unchanged statement relative to the existing imported open theorem.
3. No statements were split off and no new holes, modules, or nodes were added.
   Read the direct-sum construction and the precise adjunction statement: its left
   adjoint is the concrete presheaf functor followed by sheafification, so the
   monomorphism-preservation instance applies to that very functor. The argument
   requires no nonempty open or nonzero module assumptions; it applies also to the
   empty open, the whole space, and zero modules. Verdict: no restatement or hollow
   construction.
4. Read the shared finite-limit, finite-colimit, and additive proofs and searched
   the library and Mathlib for overFunctor/injective preservation and mapped
   resolutions. The proof already uses the short abstract adjunction route and
   constructs the required augmentation explicitly. Checked every old proof_deps
   entry against the new list: all five removed dependencies are reported above.
   Inspected dag/units/sk-thm-p1.json: this node realizes no unit statement or step,
   and no realized node was pruned. Tested making DerivedHomMayerVietoris a plain
   proof import: this fails elaboration of the public theorem's mapped-complex
   signature because its additive/zero-morphism instance is needed there. Restored
   the public import; it is justified by the statement, not merely the proof.
   Verdict: pruning complete for this delivery; unit route retained.
5. Compared the node JSON with the repository: only proof, proof_deps, and
   proof_origin differ. Their steps match the Lean proof, including sectionwise
   injectivity, sheafification, the precise over-site adjunction, and the explicit
   resolution. Verified proof_deps equals the union of the step uses. Existing
   statement, statement dependencies, unit, and chapter remain unchanged.
   Verdict: DAG agrees with Lean; there are no new nodes to audit.

Second reading changed no delivered Lean or node content. Added this independent
review and documented why the shared-instance public import must remain public.
