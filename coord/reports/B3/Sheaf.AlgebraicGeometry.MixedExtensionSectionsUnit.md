## What changed

Proved `AlgebraicGeometry.exists_mixedExtensionSectionsUnit` from the existing
`AlgebraicGeometry.exists_mixedAffineSectionsPullbackMate`. Specialize its equation
to the identity on the pullback of Q, simplify the sheaf adjunct of identity to the
unit, and apply the scalar adjunction's hom-equivalence. Its defining unit formula
is exactly the required equation. The independent module and sheaf localization
universes, existing signature, docstring, options, visibility and public imports
are unchanged.

Replaced the two plain proof imports by the one plain import
`Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackMate`. Updated the parent node's
proof, proof_deps and proof_origin. No definition, target statement or other module
changes. No new module, node or change record is delivered.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_mixedExtensionSectionsUnit`
(node `lem-sc-mixed-extension-sections-unit`): 1 of 1 item holes closed.
No sorry remains in the delivered module; no holes are added or split off.
The proof depends on the existing open theorem
`AlgebraicGeometry.exists_mixedAffineSectionsPullbackMate`
(node `lem-sc-mixed-affine-sections-pullback-mate`), already used by another branch
of the target's route. It is an existing dependency, not a new hole. Consequently
this is one local hole closed; global closure/pruning totals remain the pinned
ledger's measurement, not a claim of an unconditional sorry-free target proof.

The first reader's proposed new hole
`AlgebraicGeometry.mixedExtensionSections_model_mate_isIso`
(node `lem-sc-mixed-extension-sections-model-mate`) and its module/node are removed
from the delivery by the second reading. The final proof does not use them.

## No longer needed

Removed both original direct proof imports and their direct proof dependencies:

- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`,
  node `lem-pc-affine-qcoh-derived-equivalence`.
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`,
  node `lem-pc-affine-derived-pullback-tensor-tilde`.

These modules remain transitive dependencies of the existing mate theorem; this
claims removal of direct imports, not global pruning of those modules.
The old direct proof dependency `lem-sc-mixed-global-sections-direct-image-iso`
is now supplied through the existing mate theorem. Its public module import and
statement dependency remain necessary for the unchanged signature.
The proposed model module `Sheaf.AlgebraicGeometry.MixedExtensionSectionsModelMate`
and proposed direct import `Sheaf.AlgebraicGeometry.AffineDerivedPullbackModuleModel`
are also absent from the final delivery; neither was an original direct import.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The initial reading missed the existing independent-universe theorem
`exists_mixedAffineSectionsPullbackMate`, whose identity-theta specialization proves
this item. This theorem appeared in the source before its compiled module was
available locally. The second reader's first attempt to import it failed with a
missing .olean. After the normal compiled-library refresh published it, the reader
used it and removed the unnecessary new model-computation hole.

No mathematical statement error or arbitrary choice in a definition was found.
The existing DAG's proposed affine model calculation is unnecessary directly here;
the existing stronger comparison already packages that argument. This reduction
is below the unit level and leaves the unit route intact.

## Second reading by B3

1. Compared the entire module with the repository version by diff. The existing
   declaration signature, universes, docstring, options, public imports and
   visibility are byte for byte unchanged. Only its proof and plain proof imports
   change. No other existing Lean module or definition changes. Verdict: pass.
2. Checked the hom-equivalence proof from its identity specialization through the
   scalar unit equation. The final module has no textual sorry and no axiom,
   unsafe, opaque, implemented_by, extern or holed definition. Local compilation passed with no errors or warnings. A scratch-copy
   #print axioms probe also compiled and showed exactly propext, Classical.choice,
   Quot.sound and sorryAx. The latter comes from existing open dependencies; no
   new hole or forbidden axiom is introduced.
   Verdict: proof conditional on existing lower dependencies, no new hole.
3. Read the proposed K-flat model theorem, its docstring/node, the equal-universe
   library model theorem, the affine chart-model and equivalence declarations,
   the fixed scalar/sheaf adjunctions and normalized Leray construction. Read
   Stacks Tags 06Z0, 08DV, 08DW(2) and 0AA7 online. Checked zero complexes, empty
   affines/zero rings, identity maps and unbounded K-flat models: no flatness of g
   is required. The proposed lemma was true and a proper model part of the initial
   argument, but unnecessary: it and its hole/node/module are removed.
   Repeated Loogle search '"IsIso", "homEquiv"' returned only general Kan-extension
   adjunction lemmas. LeanFinder search 'base change affine derived sections
   adjunction transpose is invertible on a K-flat complex' returned ordinary
   flatness/descent lemmas. Direct rg of both project roots found the existing
   stronger independent-universe mate theorem. Verdict: no new statement delivered.
4. Took the shorter existing-library route as soon as its compiled module was
   published. Checked every old proof dependency against the final proof and
   recorded all three that are no longer direct dependencies above. The plain
   proof import is the only new import; public imports remain required by the
   signature. The unit sk-thm-picard-duality and its realized fields are unchanged;
   this below-unit auxiliary reduction bypasses no realized unit step. Verdict: pass.
5. Compared the existing node's signature and proof with the final Lean. Its three
   steps now record the existing affine mate, sheaf homEquiv_id, and scalar
   hom-equivalence/unit computation; proof_deps is exactly their union. Corrected
   the proof metadata including the sheaf-adjunction dependency omitted by the
   first reader. All non-proof fields are unchanged. Verdict: pass.

Second reading replaced the model decomposition by the existing theorem's identity
case, removed one proposed new module/node/hole, and rewrote the report and parent
proof metadata for the final implementation. No existing interface changed.
