## What changed
Proved the scalar restriction identity/composition laws, scalar hom linearity,
naturality, identity/composition laws, and scalar functor additivity. Sectionwise
extensionality reduces these laws to the existing module presheaf laws.
No signatures, definitions, attributes, options, or imports changed.
Updated the existing node's proof and proof_origin to record this partial proof.

## Proved and sorry left
Closed 7 of 24 original holes: `scalarFunctor_additive`, `scalarHom_comp`, `scalarHom_id`, `scalarHom_linear`, `scalarHom_naturality`, `scalarRestriction_comp`, `scalarRestriction_id`.
Added holes: none. This is a partial proof, not a decomposition.
Remaining 17 holes: `scalarCohomologyExtMap_add`, `exists_moduleExtEquiv`, `exists_scalarPullbackCoefficient`, `exists_scalarTensorCoefficient`, `scalarCohomologyExtMap_bijective`, `scalarCohomologyExtMap_smul`, `scalarFunctor_preservesFiniteColimits`, `scalarFunctor_preservesFiniteLimits`, `scalarInverseImage_additive`, `scalarInverseImage_preservesFiniteColimits`, `scalarInverseImage_preservesFiniteLimits`, `scalarPresheaf_isSheaf`, `scalarRestriction_linear`, `scalarTensorLeftColimits`, `scalarTensorLeftLimits`, `scalarTensorRightColimits`, `scalarTensorRightLimits`.
All remaining holes retain their original named theorem, source/proof docstring,
and node `def-sc-field-linear-module-cohomology-operations`.

## No longer needed
None. The old node's proof_deps is empty and remains empty. No dependency node or
module was bypassed. The imported module, sheaf, injective-resolution, derived Ext,
and monoidal infrastructure still supports the unchanged constructions and obligations.

## Where the brief, the DAG or earlier work was wrong
The first report omitted scalarHom_id and scalarHom_comp from the proved list and
incorrectly claimed scalarInverseImage_additive, whose proof is still sorry.
The existing node recorded only the prior explicit-data repair, not these new proofs.
Both records are corrected. No mathematical statement discrepancy was found.

## Second reading by K1
1. Compared the whole delivered module with the repository using diff and the
   declaration parser: all existing signatures are byte for byte unchanged; only
   seven theorem proof bodies differ. No definition or visible interface changed.
2. The delivered module compiled locally without errors or warnings through lcompile.py.
   Every remaining sorry is the whole proof of an existing public named theorem; no
   new sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition was
   introduced. A scratch copy with #print axioms for all seven closed declarations compiled in
   37.9 seconds: only propext, Classical.choice, Quot.sound, and transitive sorryAx
   occur; scalarHom_linear has no sorryAx. The delivery tool additionally probes all
   declarations.
   Existing choices are unchanged: the Ext equivalence is characterized on resolution
   cocycle representatives, and the pullback coefficient by the adjunction on every
   section; these are characterizations, not arbitrary witnesses of bare existence.
3. No statements were split off and no declarations or nodes were added. Checked
   section map linearity and naturality against Mathlib PresheafOfModules, and Ext
   additivity against mapExactFunctor_add and comp_add; rg of both library roots found
   no alternate field-linear operation. The sectionwise arguments include zero sections,
   identity maps and arbitrary opens, without extra hypotheses.
4. The proof takes the direct sectionwise and Mathlib routes. No imports were added
   and none of the old proof_deps remains unused (the list was already empty).
   Read dag/units/sk-prop-av-cube.json: no unit statement or step is bypassed or changed;
   its realized fields are unchanged. The module's cohomology and cup-product route stays.
5. Updated the existing node's proof/proof_origin with the seven proofs and seventeen
   open obligations; proof_deps stays empty, consistent with elementary functor laws
   and Mathlib tools. No new node needs metadata or a change record.

Second reading changed: proved scalarHom_linear and scalarHom_naturality; corrected the proved/open counts and declaration lists;
updated node proof metadata. Retained the first worker's five correct proofs.

The optional Ext additivity proof was not retained: it pushed the already expensive
Ext constructions beyond the local 60-second compilation limit. No definition was
changed to accommodate it; the original named obligation remains.
