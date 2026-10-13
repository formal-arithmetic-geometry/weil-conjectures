## What changed

Proved AlgebraicGeometry.coherentFormalModules_affine_reconstruction_assembly with its
original signature. Only the assigned Lean module and its proof-route DAG record are
changed. Added proof-only imports of CoherentAffineSectionsFinite,
CoherentFiniteTypeLocallyNoetherian, and the source-library Modules.Tilde. The original public quotient-functor import stays unchanged.

The proof constructs the canonical map at each level by the tilde/Gamma adjunction and
cokernel.desc. Annihilation makes it factor through the quotient. Its sections map is
surjective by the adjunction triangle. The assumed objectwise isomorphism turns it into
a surjective endomorphism of a finite section module, so 05G8 makes it invertible.
Counit naturality reflects this to a sheaf isomorphism. Transition compatibility and
outer morphism naturality are proved separately by cancelling quotient projections.
No arbitrary witness of an unproved existence theorem defines library data: the only
choices in this theorem are the supplied isomorphisms and projection-compatible maps.

Read Stacks 087W at https://stacks.math.columbia.edu/tag/087W (the local literature
checkout is absent on this machine) and the pinned Mathlib/source-library signatures.
Searches through msearch.py, Mathlib, Sheaf and WeilConjectures found the finite-module
endomorphism theorem and generic NatIso.ofComponents construction. The unit record
sk-thm-p1 was read; this subsidiary node is not a realized unit statement or unit step,
and no unit route was bypassed. Checked imports with import_direction.py.

## Proved and sorry left

Closed one of one original holes:
AlgebraicGeometry.coherentFormalModules_affine_reconstruction_assembly
(node lem-weil-pbc-coherent-formal-modules-affine-reconstruction-assembly).
No sorry remains in the delivered Lean module, and no holes or modules are added.
This is a proof, not a decomposition. Existing dependencies may retain their own holes.
Single-file lcompile.py completed without errors or warnings in about 21 seconds.

## No longer needed

The second reader removed the redundant proof-only import
Mathlib.RingTheory.Noetherian.Orzech: the same declarations and instance are already
available through the retained imports, verified by compiling without it.
No original import was removed: the sole original public import is needed by the
statement. The revised proof does not directly need
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections or its module
Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections; it is removed
from this node's proof_deps. That module may remain reachable through other consumers.
The adic-completion definition is still needed by the unchanged statement, but no
completion theorem or completion construction enters the proof, so
 def-weil-pbc-adic-completion is removed from proof_deps (retained in stmt_deps).
An experimental quotient-comparison split was eliminated; no new node is delivered.

## Where the brief, the DAG or earlier work was wrong

The old route was too vague: hobj supplies arbitrary objectwise isomorphisms without
projection compatibility, so directly choosing them does not prove naturality. Rather
than strengthen that interface or repeat the entire first-isomorphism argument, the
proof builds the canonical quotient comparison and uses hobj solely to prove its
invertibility by the finite-module surjective-endomorphism theorem. The kernel-equality
half of hquotient is unnecessary for assembly once hobj is assumed; the surjectivity
half is used. No signature or definition was changed. The proof uses the existing
05G8 Mathlib-leaf node and existing coherent-affine-sections-finite node, not new nodes.
Edge cases I = bottom, I = top, the zero module and the zero ring require no exclusion:
annihilation, adjunction triangles, finite-module endomorphisms and epi cancellation
all hold in those cases. No statement is disputed.

## Second reading by K1

1. Compared the sole delivered module and node with the repository using diff. The
   existing theorem signature is byte for byte identical (also checked by extracting
   the text from `theorem` to `:= by`). There are no new declarations, definitions,
   changed public imports, or change records. Verdict: unchanged interface.
2. Compiled the delivered file locally without errors or warnings. Read the entire
   proof: the quotient comparison is constructed by cokernel.desc, its sections map
   is surjective by the adjunction triangle, and Hopficity proves it invertible using
   the supplied objectwise isomorphism. Both naturality proofs cancel cokernel epis.
   A scratch copy with #print axioms reports exactly propext, Classical.choice,
   Quot.sound, and sorryAx from existing open dependencies. No forbidden declaration
   or attribute and no local sorry occur. The proof adds no library data construction
   from an arbitrary unproved existence witness. Verdict: valid relative proof.
3. There are no split-off statements, new holes, or new nodes. Checked ideal bottom,
   ideal top, zero modules, and the zero ring: the argument requires no nonzero
   hypothesis and its adjunction, epi cancellation, and finite-module endomorphism
   steps remain valid. Verdict: no decomposition or statement repair needed.
4. Searched the source library and Sheaf for reconstruction/quotient isomorphisms,
   and Mathlib via msearch for natural isomorphism components, using terms different
   from the first reader's search. The available NatIso.ofComponents and finite
   endomorphism results are used; no existing complete reconstruction assembly was
   found. The retained imports supply the unchanged signature, coherent sections,
   quasi-coherence, and restriction of finite sections to A. Removed the redundant
   Noetherian.Orzech import after a successful compile without it. The two old
   dependencies genuinely pruned are listed above; the old coherence-equivalence
   dependency remains needed and is now restored. Read sk-thm-p1.realized: this
   subsidiary assembly node realizes no unit statement or step. Verdict: route kept.
5. Compared all node fields with the original: only proof, proof_deps and
   proof_origin change. The finite-module and adjunction nodes match the argument.
   Restored pqf-lem-coherent-ft-locnoeth, whose coherence equivalence is directly
   applied, and added the existing lem-weil-pbc-formal-module-ideal-power-factor,
   whose formalModuleQuotient_factor is directly applied. Each is listed in the
   appropriate proof step as well as proof_deps. Verdict: node matches Lean.

Second reading changed only the redundant proof import, the two missing proof-route
node dependencies, and this report. The proof body and signature are unchanged.
