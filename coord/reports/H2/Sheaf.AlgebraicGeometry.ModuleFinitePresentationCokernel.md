## What changed

Reduced `AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_isFiniteType`
to finite type of the kernel of a local finite-free generator map followed by the
restricted cokernel map. This is steps 3–5 of Stacks Lemma 0H96, now stated as
`kernel_composite_cokernel_isFiniteType` in the new module
`Sheaf.AlgebraicGeometry.ModuleFinitePresentationCokernelKernel`.

The main proof chooses the finite local presentations of H, composes their generator
maps with the restricted cokernel map, proves these composites epi, and applies the
new kernel theorem. A proved private helper chooses finite local generators of these
kernels, constructs finite presentations on the refined cover, and glues them. The
helper reuses the proved construction in CoherentFiniteTypeLocallyNoetherian.lean;
that scheme-specific module is not imported. Added proof-only imports of the source
library's sheaf Quasicoherent and Generators modules for locality, finite-presentation
construction, and `GeneratingSections.ofEpiFree`.

Both original signatures and their docstrings are unchanged. Both delivery modules
compile without warnings. This is a decomposition, not a completed axiom-free proof.

## Proved and sorry left

Closed the remaining original hole:
`AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_isFiniteType`
(node `lem-weil-pbc-module-finite-presentation-cokernel`).
The special-case theorem
`AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_both_isFinitePresentation`
was already proved on the delivery base and remains proved.

Added one hole, in the new module:
`AlgebraicGeometry.RingedSpace.kernel_composite_cokernel_isFiniteType`
(node `lem-weil-pbc-module-finite-presentation-cokernel-kernel`).
It assumes a finite global presentation only on one open and concludes finite type
of a specific kernel, not finite presentation of the cokernel. No sorry remains in
the item module. Net holes closed minus added: zero; one upper hole decomposed.

## No longer needed

Removed direct proof imports of
`Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting` and
`Sheaf.AlgebraicGeometry.ModuleFiniteTypeImageExtension` from the item module.
They are still dependencies of the new kernel theorem, so these modules remain
reachable and are not globally pruned.

The item proof no longer directly needs nodes
`def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-ringed-space-module-exactness-local-lifting`,
`def-weil-pbc-exact-sequence`,
`lem-weil-pbc-abelian-exact-epi-cokernel`,
`lem-weil-pbc-abelian-exact-iff-epi-kernel-lift`, and
`lem-weil-pbc-module-finite-type-image-extension`.
The new kernel theorem still needs the local lifting, exactness, kernel-lift, and
image/extension facts. The cokernel construction in step 6 uses Mathlib's
`Abelian.epiIsCokernelOfKernel` and `isCokernelEpiComp` directly, so the standalone
abelian exact-epi-cokernel node is unnecessary for this route. No globally unreachable
module is claimed without the maintainer's import-closure calculation.

## Where the brief, the DAG or earlier work was wrong

The special case was already proved on the current delivery base, although the first
local source snapshot still showed its sorry. The delivery tool correctly rejected
counting that change as new progress.

A tentative global finite-free presentation intermediate was discarded after edge-case
review: finite presentation is local and need not imply such a global presentation.
No such statement, module, or node remains in this delivery. The replacement local
kernel theorem follows the Stacks proof and accommodates empty generating families
and the empty open. The item is below the unit's realized statements/steps, and the
unit route is unchanged.

The local copy of literature/stacks-project/modules.tex was absent, so the source proof
was checked at https://stacks.math.columbia.edu/tag/0H96.

## New nodes

`lem-weil-pbc-module-finite-presentation-cokernel-kernel` states finite type of the
relations kernel on each finite-presentation chart. Its complete natural-language proof
uses the short exact sequence from the original relations kernel to the preimage of the
image to the image of f. It is strictly part of the argument, separated from the fully
formalized locality and finite-presentation construction. The new module is
`Sheaf.AlgebraicGeometry.ModuleFinitePresentationCokernelKernel`.

## Second reading by H2

1. Compared the delivered item with the repository using diff. Both existing theorem
   signatures, visibility, and docstrings are byte for byte unchanged. Only proof bodies,
   proof-only imports, and a private proved helper were added. No definitions or target
   statements changed; no change record is required. Verdict: pass.
2. Compiled both delivery modules in import order through lcompile.py. There is exactly
   one sorry, the named kernel-composite theorem listed above, and no forbidden declaration
   mechanism or hollow definition. The finite presentation data and local generator data
   are obtained from proved Mathlib existence projections of the finiteness hypotheses,
   inside proofs; no public data is chosen from an unproved mere-existence theorem.
   Verdict: pass, subject to the axiom probe recorded below.
3. Read the new statement and its complete docstring argument against Stacks 0H96
   (https://stacks.math.columbia.edu/tag/0H96). Its kernel is precisely the preimage of
   the image under the presentation epimorphism. Restriction preserves the cokernel and
   finite type, so the exact extension argument applies. Empty opens and empty finite
   families cause no exception; for f = 0 it reduces to the presentation relations.
   The statement is strictly the finite-type step of the argument and does not assert
   finite presentation of the cokernel. Independent LeanFinder search used "finitely
   generated kernel of an epimorphism from a finite free sheaf to a quotient sheaf";
   Loogle searched kernel/cokernel, and rg searched relation kernels throughout both
   library roots and Mathlib. No matching general result was found. Existing coherent
   cokernel-relations results require coherence, a stronger hypothesis; the finite-free
   surjection kernel theorem requires finite presentation of its codomain, which is the
   conclusion being established here. Closing this split needs an actual extension
   construction on the open slice, not an immediate existing lemma. Verdict: pass.
4. Read the finite-local-presentation reduction and the private finite-generators/kernel
   construction. The latter uses proved upstream locality and cokernel-preservation
   results rather than importing a scheme-specific coherence theorem. All proof imports
   support these constructions; the new kernel module retains its planned dependencies.
   The six old proof dependencies removed from the item's route are all listed in
   No longer needed. Checked dag/units/sk-thm-p1.json: neither the item nor its new helper
   realizes the unit statement or a unit step, and none of the realized route is bypassed.
   Verdict: pass; this is one closed upper hole and one added lower hole, net zero.
5. Compared the existing node JSON: only proof, proof_deps, and proof_origin changed.
   The new node contains the required provenance, searches, statement dependencies,
   source, proof, Lean record, creation record, and blueprint route. Its signature
   matches Lean, and the existing node describes the actual local construction.
   Verdict: pass.

Second reading changed the report only: added independent mathematical, signature,
search, pruning, and metadata checks. No correct proof was rewritten.

Axiom probe: the private construction uses only propext, Classical.choice, and
Quot.sound. Both original theorems and the split kernel theorem additionally use
sorryAx, exactly as expected from the one remaining split hole. No other axiom
appeared. The scratch copy was removed before delivery.
