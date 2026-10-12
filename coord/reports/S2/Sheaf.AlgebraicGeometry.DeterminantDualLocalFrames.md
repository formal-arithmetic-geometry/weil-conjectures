## What changed

Proved `AlgebraicGeometry.exterior_dual_local_frames` in the assigned module without changing
its signature or docstring. Constructed the section basis from the free trivialization,
constructed the dual sections by transporting its dual basis through local evaluation,
transported both exterior bases through the sheafification unit, and applied local evaluation
to the exterior sheaf. Added proof-only imports for the two new modules, finite dual and exterior bases,
and the free-sheaf sections API. Removed the redundant proof-only internal-Hom import.

Added `Sheaf.AlgebraicGeometry.Modules.DualLocalEvaluation`, with a complete proof of
`AlgebraicGeometry.Scheme.Modules.dual_local_evaluation_equiv` for any finite index type.
The proof restricts finite inclusions and projections, proves the generator expansion on
every smaller open, proves evaluation injective by naturality, and gives its inverse by a
finite sum of coordinate morphisms. Its private helper is fully proved.

Added `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison`, isolating the
remaining sheafification comparison. Updated the original node's proof route and dependencies.
The unit route and all existing statements and definitions stay as written.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.exterior_dual_local_frames`
(node `lem-sc-exterior-dual-local-frames`): its combining proof compiles with no internal holes.
This is a decomposition, not a claim of a sorry-free target closure: one upper hole is closed
and one lower hole is added (net zero holes).

Fully proved `AlgebraicGeometry.Scheme.Modules.dual_local_evaluation_equiv`
(node `lem-sc-finite-free-dual-local-evaluation`), including the private
`evaluation_bijective_of_generators`. This new module contains no sorry.

The sole sorry left in the delivery is
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_local_free_comparison`
(node `lem-sc-exterior-sheaf-local-free-comparison`). It states finite freeness on U and
bijectivity of the actual sheafification unit on every smaller V; it contains no dual frame
or evaluation assertion, and is strictly one part of the original argument. It is used twice,
for M and its internal dual. Its docstring and node give the full remaining argument.

All three modules compile locally without warnings. Edge cases checked mathematically:
empty finite index types and rank zero use empty sums; n=0 uses the singleton empty wedge;
n>r uses the empty exterior index; zero rings and empty opens require no nontriviality.
The proved evaluation argument works in all these cases without division or a nonzero basis.

## No longer needed

Removed the original proof-only import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`; its declarations remain
available through the existing public dual import. No original node or module is globally
pruned: the original exterior-basis and module-sheafification dependencies are still needed
inside the new exterior comparison node. The original generic module-sheafification node is
no longer a direct dependency of the frame theorem; it remains a transitive dependency.
The new exterior comparison module imports the Mathlib free-sheaf interface directly and
does not import the unrelated scheme duality module.

## Where the brief, the DAG or earlier work was wrong

The existing proof dependencies provide exterior bases of module exterior powers and the
generic sheafification adjunction, but no declaration states that the sheafification unit is
bijective on a finite-free open or that the exterior sheaf is free there. That is the remaining
new theorem. The internal-dual evaluation comparison was also absent; it is now proved.

The stated literature path is not populated on this machine. Read the cited source directly
at https://stacks.math.columbia.edu/tag/0BRT (lemma-smooth-proper). As the existing node
already notes, that tag uses determinant inversion but does not state either coordinate
lemma. The new arguments are explicitly marked as agent expansions of the existing node's
steps, not as verbatim Stacks lemmas. Blueprint-wide searches for exterior powers and internal
duals found no matching blueprint statement. LeanSearch returned Internal Server Error;
its searches are recorded as unavailable, not as no-match evidence.

## New nodes

`lem-sc-finite-free-dual-local-evaluation`: generic identity-open evaluation of the internal
dual on a finite-free open. Its module is fully proved and is used for both M and its exterior
sheaf. It realizes original steps 1 and 3, with finite-coordinate reconstruction in Lean.

`lem-sc-exterior-sheaf-local-free-comparison`: the remaining original step 2. It isolates
local sheafification and freeness of the exterior sheaf; the frame theorem supplies the
actual wedge bases by Mathlib basis transport. No change records or forced adaptations.

## Second reading by S2

1. **Interface checked — pass.** Read all three delivered modules and diffed the frame
   module against the repository. Its full theorem signature and existing docstring are
   byte-for-byte unchanged; the only existing-node edits are `proof`, `proof_deps`, and
   `proof_origin`. There are no definition changes, change records, or forced adaptations.
   The added transparency option affects elaboration of the proof, not its statement.

2. **Proof checked — pass, with one declared lower hole.** Compiled all three modules in
   import order through `lcompile.py`. Read the generator identity and its restriction in
   `DualLocalEvaluation`: `htotal` gives the expansion on every smaller open, naturality
   proves injectivity, and the finite sum of coefficient projections proves surjectivity.
   Read the frame proof: the dual basis transported by `cM.symm` supplies phi and its
   coordinate formula; the two actual sheafification units transport the exterior bases;
   `exteriorPower.basis_apply` supplies both required wedge formulas; a second application
   of evaluation supplies c with precisely the final formula. No axiom, unsafe declaration,
   opaque declaration, external implementation, hollow definition, or internal sorry occurs.
   Scratch `#print axioms` confirms evaluation uses only `propext`, `Classical.choice`,
   and `Quot.sound`; the frame and comparison use those plus the permitted `sorryAx`.
   The sole new sorry is the reported comparison theorem, with its source and complete
   coordinate proof in its docstring. All choices of trivializations are local to proofs of
   propositions; no data definition chooses an arbitrary witness of an unproved existence.

3. **New statements checked — pass.** Read Stacks Tag 0BRT, `lemma-smooth-proper`, at
   https://stacks.math.columbia.edu/tag/0BRT: its final step inverts the determinant, but it
   does not state either new coordinate lemma. The nodes honestly identify these as agent
   expansions of the existing frame proof. Evaluation needs only a finite free restriction,
   and the comparison needs only the same restriction, with no affine or nonzero-ring
   assumption. For r=0 and n>r the exterior index is empty (except n=0); for n=0 it is a
   singleton and restrictions preserve 1. Empty opens have the zero ring and their section
   modules are zero. Each coordinate/gluing argument still works. The remaining comparison
   is strictly the exterior-sheaf part: it supplies no dual sections, dual basis, or evaluation
   equivalence. It is used twice in an actual combining proof, rather than restating the
   frame theorem. Fresh searches used different terms: LeanFinder query "sheafification
   unit is isomorphism on open subset where presheaf is a sheaf" found generic
   `isIso_toSheafify`/`isoSheafify`, which still require the local exterior presheaf to be a
   sheaf; Loogle did not know the upstream-only `PresheafOfModules.homObjEvalId` name.
   A launcher grep for exterior trivializations/comparisons and homObj section equivalences
   found no exact result. Direct rg searches in lean/Sheaf, lean/WeilConjectures, the upstream
   module/sheaf sources, and the pinned Mathlib exterior files found the ring exterior basis,
   the already proved zero/first exterior comparisons and the open-restriction statement,
   but no theorem supplying this finite-free comparison. Closing the general comparison
   requires constructing its natural exterior coordinate isomorphism; it is not a short
   application of any searched result.

4. **Route and pruning checked — pass after repairs.** The three original coordinate steps
   remain: reconstruct dual functionals, compare exterior sections, reconstruct exterior
   dual functionals. `dag/units/sk-thm-picard-duality.json` is untouched (its realized arrays
   are empty on the repository baseline); no unit statement or route was bypassed. All old
   proof dependencies remain direct except the generic sheafification interface, which is
   now transitive through the comparison node. The original internal-Hom import was removed
   by the first worker; corrected the report's inaccurate claim that no import was removed.
   Removed the unnecessary public exterior-basis import from the comparison statement module
   and placed it as a proof-only import of the frame module, where its basis construction
   is used. No module becomes globally unreachable, so the globally pruned list is none.

5. **Nodes checked — pass.** Compared each new `lean.statement` to its declaration and the
   original node to its baseline. The frame node records the actual basis construction,
   local comparison calls and evaluation calls. The evaluation node records the proved
   finite-coordinate argument; the comparison node records the remaining natural exterior
   coordinates and sheafification argument. In each node `proof_deps` is the union of the
   step uses, and `proof_origin` identifies the relevant old coordinate steps. New nodes have
   the item's chapter and unit, creation/Lean records, source, three recorded search kinds
   (the unavailable service is marked unavailable), and blueprint ancestry. No new node
   duplicates the original frame statement.

Second-reading changes: repaired import visibility/placement, added source and blueprint
references to the two new module docstrings, corrected the removed-import report, and wrote
this independent review. The mathematical proofs and all theorem signatures were retained.
The delivery closes one original hole and adds one strictly smaller hole: decomposition,
net zero holes. The additional local-dual theorem and its private helper are fully proved.
