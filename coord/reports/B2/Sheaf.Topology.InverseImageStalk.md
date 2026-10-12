## What changed

Proved both declarations of `Sheaf.Topology.InverseImageStalk`, with their signatures
unchanged. Added the proof-only import `Mathlib.Topology.Sheaves.Sheafify`.
Private, fully proved helpers construct the canonical stalk map from the sheaf-adjunction
unit, compute its germ formula, prove it is an isomorphism, and establish naturality.
The isomorphism proof compares the abstract pullback adjunction with the explicit
sheafified-presheaf construction using `Adjunction.leftAdjointUniq`, then uses
`Presheaf.stalkPullbackIso` and `Presheaf.stalkFunctor_map_unit_toSheafify_isIso`.
The original stalk element is represented using `Presheaf.exists_germ_eq`; the germ
formula and the inverse-isomorphism identity prove the last clause in both categories.

Updated the existing node's proof, proof dependencies and proof origin to match.
Added `coord/changes/InverseImageStalkScopedHelpers.md` for the static checker's
conservative flag on new locally scoped proof-helper commands; no public API changes.
The item is not a realized statement or step of `sk-thm-reduction`; its route is preserved.
Local compilation passes cleanly. The delivery dry run checks the server and axioms.
Searches ran through msearch: LeanFinder for pullback stalks, Loogle for
`TopCat.Presheaf.stalkPushforward`, and grep for stalk preservation by sheafification.
Also read the related explicit/abstract adjunction comparison in
`WeilConjectures.Topology.Sheaves.SpectralRestriction`.

## Proved and sorry left

- `TopCat.Sheaf.exists_inverseImage_stalk_iso_ab`: proved.
- `TopCat.Sheaf.exists_inverseImage_stalk_iso_commRing`: proved.

No sorry remains in the module; none is introduced elsewhere. No new axioms,
public signatures, or definitions used by other modules are introduced or changed.

## No longer needed

Removed the proof-only import `Sheaf.Topology.PresheafModuleStalkFunctor`.
Its declarations (including `stalkMap_linear`, `stalkMap_id` and `stalkMap_comp`)
are not needed on this branch: ordinary Mathlib presheaf stalks suffice.
The node `def-weil-pbc-module-stalk` remains as the existing definition/germ-reference
node; the project's module-valued stalk functor is not used.

Removed proof dependency `lem-weil-pbc-filtered-colimit-algebras-elementwise`:
`Presheaf.exists_germ_eq` applies directly to commutative rings, so the route through
commutative integer algebras is unnecessary. This is a Mathlib leaf, not a project
module to import. No other planned stalk-isomorphism or sheafification dependency
is pruned. All original public imports supply statement notation or category/limit
instances and are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The plan's representation argument for rings
was longer than needed. The abstract sheaf pullback must be compared with the explicit
construction, rather than treated as definitionally the same adjunction. The proof
handles this comparison and unit compatibility explicitly.

The local literature checkout does not contain `literature/stacks-project/sheaves.tex`;
read the cited Stacks statements online at https://stacks.math.columbia.edu/tag/008H
and https://stacks.math.columbia.edu/tag/008O. The mathematical route is unchanged.

## Second reading by B2

1. Compared the sole delivered Lean module against the repository using `diff` and
   separately compared both existing theorem signatures byte for byte: identical.
   The added map and natural isomorphism are private proof helpers; no existing
   definition or public signature changes. The proof-only Sheafify import is plain
   `import`. The scoped-helper change record accounts for the static scope flags.
   Verdict: pass.
2. Compiled the module locally without warnings or errors. Searched the delivered
   source for sorry, axiom, unsafe, opaque, implemented_by, extern and kernel-check
   bypasses: none. Compiled a scratch copy with `#print axioms` for both public
   theorems: exactly propext, Classical.choice and Quot.sound, with no sorryAx.
   Read the private helpers: the canonical map is induced by the unit; equality
   with the explicit presheaf/sheafification composite is checked on all germs
   using unit compatibility, so cancellation gives a genuine isomorphism.
   Naturality follows from unit naturality, and applying the inverse to an element
   before exists_germ_eq proves the representation clause. Verdict: pass.
3. No statements are split off and no sorry remains. The generic helpers are fully
   proved and private, and are neither axioms nor renamed restatements with sorry.
   Checked Mathlib's stalkPullbackIso, stalkFunctor_map_unit_toSheafify_isIso and
   exists_germ_eq at their definitions. The argument also covers identity maps,
   one-point spaces and zero objects; an empty source has no point x to consider.
   Verdict: pass; no new-node obligations.
4. Read downward from both existential theorems through the shared helpers. The
   proof takes the existing Mathlib isomorphisms directly. Searched the library
   for stalk comparisons and adjunction uniqueness with rg, and performed a fresh
   msearch grep for the combined sheaf-adjunction/stalk route. Related proofs in
   SpectralRestriction and SpectralClosedRestriction use the same comparison;
   no existing generic sheaf-level theorem supplies all the requested clauses.
   The removed module-valued stalk import is unused; its definition node remains
   only for the Mathlib stalk/germ part of its match. The sole removed proof edge
   is lem-weil-pbc-filtered-colimit-algebras-elementwise, already listed under
   No longer needed. Reviewed sk-thm-reduction.json: this item realizes neither
   its statement nor any step, and no unit route or realized field changes.
   Verdict: pass.
5. Compared the delivered node with the repository. Only proof, proof_deps and
   proof_origin change. The proof dependencies equal the union of the steps'
   uses, and their Mathlib matches are precisely the inverse-image construction,
   presheaf stalk comparison, both sheafification instances and stalk/germ facts
   used in Lean. The proof text explains the adjunction comparison and direct
   germ representation. No new nodes. Verdict: pass.

Second reading changed only this report: the proofs and node metadata needed no
repair. Scratch axiom checks are not part of the delivery.
