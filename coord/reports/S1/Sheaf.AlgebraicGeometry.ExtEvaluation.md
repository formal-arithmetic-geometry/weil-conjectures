## What changed

Proved `AlgebraicGeometry.Scheme.Modules.dual_tensor_hom_iso` in
`Sheaf.AlgebraicGeometry.ExtEvaluation`, with its signature unchanged. The proof takes
`e G := asIso (dualTensorHom F G)` using the existing source-library
`isIso_dualTensorHom_of_isFiniteLocallyFree` instance; the hom equality is reflexivity,
and naturality is `dualTensorHom_naturality_right F g` reversed. Updated the existing
node's proof, proof dependencies and proof origin to record this route. No new statements
or definitions were needed. The unit record `sk-thm-picard-duality` has no realized nodes
in its statement or steps; its route is unchanged.

The existing public import `WeilConjectures.AlgebraicGeometry.Modules.HomTensor` suffices.
Removed four redundant private proof imports listed below.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Modules.dual_tensor_hom_iso`
(node `lem-sc-ext-evaluation`): 1 of 1 original sorries closed. No sorry remains in the
item and no new sorry is introduced. Local compilation passed without warnings.
A compiled `#print axioms` probe reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed direct imports:
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`

The old proof-only dependency nodes no longer need separate invocation by this wrapper:
`def-amb-finite-locally-free-module`, `def-pur-sheaf-tensor-product`,
`def-pur-sheaf-hom`, `def-pur-sheaf-modules-hom-module`,
`def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-site-sheafification-iso-locally-bijective`, and
`def-weil-presheaf-modules-sheafification`.
The first five remain statement dependencies, and the underlying notions and some
source-library implementations remain transitively imported. This is removal of
redundant direct dependencies, not a claim that every such module is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The old search record missed the exact source-library results:
`isIso_dualTensorHom_of_isFiniteLocallyFree` and `dualTensorHom_naturality_right` in
`WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree` (lines 46 and 29).
Both are already proved. Their hypothesis allows varying finite local ranks, and the
coefficient module is arbitrary; no constant-rank or quasi-coherence assumption is added.
The rank-zero case and disconnected schemes require no extra case split because the
existing instance has exactly this generality.

Searches run: LeanFinder for evaluation of a finite locally free module returned related
Mathlib sheaf and condensed-module APIs, without an exact match; Loogle for
`CategoryTheory.asIso` returned `asIso` and `asIso_hom`; the launcher grep service returned
zero matches, while direct `rg` in the source library found both exact results above.
The literature blueprint files are not present on this machine; the repository node and
unit record and the complete source-library Lean proofs were read instead. No new
mathematical argument or unproved intermediate lemma is being introduced.

## Second reading by S1

1. PASS: compared the sole delivered module against the repository with `diff` and
   checked the theorem signature byte for byte. The only Lean changes are replacing
   its proof and deleting four private imports. The public import, docstring, universe,
   hypotheses, canonical-map equality, and naturality conclusion are unchanged. No
   definition or statement change record is required.
2. PASS: independently compiled the module and its scratch copy containing
   `#print axioms AlgebraicGeometry.Scheme.Modules.dual_tensor_hom_iso` through
   `lcompile.py`. Both compile cleanly; the axiom list is exactly `propext`,
   `Classical.choice`, and `Quot.sound`. The module contains no sorry or forbidden
   declaration. The `asIso` hom equality reduces definitionally, and the final
   equality is the symmetry of the existing naturality lemma.
3. PASS: no statements were split off and no new declarations or nodes were added.
   Read `HomTensor/LocallyFree.lean` in full and the finite-free calculation in
   `HomTensor/Free.lean`; the reused instance assumes finite local generators of F,
   not invertibility of G or constant rank. Its local calculation admits an empty
   finite basis (rank zero), rank one, and different ranks on disconnected opens;
   G is arbitrary throughout. Direct searches in the source confirm that both
   reused declarations already exist, so no duplicate helper is needed.
4. PASS: the proof directly reuses the proved source instance and naturality lemma,
   with no lower holes. The sole remaining public import is used by the signature
   and re-exports both results. Checked all seven old proof dependencies against
   `No longer needed`: every removed dependency is listed. This prunes direct
   dependency edges, not necessarily globally reachable modules. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists
   are empty, and the reused source proof follows the original local evaluation
   and sheafification route; no realized unit step is bypassed.
5. PASS: compared the node JSON against the repository. Only `proof`, `proof_deps`,
   and `proof_origin` differ. Its two steps accurately name the existing Lean
   results and the elementary packaging and symmetry performed by this wrapper;
   there are no new DAG dependencies. The node statement and Lean record are
   unchanged and agree with the theorem, including variable local rank and
   naturality for every coefficient morphism.

Second reading changed only this report by adding the independent review. No repair
of the proof or node was necessary. One original hole is closed and zero holes are
added; this is a proof, not a decomposition.
