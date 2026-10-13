## What changed

Completed `AlgebraicGeometry.Scheme.Modules.coherent_local_finite_presentation` with its
original signature. Finite local generators of G give finite free epimorphisms; coherence
makes their kernels finite type. Finite local generators of each kernel then give finite
presentations using restriction, cokernel preservation and `isCokernelEpiComp`. Locality
of finite presentation assembles these data. A covering member containing x supplies the
requested presentation; finite reindexing and cokernel uniqueness produce the displayed
biproduct cokernel isomorphism.

Added proof-only imports of `Mathlib.Data.Fintype.EquivFin`,
`Mathlib.CategoryTheory.Sites.Spaces`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
A private, fully constructed isomorphism handles finite free reindexing. Explicit local
sheafification instances avoid repeated expensive searches on nested slice sites. No
public interface, target signature, or definition used by targets changes.

Updated the node's proof to the implemented covering-and-locality construction, which
follows the argument of [Stacks Tag 01BW](https://stacks.math.columbia.edu/tag/01BW).
The unit's realized statements and steps are preserved. Zero generator and relation ranks
are allowed by finite coproduct reindexing, so the zero module case needs no exception.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.Modules.coherent_local_finite_presentation`
(node `lem-weil-pbc-coherent-local-finite-presentation`). No sorry remains in the item and
no new holes or nodes are added. This is a proof, not a decomposition.

## No longer needed

None: both original public imports are required by the statement. Each added proof-only
import is used. The three existing proof dependency nodes remain needed:
`pqf-def-coherent`, `def-weil-pbc-module-finite-type-presentation`, and
`def-weil-sheaf-of-modules-category`. No module or node is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The inherited report described a cofork split that was absent from the sandbox and would
merely repackage the desired presentation. It has been replaced by this report of the
complete proof. The inherited proof draft timed out because it repeated instance searches
on nested slice sites; caching these instances makes elaboration practical. The final
transport also needed to unfold the relation composite when checking the cokernel square.
No mathematical error in the theorem or its source was found. Search found no shorter
coherent-to-finite-presentation theorem valid for arbitrary schemes: the existing private
helper in `TwistedSectionsFiniteDimensional` additionally assumes locally Noetherian.

## Second reading by G1

1. Compared the delivered module with the repository version. The theorem signature and
   all existing declarations are unchanged; only the proof body, private helper, and
   proof-only imports differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it has no errors, forbidden declarations, or
   unlisted `sorry`s. Axioms of the target are only `propext`, `Classical.choice`, and
   `Quot.sound`. Verdict: pass.
3. Checked the proof against its imported dependencies and searched the local library and
   Mathlib for an existing coherent-to-finite-presentation result. The theorem and its
   finite-index reindexing helper are needed and mathematically valid, including zero
   ranks. Verdict: pass.
4. Checked the proof from the target downward: finite generators, finite-type kernel,
   local presentations, and cokernel transport. All four added imports are used and no
   original import can be removed. Verdict: pass; no pruning.
5. Compared the DAG proof steps and dependencies with the Lean proof. The three stated
   proof dependencies remain used and the unit route through local finite presentations
   is preserved. Verdict: pass.

Changed only the proof implementation and its proof-only imports; no statements,
definitions, nodes, or change records required repair.
