## What changed

Proved `AlgebraicGeometry.RingedSpace.internalHom_germ_eq_zero_of_finiteType`
in `Sheaf.AlgebraicGeometry.InternalHomGermZeroFiniteType`, with its signature and
existing public declaration unchanged. The second reading makes the proof-only
`Sheaf.Algebra.Homology.ModuleStalkFunctor` import plain rather than public. Two proved private helpers extract a finite
family on a neighborhood from Mathlib's covering data and cancel the restricted
free generator epimorphism. The main proof kills the finitely many generator
images on a common open neighborhood and then takes the germ.

The proof follows all three steps of the existing node. It uses Mathlib's
`overMap` left adjoint to preserve coproducts and epimorphisms, the free-sheaf
universal property, naturality, `TopCat.Presheaf.germ_eq`, finite intersections
of opens, and `TopCat.Presheaf.germ_res_apply`. No node route changes or new
imports are needed; only the visibility of one proof-only import changes. The unit's realized statements and steps are unaffected.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.RingedSpace.internalHom_germ_eq_zero_of_finiteType`
(node `lem-weil-pbc-internal-hom-germ-zero-finite-type`).

No holes added; no `sorry` remains in the delivered module. Both private helpers
`finiteType_neighborhood` and `zero_on_generators` have complete proofs.
This is a proof, not a decomposition. The finite-intersection construction
includes the empty family: its infimum is the top open, and the empty free
coproduct still gives the required cancellation.

## No longer needed

None. The existing node's four proof dependencies still describe the proof:
finite type generators, localized restrictions, germs, and internal Hom.
No imports were added or removed. The plain ModuleStalkFunctor
import supplies the `RingedSpace.Modules` abbreviation used by the helpers.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The plan's restriction/cancellation step requires
preservation of the free coproduct as well as the epimorphism; Mathlib's
`SheafOfModules.overMap` left adjoint and `isColimitOfPreserves` provide both.
The theorem follows the original plan without changing any statement.

Searches: leanfinder for a finite-type local morphism with zero stalk map,
loogle for `SheafOfModules.GeneratingSections`, and grep for
`germ_eq|GeneratingSections|IsFiniteType`, plus direct searches of the source
library, Mathlib, and DAG. No direct internal-Hom zero-germ theorem was found;
Mathlib's generator and germ APIs suffice.


## Second reading by B2

1. Compared the only delivered module with the repository using `diff` and
   independently compared the complete existing theorem signature byte for byte.
   Verdict: unchanged hypotheses, conclusion, universes, and public declaration;
   no definitions changed. The import-visibility change is documented in
   `coord/changes/InternalHomGermZeroFiniteType_ModuleStalkFunctor_import.md`.
2. Compiled the original submitted proof locally with `lcompile.py` (43.4 seconds,
   no errors or warnings). Scanned the complete module: no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, or skipped kernel checking.
   Checked the finite-cover extraction, restricted coproduct universal property,
   preservation and cancellation of the generator epimorphism, naturality,
   finite intersection, and compatibility of germs. The empty family uses top
   as its intersection; an empty space has no point to consider. The repaired file compiled in a scratch
   copy (53.7 seconds); `#print axioms` for the main theorem and both private
   helpers returned exactly `propext`, `Classical.choice`, and `Quot.sound`,
   with no `sorryAx`. Verdict: all three proofs are kernel checked.
3. No statements split off, no new holes, and no new nodes. The two private
   helpers are proved, strictly smaller parts of the argument. Repeated searches
   using leanfinder (local vanishing of a finite-type sheaf morphism) and loogle
   (`SheafOfModules.GeneratingSections, CategoryTheory.Epi`), plus direct source
   searches, found no shorter theorem for this assertion. The ringed-space
   zero-germ lemma concerns structure-ring sections, not module morphisms.
4. All three steps of the existing node are realized by the proof. Read
   `dag/units/sk-thm-p1.json`, including `realized`: the item is a refinement
   below the unit's realized steps and bypasses none of them. The four existing
   proof dependencies remain used, so `No longer needed` is complete. Corrected
   the one proof-only import to plain `import`; it supplies `Modules` only in
   private helper signatures, not in the existing public theorem signature.
5. Read the node and the Lean records or Mathlib match of all four dependencies.
   Verdict: the original `proof`, `proof_deps`, and documentary `proof_origin`
   describe the implemented route; no node edits or additions are necessary.

Second-reading change: made `Sheaf.Algebra.Homology.ModuleStalkFunctor` a plain
import. No mathematical proof changes were needed. Closed one original hole,
added zero holes, and pruned no modules.


The first dry run required a change record for the public-to-plain import edit.
Added `coord/changes/InternalHomGermZeroFiniteType_ModuleStalkFunctor_import.md`
with the old and new import, all 1053 transitive downstream users, their claim
holders, and the reason no adaptation is needed: the sole direct importer,
`Sheaf.AlgebraicGeometry.FinitePresentationStalkKernel`, already publicly imports
`ModuleStalkFunctor` itself. No statements or definitions changed.
