## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_generators` from an
explicit affine global-generating-family construction and a new compact-selection
lemma. The original theorem signature and visibility are unchanged.

The private, fully proved `exists_affine_generatingSections` restricts H along
`V.fromSpec`, uses the quasi-coherent affine counit and `presentationTilde` on all
module elements, and transports its generators back to `H.over V` through
`presentationRestrictOpensRange` and `presentationOverOfRestrict`.
The main theorem obtains a finite subfamily, enumerates its finite subtype by
`ULift (Fin (Fintype.card S))`, maps that equivalence through `freeFunctor`, and
composes its isomorphism with the selected epimorphism. Restriction preserves the
isomorphism and epimorphic composition finishes the proof.

Added proof-only imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Sheaf.AlgebraicGeometry.ModuleGeneratingSectionsCompactSelection`. Added the selection module
and its DAG node,
and updated the original node's proof, proof_deps and proof_origin.
No existing public signature, definition, public import or visibility changed.

All delivered modules compile individually in dependency order through lcompile.py.
The import-direction check permits the source-library import. Empty selected
families reindex to Fin 0; no nonempty-open or positive-rank hypothesis is introduced.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_generators`
(node `lem-weil-pbc-module-finite-type-affine-generators`). Its module has no sorry.
The private helper `exists_affine_generatingSections` is also fully proved.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_finset_generatingSections_on_compact`
(node `lem-weil-pbc-module-generating-sections-compact-selection`) in
`Sheaf.AlgebraicGeometry.ModuleGeneratingSectionsCompactSelection`.
Its whole proof is `by sorry`, with its source and complete argument in the docstring.
This is a decomposition: one hole closed and one hole added, net zero. It does
not establish an unconditional sorry-free proof of the original theorem.
The remaining lemma assumes a specified global generating family, selects from
that family, and assumes neither affineness nor quasi-coherence. Thus it isolates
the compactness argument and leaves out the proved affine construction and finite
reindexing; it is not the original statement under another name.

## No longer needed

The planned affine finite-type criterion
`lem-weil-pbc-quasi-coherent-finite-type-affine` and its module
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` are no longer needed by
this theorem's proof. No proof import of that module was added. The new route also
avoids principal-open refinement, localization generators, and numerator clearing.

The original direct proof dependency `def-weil-pbc-quasi-compact-scheme` also leaves
the item node: its compactness argument now belongs to the new selection node, which
still depends on it. Thus compactness is retained transitively, not pruned from the
full proof. These are exactly the two entries removed from the old `proof_deps`.

The second reading removed the redundant newly added proof import
`Mathlib.Data.Fintype.EquivFin`: the remaining imports already expose `equivFin`,
and the complete proof compiled without this import.

No baseline imports were removed: the original module imported only
`Sheaf.AlgebraicGeometry.Coherent`, which its unchanged statement still needs.
The affine tilde adjunction, associated-sheaf construction, module category,
finite-type definition, and restriction machinery remain needed. Compactness
remains needed by the new selection lemma. No assertion is made that any module
has disappeared from the whole targets' import closure.

The node is below unit sk-thm-p1; it is not one of the unit's realized statement or
step nodes. The unit's realized statement and steps are retained unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original principal-localization plan is valid,
but its affine finite-type criterion is unnecessary for the shorter route above.
The standard global presentation already supplies generators on V even when H
is not of finite type on V; compactness selects a finite subfamily on K.

Lean requires an explicit `H' : X.Modules := H` annotation before field notation
`restrict` can find the scheme-module declaration on the moduleRings carrier.
The existing signature itself is definitionally compatible and was not changed.

The Stacks source files were absent locally. Sources were read directly at
https://stacks.math.columbia.edu/tag/01PF,
https://stacks.math.columbia.edu/tag/01BB, and
https://stacks.math.columbia.edu/tag/01B8.
LeanSearch was unavailable (Internal Server Error); this is recorded without an
absence verdict. LeanFinder and source grep found no compact-selection theorem.
The blueprint search for 01BB returned no matching blueprint node.

## New nodes

`lem-weil-pbc-module-generating-sections-compact-selection` states selection of a
finite subfamily from an already specified global generating family on a compact
open where the target is of finite type. Its local finite-support argument and
finite-subcover argument follow Stacks Modules 01BB and 01B8. K empty permits the
empty finset; an empty original index already forces the target to be zero.
Its module is
`lean/Sheaf/AlgebraicGeometry/ModuleGeneratingSectionsCompactSelection.lean`.
No change record or forced consumer adaptation is needed.

## Second reading by R4

1. Compared both delivered Lean files with the repository. The selection module is
   new. In the original module the existing theorem signature, visibility, docstring,
   and public import are byte-for-byte unchanged; only proof imports, a private
   proved helper, and the theorem body were added. No definition changed and no
   change record is needed. Verdict: pass.
2. Compiled both modules in import order with lcompile.py. No compiler errors or
   warnings. Inspected all delivered code: the only sorry is the complete proof of
   `exists_finset_generatingSections_on_compact`, listed above; no forbidden
   declarations or hollow definitions occur. A scratch-copy `#print axioms` showed
   only propext, Classical.choice and Quot.sound for the affine helper, and those
   plus sorryAx for the main theorem and selection lemma. The main proof eliminates
   existential witnesses only inside a theorem; it introduces no data definition
   chosen from unproved existence. Verdict: pass as a decomposition, net zero holes.
3. Read the selection statement, docstring, node, and Stacks
   [01BB](https://stacks.math.columbia.edu/tag/01BB) and
   [01B8](https://stacks.math.columbia.edu/tag/01B8). Finite local generators lift
   through sigma on stalks with finite support, and their identities hold after
   shrinking; compactness then gives a finite union of supports. This works for
   empty K, empty sigma.I, zero H, and K = V, without quasi-coherence or affineness.
   The assertion selects from a specified family, whereas the original theorem
   must first construct one on an affine open. It is a genuine strictly smaller
   step, not a renaming of the target. Repeated LeanFinder search with the wording
   "surjection from an infinite free sheaf ... finitely many summands" and Loogle
   query `SheafOfModules.GeneratingSections, Finset` found no existing selection
   theorem. Targeted source searches checked Mathlib Generators and the source
   library's sheaf generators, and inspected `FiniteGlobalGeneratingFamily` and
   `FiniteSectionsCover`: those require invertibility and do not cover this
   general finite-type assertion. No short existing proof closes the hole.
   Verdict: pass.
4. Read from the target through the private helper to compact selection and finite
   reindexing. The affine helper uses a real presentation by all module elements
   and transports it through actual isomorphisms; its axiom check is sorry-free.
   The final freeFunctor isomorphism and epimorphic composition are appropriate
   even for S empty. Removed the redundant EquivFin proof import after compiling
   without it. Checked the old proof_deps difference and completed No longer
   needed with its compactness entry. Read sk-thm-p1.realized: neither the item
   nor its pruned affine criterion realizes a unit statement or step. No realized
   node or unit route changes. Verdict: pass.
5. Compared the existing node JSON with the repository: only proof, proof_deps
   and proof_origin differ. Its three proof steps match the helper, the selection
   application, and finite reindexing; proof_deps is the union of their uses. The
   new node has the correct chapter, unit, provenance, source, three search kinds,
   statement dependencies, proof plan, and verbatim Lean signature. Its sole
   named sorry matches the report. Verdict: pass.

Changes by the second reader: removed the redundant proof-only EquivFin import;
completed the account of removed direct DAG dependencies; added this independent
review and its compiler, axiom, source, and duplicate-search evidence. No statement,
definition, proof argument, or new hole was changed.
