## What changed

The existing signature and docstring of
`AlgebraicGeometry.Scheme.Modules.nonempty_algebraModule_presentation_over` are unchanged.
Its proof now obtains global generating sections, proves the underlying kernel is
quasi-coherent, obtains generating sections of that kernel, and assembles the existing
Mathlib `Presentation` structure. This is a genuine generation/kernel reduction.

Removed the proposed auxiliary cokernel-data module and node: that statement encoded
an entire presentation and was not a strictly smaller obligation. Added two modules:
`Sheaf.AlgebraicGeometry.AffineAlgebraModuleGenerators` (global generation only) and
`Sheaf.AlgebraicGeometry.AffineAlgebraModuleKernel` (proved underlying kernel closure).
The returned landing found two private helper statements identical to private helpers
in `Sheaf.AlgebraicGeometry.QuasiCoherenceScalarRestriction`. Importing that module is
impossible here: it imports the presentation module, forming a cycle, and the helpers
are private. Used the return's permitted generalization route in the new kernel module:
`scalarRestriction_preservesLimitsAndColimits` establishes simultaneous preservation,
sharing the forgetful-functor argument; `quasiCoherent_slice_iff_open` proves the full
bidirectional equivalence for an arbitrary slice module. Removed all four previous
one-direction helpers. The kernel proof extracts both preservation results and uses
both implications of the quasi-coherence equivalence. No existing library module is
adapted, and all existing public signatures are unchanged.

All added imports used only by proofs are plain imports. There are no existing
statement, definition, visibility, or public-import changes, and no change records.

## Proved and sorry left

Closed the item's one direct hole:
`AlgebraicGeometry.Scheme.Modules.nonempty_algebraModule_presentation_over`.
Added one lower hole:
`AlgebraicGeometry.Scheme.Modules.nonempty_affine_algebraModule_generatingSections`
(node `lem-weil-pbc-affine-algebra-module-generators`). This is the only `sorry`
in the delivered files. It asserts existence of global generators, not a presentation,
and its docstring gives the full fraction/local-surjectivity argument.

The newly stated
`AlgebraicGeometry.Scheme.Modules.affine_algebraModule_kernel_isQuasicoherent`
(node `lem-weil-pbc-affine-algebra-module-kernel`) is proved, with only `propext`,
`Classical.choice`, and `Quot.sound`. Its generalized private preservation and slice-equivalence
helpers are proved. The item still depends on the generation hole, so it is a
**decomposition, not a completed proof**: one existing hole closed, one new hole added,
net zero before the maintainer's import-closure ledger calculation. No library definition
chooses data from an unproved existence theorem; the two Nonempty eliminations are in
the proof of a proposition only.

Local compilation of all three modules succeeds without warnings. A scratch-copy
`#print axioms` confirms the kernel theorem has only the three standard axioms; the
item and generation theorem additionally have `sorryAx`, as expected. The delivery
wrapper runs its full constant-level probe as well.

## No longer needed

Retired the proposal's duplicate private helpers `scalarRestriction_preservesColimits`
and `quasiCoherent_open_to_slice`, and their separate companions
`scalarRestriction_preservesLimits` and `quasiCoherent_slice_to_open`. Their obligations
are handled together by the two generalized helpers. No extra library import was added.

Removed the direct proof imports `Mathlib.AlgebraicGeometry.Modules.Tilde` and
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful` from the item. The latter is
now used in the kernel module; the former is the mathematical API for the remaining
generation obligation, not needed for the item's categorical assembly.

Every old direct proof dependency is accounted for:
`lem-weil-pbc-module-sheaves-colimits-forgetful` is now used by the kernel node;
`lem-weil-pbc-module-restriction-open-immersion-colimits` and
`lem-weil-pbc-affine-tilde-gamma-adjunction` remain in the generators node's proof plan.
Thus none is claimed globally pruned. The item now directly depends on the two new
nodes. No existing DAG node or module is asserted unreachable from the targets.
The unlanded `AffineAlgebraModulePresentationAux` and its circular node were deleted
from this proposal; they are not counted as library pruning.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two already-stated private helpers. They did mean the
same thing; differing binders or opens were not the cause. Generalized them in place as
allowed by the return, without importing their downstream owner or changing its private
interfaces. `tools/import_prune_check.py` now accepts the new kernel module. The updated
kernel node describes the generalized argument. The second reading below records the
prior delivery; the repaired helper proofs require the next independent reading.

The first reader's claim that existential free cokernel data is strictly weaker than
a presentation was wrong. Mathlib provides both `presentationOfIsCokernelFree` and
`Presentation.isColimit`, showing those encodings express the same obligation. Its
new node also cited the item itself in proof_deps, creating a circular mathematical
plan. The original item node was not updated to the first worker's proof.

The replacement isolates generation from kernel quasi-coherence, closes the latter
using the upstream `isQuasicoherent_sigma` and `isQuasicoherent_kernel`, and updates all
three node plans. No unit or chapter route is altered.

Sources were checked directly: [Stacks 0H88](https://stacks.math.columbia.edu/tag/0H88)
constructs the affine free presentation from sections;
[Stacks 01IC](https://stacks.math.columbia.edu/tag/01IC) proves kernel closure via tilde
exactness. The local literature checkout lacks the tex files, so these source pages
were read instead. Existing DAG source identifiers are retained.

## New nodes

`lem-weil-pbc-affine-algebra-module-generators`: arbitrary algebra scalars on the affine
slice, underlying quasi-coherence implies global generation. No quasi-coherence of A
is needed for this first half. The statement covers arbitrary modules on the slice so
it applies also to the kernel. It is true for the zero module and empty affine open:
zero generators suffice; neither finiteness nor a nonempty-open assumption is added.

`lem-weil-pbc-affine-algebra-module-kernel`: a map from any free algebra-module sheaf
into an underlying quasi-coherent module has underlying quasi-coherent kernel when A
is quasi-coherent. It is proved for any open, without an affine or epi hypothesis.
It covers empty generator types, zero maps, and the empty open. Its proof uses the
existing library kernel and coproduct lemmas rather than restating those facts.

Both nodes have complete Lean records, natural-language proofs, source records,
four actual searches (LeanSearch unavailable; LeanFinder, Loogle, grep), and matching dependency unions.
Searches were also repeated with independent words, and `rg` checked the upstream and
project modules. No exact algebra-scalar statement on the slice was found. Existing
scheme-module kernel/coproduct matches were used in the kernel proof.

## Earlier second reading (a previous round; superseded)

1. **Interface: PASS.** Compared the item with the repository using `diff` and the
   declaration parser. Its existing declaration's signature is byte-for-byte unchanged,
   as is its docstring. Only its proof and plain proof imports change. There are no
   definition changes or adaptations of other existing modules.
2. **Proof and axioms: PASS with the declared remaining hole.** All delivered modules
   compile cleanly. Scanned for forbidden declarations and hollow definitions; none.
   The sole remaining sorry is the whole named generation theorem. Scratch-copy axiom
   checks give exactly the standard three for kernel closure, and standard three plus
   sorryAx for the item and the stated generation obligation.
3. **Split statements: PASS after repair.** Rejected the entire cokernel restatement
   and replaced it with the generation-only statement. It is a proper part of the
   argument and is used twice, with the genuinely proved kernel theorem linking the
   two uses. Checked zero modules, empty opens, arbitrary indexing types, zero maps,
   and scalar-restriction compatibility. Searches and upstream inspection found the
   kernel/coproduct route used above, not an existing complete scalar-generation result.
4. **Top-down route and pruning: PASS.** The real proof assembles generators and
   relations, and the kernel subproblem is discharged by proved upstream declarations.
   Imports are limited to statement dependencies and actual proof APIs. All three old
   proof dependencies are explicitly accounted for under No longer needed. Read
   `dag/units/sk-thm-p1.json` including realized: this auxiliary algebra lemma lies below
   the unit's proper-base-change steps; none of those realized nodes or routes changes.
5. **DAG alignment: PASS after repair.** The item now cites the two actual intermediate
   nodes. The generator node has no back-edge to the item; its blueprint ancestry is
   provenance only. Kernel proof_deps name forgetful colimits, coproduct closure, and
   kernel closure, matching the proof. New statement and Lean signatures agree.

Second reading changed: removed the circular equivalent restatement; wrote the true
recursive generation/kernel reduction; proved kernel quasi-coherence; supplied the
new nodes and actual searches; updated the item plan; pruned two direct proof imports;
corrected the progress claim to decomposition with one remaining lower hole.


## Second reading by G1

1. **Interface: PASS.** Read every delivered Lean file and diffed the existing
   presentation module against the repository. The existing signature and docstring
   are byte-for-byte unchanged; the diff changes only two plain imports and the proof.
   The other two modules are new. No existing definition, public import, visibility,
   or target statement changes; no change record is required.
2. **Proof: PASS with the declared generation hole.** Independently compiled all three
   modules through lcompile.py. Scanned every file: no forbidden declarations, no
   hollow definition, and exactly one whole-theorem sorry, in
   nonempty_affine_algebraModule_generatingSections. Separate scratch-copy #print axioms
   checks show the standard three axioms for affine_algebraModule_kernel_isQuasicoherent;
   the generation and presentation declarations additionally use sorryAx. Read the
   generalized preservation helper: reflection is used only after preservation of
   both abelian-sheaf composites is established. Read both directions of the slice
   equivalence, including its unit isomorphism. The kernel proof uses preservation
   of coproducts for the source, the hypothesis for the target, then the proved
   upstream kernel theorem; it does not assume its own conclusion.
3. **Split statements: PASS.** Read Stacks 0H88 and 01IC directly and checked each
   hypothesis of both new statements against the arguments. Global generation uses
   only underlying quasi-coherence and affineness: on D(f), m/f^n is obtained from
   the generator m by the image in A(D(f)) of f^(-n). This works without A being
   quasi-coherent. Kernel closure needs hA for the free source and hM for the target,
   but neither affineness nor epi. Empty opens and zero modules are generated by
   the empty family; empty free sources and zero maps satisfy kernel closure.
   The generation statement is strictly one part of a presentation and is applied
   twice with proved kernel closure between the applications. Repeated searches
   with independent words: LeanFinder "quasi coherent sheaf on affine scheme is
   generated by its global sections" found local-generator APIs only; Loogle
   "SheafOfModules.GeneratingSections, SheafOfModules.restrictScalars" found no hits;
   grep "fromTildeΓ|presentationOfIsIsoFromTildeΓ|generatorsOfIsCokernelFree" found
   ordinary structure-sheaf presentations and cokernel APIs. Also searched the
   project and upstream Modules files. presentationOfIsIsoFromTildeΓ gives ordinary
   O-module generators, not the required arbitrary-algebra slice statement; there
   is no direct replacement that closes the remaining theorem in a few lines.
4. **Route and pruning: PASS.** The item uses the actual Mathlib Presentation
   constructor, whose two fields are generators and kernel generators. The new
   kernel proof uses the existing isQuasicoherent_sigma and isQuasicoherent_kernel
   rather than splitting those proved facts again. Imports are statement APIs or
   used proof dependencies; proof imports are plain. Verified all three old
   proof_deps against the No longer needed accounting: forgetful colimits moves
   to kernel closure; affine tilde and open restriction remain in the generation
   plan. No globally pruned module is claimed. Read sk-thm-p1.json, including its
   realized statement and all steps: this auxiliary algebra argument changes none
   of the curve calculations, henselian comparison, or stalk exchange route.
5. **Nodes: PASS.** The existing node changes only proof, proof_deps, proof_origin.
   All three dependency lists equal the unions of the steps' uses. Matched the new
   Lean records with their declarations, source records, docstring arguments,
   creation records, blueprint ancestry, chapter/unit, and recorded searches.
   Presentation cites generators and kernel; neither cites presentation as a
   proof dependency. The repaired generalized private helpers introduce no new
   holes or nodes. The new kernel plan matches both preservation instances and
   both directions of slice/open transport as written.

Second reading changed: added the missing module docstring to the new generator
module; repeated compilation, independent searches, and axiom checks; appended this
review. No proof or statement repair was needed. The progress classification remains
one original hole closed and one lower hole added: a decomposition with net zero,
not a sorry-free proof of the presentation target.
