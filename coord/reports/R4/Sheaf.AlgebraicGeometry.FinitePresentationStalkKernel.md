## What changed

Completed the existing sandbox attempt for
`Sheaf.AlgebraicGeometry.FinitePresentationStalkKernel`. The signature and visibility of
`AlgebraicGeometry.RingedSpace.exists_finitePresentation_stalk_kernel` are unchanged.
Its proof now combines three strictly separate intermediate statements with the existing
canonical stalk evaluation and Mathlib's left exactness of linear Hom. The range calculation
first proves `range ε = ker α` algebraically and then uses
`LinearMap.range_comp_of_range_eq_top` to transfer it to `β = ε.comp c`.
The proof also checks injectivity and the formula on arbitrary representative neighborhoods.
No data definition is added, and no target or other existing module is changed.

Three new modules state the remaining work: `FinitePresentationSourceStalk`,
`InternalHomGermZeroFiniteType`, and `StalkLinearMapLocalLiftFinitePresentation` under
`Sheaf.AlgebraicGeometry`. Each has one public theorem with its complete proof in words,
source, and matching new node. Added ordinary proof imports of these three modules,
`StalkInternalHomEvaluation`, and `Mathlib.LinearAlgebra.LeftExact` to the item's module.
Updated the item's DAG proof, proof dependencies and proof origin to the actual route.
Existing public imports are unchanged. The source-stalk module does not import internal Hom;
the zero-germ module imports Generators rather than the larger Quasicoherent module.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.RingedSpace.exists_finitePresentation_stalk_kernel`
(node `lem-weil-pbc-finite-presentation-stalk-kernel`). Its complete Lean proof compiles
from named intermediate statements; this is a decomposition, not an axiom-free proof
of the geometric result. There are no remaining direct sorries in the item's module.

Added three holes, all entire proofs of public named theorems in separate new modules:

- `AlgebraicGeometry.RingedSpace.exists_finitePresentation_source_stalk`
  — `lem-weil-pbc-finite-presentation-source-stalk`.
  It constructs only the source presentation; it has no target sheaf, evaluation map,
  internal-Hom injectivity or coordinate kernel conclusion.
- `AlgebraicGeometry.RingedSpace.internalHom_germ_eq_zero_of_finiteType`
  — `lem-weil-pbc-internal-hom-germ-zero-finite-type`.
  It detects a zero germ using only finite type, without finite presentation or any
  surjectivity or kernel conclusion.
- `AlgebraicGeometry.RingedSpace.exists_local_internalHom_of_stalkLinearMap`
  — `lem-weil-pbc-stalk-linear-map-local-lift-finite-presentation`.
  It lifts one specified linear map locally; it asserts no uniqueness, injectivity,
  comparison equivalence, source presentation or coordinate kernel equality.

Thus one hole is closed and three are added: net minus two before any closure pruning.
No claim of net sorry progress is made. The proof combines the parts by germ comparison,
injectivity of composition, left exactness, and the range-of-composition lemma.

Compilation: the earlier four-module set compiled, the revised parent compiled, and the
final set is checked by `lcompile.py --all` and the delivery dry run with the axiom probe.
The only permitted remaining nonstandard proof assumption is the recorded `sorry` in each
new theorem. Empty finite index sets, zero source, zero target and zero stalk ring cause no
exception: finite intersections over empty families require no shrinking; the free
zero-rank module is zero; the algebraic exactness proof works uniformly. No inhabitedness,
nonzero-ring, coherence, noetherianity or affine hypothesis has been added.

## No longer needed

Removed the direct proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel`
  (`lem-weil-pbc-sheaf-hom-finite-presentation-kernel`). The new route proves the
  evaluation kernel via lifting generator images and killing finitely many relations.
  None of the delivered intermediate nodes uses this sheaf coordinate theorem either.
- `Sheaf.Algebra.Homology.ModuleStalkExact`
  (`lem-weil-pbc-module-stalk-exact`). It is unnecessary in the item's completed Lean
  proof but remains needed below, for the source-stalk presentation and its local lift.
  This is removal of a direct import, not a claim that the result is globally pruned.

The original direct dependencies `def-weil-pbc-module-finite-type-presentation`,
`def-weil-pbc-module-stalk`, `def-pur-sheaf-hom` and `def-pur-localized-ringed-site`
are now accessed through the intermediate arguments, rather than used directly as
proof steps of this node. They are still needed below and are not globally pruned.
`lem-weil-pbc-module-hom-left-exact` remains needed and is discharged by the existing
Mathlib declarations, without a new statement module. No module listed in a blueprint
unit's `realized` statement or proof steps is bypassed. All existing public imports of
the item are retained because they form its statement interface.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had four compiling modules but no node files or report,
so it was not reviewable as a delivery. Its algebraic combination was sound; this
session separated the range calculation and supplied the missing records.

The original DAG suggested transporting the categorical finite-product internal-Hom
kernel through restriction and stalks. The delivered proof instead spells out the
finite-type zero-germ argument and finite-presentation local-lift argument, then uses
linear Hom exactness. This changes only the route below the unit level. The local lift
is proved in words by choosing representatives for finitely many generator images,
killing finitely many relation images after shrinking, and descending through the
cokernel; it must not be proved by importing the higher comparison theorem.
`StalkInternalHomFinitePresentation` already imports this item and cannot be used here.
The higher comparison result is not imported or used by any delivered module or node.

The referenced local `literature/stacks-project/modules.tex` is absent on this machine.
Read the primary source directly at https://stacks.math.columbia.edu/tag/01CP and the
finite-presentation definition at https://stacks.math.columbia.edu/tag/01BN. Source
references retain the project's canonical literature path and tag. LeanSearch returned
Internal Server Error; its searches are recorded as unavailable, without a mathematical
verdict. LeanFinder, Loogle, local Mathlib/library grep, and the existing 01CP DAG nodes
were checked. No existing node states any of these three restricted intermediate claims.

## New nodes

`lem-weil-pbc-finite-presentation-source-stalk` in
`dag/nodes/sec-proper-base-change/` records the source-stalk portion of Tag 01CP, with
finite-rank coordinate identification and the basis-image formula. Its module is
`Sheaf.AlgebraicGeometry.FinitePresentationSourceStalk`.

`lem-weil-pbc-internal-hom-germ-zero-finite-type` in the same directory records the
second paragraph of Tag 01CP. Its module is
`Sheaf.AlgebraicGeometry.InternalHomGermZeroFiniteType`.

`lem-weil-pbc-stalk-linear-map-local-lift-finite-presentation` in the same directory
records the representative-level lifting part of the finite-coordinate kernel
argument in Tag 01CP. Its module is
`Sheaf.AlgebraicGeometry.StalkLinearMapLocalLiftFinitePresentation`. The natural-language
proof includes the finite relations and cokernel descent, so it does not merely invoke
the higher stalk comparison under another name.

All three inherit the item's chapter and unit and insert the item in the blueprint
ancestor chain. Each has three kinds of search, a self-contained statement, numbered
proof steps, exact signature record and whole-proof sorry. There are no change records,
because no existing statement, definition, visibility or public import was changed.


## Second reading by R4

Independent second reader, 2026-10-13. I did not write this proof.

1. **Interface: pass.** Read the four delivered modules and compared the existing
   module with the repository using `diff -u`. Only its ordinary proof imports and
   theorem body changed. The existing signature, visibility, public imports and
   docstring are byte-for-byte unchanged. No definition or target is changed, and
   no forced adaptation or change record is needed. The original docstring describes
   the old planned route; the actual replacement route is recorded above and in the DAG.
2. **Lean proof and axioms: pass as a decomposition.** Compiled all four modules
   in import order with `lcompile.py --all`, without errors or warnings. Read the
   combination: zero-germ detection gives injectivity of canonical evaluation,
   local lifting gives surjectivity, and linear Hom exactness gives the coordinate
   kernel. Restriction to the intersection verifies the formula for arbitrary W.
   A scratch copy with `#print axioms` for all four public theorems compiled and
   reported exactly `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` for each.
   There are precisely three direct sorries, each the whole proof of its documented
   public theorem, and none in the item. No forbidden declarations or hollow data
   definitions were added. Existential witnesses are used inside a theorem proof;
   no arbitrary witness from an unproved existence theorem defines public data.
3. **Split statements: pass.** Checked each signature against its node, its complete
   docstring argument, and Stacks Tags [01CP](https://stacks.math.columbia.edu/tag/01CP)
   and [01BN](https://stacks.math.columbia.edu/tag/01BN). The source presentation,
   finite-type zero-germ detection, and lifting one specified stalk-linear map
   are separate parts of the argument, not renamed copies of the full item.
   On a one-point space they reduce to a finite module presentation, detection of
   a zero homomorphism, and representing the specified homomorphism itself.
   Empty generator/relation families, zero source/target, and a zero stalk ring
   are compatible with these arguments; an empty space has no input point x.
   Repeated LeanFinder searches with different wording for each of the three claims
   found presentation constructors and individual germ lemmas, not these results.
   Loogle's exactness/surjectivity/LinearMap search found algebraic exactness lemmas
   rather than a sheaf-stalk presentation theorem. Local Mathlib, upstream and Sheaf
   searches likewise found no duplicate. Inspected `GeneratingSectionsStalkSpan`
   and `FiniteLocallyFreeStalkHomLift`/`FiniteLocallyFreeStalkHomEquality`: they are
   scheme results and the latter two require finite locally free sources, so they
   do not close these general ringed-space claims. No split hole had a short proof
   from the available declarations.
4. **Route and pruning: pass.** The proof uses the existing canonical evaluation
   and Mathlib left exactness before introducing any further algebraic statement.
   All five added ordinary proof imports serve the proof; the public imports serve
   the unchanged statement interface. Compared all seven old proof dependencies
   with the new proof: every removed dependency is accounted for under No longer
   needed, with the still-needed lower dependencies distinguished from global
   pruning. The sheaf coordinate-kernel module is bypassed; ModuleStalkExact remains
   part of the lower source/local-lift plans, so no global pruning of it is claimed.
   Read `dag/units/sk-thm-p1.json` realized statement and steps; none of the removed
   dependencies realizes a unit step. The unit record and its route are preserved.
5. **DAG: pass.** The existing node changes only proof, proof_deps and proof_origin.
   Its four proof steps match the Lean combination. For all four nodes the union
   of step uses equals proof_deps, and the recorded Lean signature matches the
   module after whitespace normalization. New nodes have source, searches,
   complete proof steps, status split, creation record, inherited chapter/unit,
   blueprint ancestry, and module/declaration records. Their lower dependencies
   match their natural-language proof plans rather than pretending the sorries
   have been discharged.

Second reading changed only this report: added the independent checks, edge-case
assessment, alternative searches and explicit axiom results. The Lean proof and node
records required no repair. One original hole closed, three named holes added;
this remains a decomposition with net minus two, not an axiom-free geometric proof.
