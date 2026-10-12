## What changed

The original finite-type theorem is proved from a local comparison diagram and a proved
kernel-generator argument. Its signature is unchanged. Two new modules isolate the local
shrinking/lifting statement and the complete categorical generator argument. The original
DAG node now records these steps. Proof imports use plain `import`; statement dependencies use `public import`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.RingedSpace.finitePresentation_kernel_surjection_finiteType`.
Proved the new `AlgebraicGeometry.RingedSpace.finitePresentation_kernel_comparison_generators`
without any sorry: the kernel is a quotient of the coproduct of the presentation kernel and
its original finite free source; a right inverse proves that quotient map is epi.

One new hole remains:
`AlgebraicGeometry.RingedSpace.finitePresentation_local_comparison`, node
`lem-weil-pbc-finite-presentation-local-comparison`.
It asserts only existence of the local finite presentation and two comparison maps, plus
restriction compatibility for the kernel. It does not assert finite type or finite kernel
generation. This is a decomposition (one upper hole closed, one smaller hole added), not
a proof free of remaining dependencies. No hollow definition or axiom is added.

## No longer needed

Removed the direct proof import
`Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting` from the item; local lifting
is now needed only by the local comparison lemma, whose module imports it. Also removed the direct proof dependency `def-weil-sheaf-of-modules-category` from
this item's `proof_deps`: its categorical constructions are now in the comparison
nodes. Removed redundant `Mathlib.Data.Finite.Sigma` from the new kernel-comparison
module; its finite dependent-sum instance is already available through the needed imports.
No existing DAG node or module is globally pruned: the remaining local comparison still needs the
original lifting dependency. The exactness part of that dependency is not needed for the
proved generator argument, which instead uses a categorical split epimorphism.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or unit route was found. The final local-surjectivity
argument can be replaced by an explicit split epi from the presentation kernel plus the
finite free source. Rank zero and empty finite presentation families require no exceptions;
the coproduct and free-module constructions handle them. If X is empty, the local generator
cover is indexed by the empty carrier and covers X vacuously.

The attempted local-generators restatement was discarded: it would merely repackage finite
type. The delivered local comparison statement is strictly the shrinking/lifting step.

## New nodes

`lem-weil-pbc-finite-presentation-local-comparison` records the local comparison maps from
Stacks 01BP(1), first paragraph, with the sectionwise kernel restriction from 01AF.
Its module has the sole remaining new sorry and a complete natural-language proof.

`lem-weil-pbc-finite-presentation-kernel-comparison` records the displayed generator map and
final assertion of Stacks 01BP(1). Its Lean theorem is fully proved using kernel lifts,
a split epi from a coproduct, and finite generating sections. No change record is needed:
all existing signatures and definitions are unchanged.

## Second reading by V1

1. Compared every delivered module with the read-only repository. The only existing
   module is the item: its universe, namespace, visibility, theorem signature, and
   public imports are byte-for-byte unchanged. Its proof, private imports, and proof
   docstring changed. The other two modules are new; no existing definition changed
   and no change record is required. Verdict: pass.
2. Compiled all three modules in import order with `lcompile.py`. Scratch copies with
   `#print axioms` showed only `propext`, `Classical.choice`, and `Quot.sound` for
   `finitePresentation_kernel_comparison_generators`; the item and local-comparison
   theorem additionally use `sorryAx`. The sole literal sorry is the named theorem
   `finitePresentation_local_comparison`. No forbidden declarations or hollow
   definitions occur. The choices in the item's proof assemble witnesses inside a
   proposition proof; no definition chooses arbitrary data from an unproved theorem.
   Verdict: pass as a decomposition, not an axiom-free proof of the original item.
3. Read the local-comparison statement and the generating-sections argument against
   [Stacks 01BP](https://stacks.math.columbia.edu/tag/01BP), proof of (1). Finite
   simultaneous lifts after shrinking give the two comparison maps; restriction
   preserves the finite presentation and kernel, yielding the stated isomorphism.
   The hole isolates this step and does not assert kernel finite type. Rank zero,
   a presentation with no generators or no relations, the zero module, and the
   empty space require no extra hypotheses. The generator theorem is fully proved:
   cancellation by the monic kernel inclusion checks the displayed right inverse.
   Independent LeanFinder search for simultaneous local lifting from finite free
   modules, Loogle search for presentations under restriction, msearch grep for
   presentation mapping and restricted free modules, and rg over Mathlib and both
   library roots found presentation constructors and finite restriction helpers,
   but no existing theorem supplying both local comparisons. Closing this remaining
   statement would require substantial formalization of simultaneous section lifts
   and restriction transports, rather than a short application. Verdict: pass.
4. Read from the original conclusion through both helper statements. The proof uses
   Mathlib kernel lifts and split-epi cancellation, then upstream generating-section
   constructors; it adds no hole for the categorical generator argument. Every old
   proof dependency absent from the new direct dependency list is now named in
   `No longer needed`. `pqf-def-coherent` remains for the finite-type definition.
   The removed dependencies remain transitively needed by the comparison nodes,
   so no existing module is globally pruned. Inspected `dag/units/sk-thm-p1.json`:
   this item is below its realized statement and steps; none of them is bypassed
   or changed. Verdict: pass.
5. Compared all three node statements and Lean records with the Lean declarations.
   The original node differs only in `proof`, `proof_deps`, and `proof_origin`;
   the new nodes have sources, full proof plans, statement and proof dependencies,
   searches, split status, creation metadata, blueprint provenance, chapter, unit,
   and matching Lean records. Dependency lists are exactly the unions of their
   proof-step uses. Verdict: pass.

Second reading changed: removed the redundant finite-sigma import, corrected the
composition order in the generator proof docstring, replaced the item's obsolete
four-step docstring by its actual three-step reduction, and completed the pruning
report with both removed direct dependencies. No Lean statement or proof term changed.
Holes closed: `AlgebraicGeometry.RingedSpace.finitePresentation_kernel_surjection_finiteType`.
Holes added: `AlgebraicGeometry.RingedSpace.finitePresentation_local_comparison`.
The new generator theorem has no hole. Net holes closed minus added: zero.
