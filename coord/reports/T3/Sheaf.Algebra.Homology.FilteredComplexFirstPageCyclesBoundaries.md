## What changed

Repaired `CategoryTheory.DecreasingFiltration.filteredComplex_firstPage_cycles_boundaries`
by removing the private helper whose statement duplicated
`CategoryTheory.pullback_kernel` in `Sheaf.CategoryTheory.SubobjectHomologyStep`.
The local replacement is the strictly more general helper
`pullback_kernel_of_eq`, which takes the composite morphism and an explicit equality;
its proof is the same subobject argument and is used at both call sites. The target
statement and all public interfaces are unchanged. The module compiles with
`lcompile.py`, and `deliver3.py --no-push` completes successfully.

## Proved and sorry left

Closed the repository's sole hole:
`CategoryTheory.DecreasingFiltration.filteredComplex_firstPage_cycles_boundaries`.
Both conjuncts are proved with its original statement. Holes closed: 1; holes added: 0;
split-off statements: 0. No `sorry` remains in the delivered module. The refreshed scratch
axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The duplicate exact-composite helper `pullback_kernel` is no longer present.
Removed the redundant direct proof import `Sheaf.CategoryTheory.Filtration`; the public
import of `FilteredComplexSubquotients` already supplies it. Added the two plain proof
imports `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits` and
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject`. Removing either from a scratch
copy fails compilation (respectively the Galois-connection/image API and
`Subobject.exists_obj_pullback_obj` are unavailable).
No old `proof_deps` entry is unused: the abelian-category, filtration, and subquotient
nodes still supply the structures and definitions. No DAG node or module is pruned
from the import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a private theorem with exactly the same statement as
an existing library theorem, which `import_prune_check.py` rejects. The existing theorem
is private in its source module and therefore cannot be referenced by name across module
boundaries; the repair uses a genuinely generalized local lemma with an explicit target
morphism and equality, avoiding the duplicate declaration while preserving the proof.

## New nodes

None.


## Second reading by T3

1. Compared the complete delivered module with the repository version using `diff`.
   The sole existing public theorem's signature, universes, section variables,
   visibility, and docstring are unchanged byte for byte. No definitions or public
   imports changed, no other module is delivered, and no change record is needed.
   Verdict: pass.
2. Compiled the actual delivered file with `lcompile.py`: no errors or warnings.
   Rebuilt the scratch axiom-check copy from the current file (the old scratch copy
   still contained the earlier helper). `#print axioms` for the public theorem gives
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned the delivered source: no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`, and no new definitions or chosen witnesses.
   Read each helper proof: evaluation preserves the mono/epi and exact cokernel
   sequence; the subcomplex inclusions commute with the differential; the Galois
   connection supplies inverse images and image inequalities. Verdict: pass.
3. There are no split-off statements, new modules, or new nodes. The proved private
   kernel helper follows by the two factorization inequalities after substituting
   its explicit composite equality. For zero maps it gives the full kernel; for an
   identity first map it recovers the original kernel. Searched Mathlib through
   `msearch.py` grep and LeanFinder with inverse-image/composite terminology, and
   searched both project roots with `rg`. No usable public kernel-pullback equality
   was found. The exact-composite helper in `SubobjectHomologyStep` and the
   image-composite helper in upstream `CardinalGeneratedCover` are private, so they
   cannot be imported by name. The local elementary proofs do not introduce holes.
   Verdict: pass.
4. Read the definitions in `FilteredComplexSubquotients` and the Stacks filtered-
   complex formulas in the local source copy
   `/home/ubuntu/work-bp/sheaf/literature/stacks-project/homology.tex`, section
   `section-filtered-complex`. At r=1 the next step is contained in the cycle
   intersection, and the differential image is contained in the current step.
   The cycle proof removes the redundant sum, identifies the inverse image of the
   graded kernel, and applies `exists_obj_pullback_obj` to the epic projection.
   The boundary proof removes the redundant intersection, pulls back along the mono
   step inclusion, kills the next-step image using `cokernel.condition`, and cancels
   the epic incoming projection in the image. These arguments cover zero complexes,
   constant filtrations, and arbitrary integer degrees without boundedness or
   finiteness assumptions. Both remaining proof imports were tested individually
   and are needed. The unit `sk-prop-av-pqf-finite` has empty `realized.statement`
   and `realized.steps`; no realized unit step is removed or bypassed by this local
   calculation. Verdict: pass.
5. Read node `lem-sp-filtered-complex-first-page-cycles-boundaries`: its two proof
   steps describe exactly the kernel and image arguments implemented here; its
   three `proof_deps` are all still used, and its document-based `proof_origin`
   remains accurate. No node changes are necessary. Verdict: pass.

Second reading changed the report to name the closed declaration, give explicit
closed/added counts, and record the removed redundant direct filtration import.
Refreshed the scratch axiom check and added scratch import-removal checks. The Lean
proof needed no further repair.
