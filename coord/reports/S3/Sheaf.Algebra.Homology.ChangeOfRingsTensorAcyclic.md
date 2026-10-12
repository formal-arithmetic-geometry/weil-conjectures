## What changed

Replaced the body of `SheafOfModules.changeOfRings_acyclic_of_tensor_acyclic` by a
complete reduction to a natural underived module comparison. The existing statement,
universes, hypotheses, visibility, definitions and public imports are unchanged.

The proof uses the already-proved upstream `CochainComplex.mapBifunctorSingle₁Iso`
from `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`, constructs the chain
isomorphism using the original h and hm, and reflects exactness through the faithful
exact underlying abelian sheaf functors. The private `acyclic_of_restriction` helper
is fully proved. Added proof imports are private.

Added `Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison`, with the one remaining
hole `SheafOfModules.exists_changeOfRings_tensor_comparison`. Its statement concerns
natural isomorphisms of modules only, with no complex or acyclicity premise/conclusion.
It has a complete proof in words and its own DAG node. No data is chosen from this
unproved theorem in a definition; witnesses are used solely within the theorem proof.

## Proved and sorry left

Closed the original hole by reduction:
- `SheafOfModules.changeOfRings_acyclic_of_tensor_acyclic`
  (`lem-pur-change-of-rings-tensor-acyclic`). Its proof depends on the comparison below.

Fully proved private helper:
- `SheafOfModules.acyclic_of_restriction`.

Added one hole, the only literal sorry in the delivered files:
- `SheafOfModules.exists_changeOfRings_tensor_comparison`
  (`lem-pur-change-of-rings-tensor-comparison`). Its whole proof is `by sorry`.

This is a decomposition: one original hole closed and one strictly simpler underived
hole added, zero net holes closed before import-closure accounting. The original item
is not independently proved without sorryAx. The degree-zero comparison uses an existing
fully proved source declaration rather than adding another theorem.

All delivered modules compile locally without warnings. Scratch #print axioms checks
show only propext, Classical.choice and Quot.sound for the reflection helper; the main
and comparison theorems additionally have sorryAx, as expected from the listed hole.

Edge cases reviewed: zero rings/modules give zero tensor modules; identity scalar
restriction is the unit tensor comparison. No flatness or boundedness was added. The
natural comparison holds for arbitrary modules, not merely acyclic complexes.

## No longer needed

No existing dependency node or module is pruned. Both old proof_deps,
`def-pc-sheaf-restrict-scalars` and `def-pur-sheaf-tensor-product`, remain used.

Removed the first worker's undelivered duplicate module
`Sheaf.Algebra.Homology.SingleTensorComplexComparison` and its new node
`lem-pur-single-tensor-complex-comparison`; use the upstream comparison directly.
Removed the redundant public import of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` from the new comparison
module: its declarations are already available through the tensor dependency.
All remaining imports support a statement or the written proof.

## Where the brief, the DAG or earlier work was wrong

The original plan needed a natural underived scalar/tensor comparison in addition to
the tensor and restriction constructions. That missing comparison is split off here.
The first worker missed the existing source `mapBifunctorSingle₁Iso` and duplicated
its argument; the second reading removed this duplicate module and node.

Independent searches used LeanFinder (scalar extension viewed over the original ring),
Loogle (restrictScalars with SheafOfModules), and grep (sheafification/restriction and
extension/tensor). No exact underived scalar/tensor comparison was found. Repository
search located the fully proved source BifunctorSingle comparison and checked the
identity-only change-of-rings comparison and module-sheafification tensor lemmas;
neither closes the remaining arbitrary ring-map comparison in a few minutes.

The Stacks sources were checked at https://stacks.math.columbia.edu/tag/06YY and
https://stacks.math.columbia.edu/tag/03EK. The latter defines sheaf tensor by
sheafification and points to the change-of-rings construction; the natural comparison
is an agent expansion of those constructions, not a verbatim named Stacks lemma.
WANTED: local copies of the cited sites-modules and sites-cohomology sources.

The existing parent ancestry has created.item as a module name. The new node follows
the previously recorded ancestry to `def-weil-derived-complete-integral-detailed`.

## New nodes

`lem-pur-change-of-rings-tensor-comparison`: natural underived O-module isomorphisms
from restricted change of rings to tensoring with the restricted Oprime unit.
The remaining proof is in `Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison`.
No change records or forced adaptations were needed.

## Second reading by S3

1. Compared the original module byte for byte outside its imports, private helper,
   and theorem proof body. The existing theorem signature and docstring are unchanged;
   no definition, target statement, hypothesis or conclusion changed. Verdict: pass.
2. Compiled the delivery in import order through lcompile.py; no errors or warnings.
   Scanned for forbidden declarations and checked axioms in scratch copies. Exactly
   the named comparison theorem has a literal sorry; there is no hollow definition.
   The reflection helper has standard axioms only; the main theorem retains sorryAx
   through the comparison. Verdict: pass as a decomposition.
3. Read the remaining split statement and its full docstring and DAG proof. It is the
   correct natural underived scalar/tensor identification, including zero and identity
   cases, requires no flatness, and is strictly simpler than the item. Independent
   searches found no duplicate general comparison. Its witnesses are used only in a
   proof. Verdict: pass.
4. Found the shortest existing source route for the degree-zero complex comparison,
   removed its duplicate new module/node, and used mapBifunctorSingle₁Iso directly.
   The old proof_deps are both still used. The unit sk-def-sf-operations has empty
   realized.statement and realized.steps records and no unit step is bypassed.
   Removed a redundant public import from the new comparison. Verdict: pass.
5. Checked the parent proof steps and dependency union against the final Lean proof;
   updated them for the upstream comparison and retained both original dependency
   nodes. The one new node has the required source, complete proof, searches,
   ancestry, chapter/unit, created and verbatim Lean statement records. Verdict: pass.

Second-reading changes: replaced the duplicate single-complex proof with the existing
source isomorphism, deleted its undelivered module/node, removed the redundant public
Mathlib import, corrected the parent DAG route/dependency union, and rewrote this
report around the final decomposition and verification results.
