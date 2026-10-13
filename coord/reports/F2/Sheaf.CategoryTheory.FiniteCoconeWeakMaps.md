## What changed

Replaced the sorry proof of
`CategoryTheory.BigradedExactCouple.finiteCocone_weakMaps` with a reduction to the
finite-tail cycle and boundary descriptions. The existing theorem signature,
visibility, definitions and public imports are unchanged. Added ordinary proof
imports for the two formula modules and abelian image/subobject calculations.
The five private helpers prove pullback/kernel, cokernel/image, inverse-image of
image, quotient-kernel and initial-g kernel identities.

Added `Sheaf.CategoryTheory.FiniteCoconeLimitCycles`, with a complete proof from
`pageCouple_image_prefix`, the tower projection equations and exactness.
Added `Sheaf.CategoryTheory.FiniteCoconeLimitBoundaries`, with one named open theorem
and an expanded full induction proof in its docstring. Updated the item's DAG
proof and both new nodes to name the facts actually used. No statement or
definition change record is required; the earlier purported visibility record
was removed because it described only ordinary proof imports/private helpers.

## Proved and sorry left

Hole closed:
`CategoryTheory.BigradedExactCouple.finiteCocone_weakMaps`
(node `lem-sp-finite-cocone-weak-maps`). Its proof body contains no sorry, but
its axioms still include `sorryAx` through the new boundary formula.

New, fully proved theorem:
`CategoryTheory.BigradedExactCouple.finiteCocone_limitCycles`
(node `lem-sp-finite-cocone-limit-cycles`). Its axioms are exactly the permitted
standard axioms. All five private helper proofs also use only standard axioms.

Hole added and left:
`CategoryTheory.BigradedExactCouple.finiteCocone_limitBoundaries`
(node `lem-sp-finite-cocone-limit-boundaries`), whose whole proof is `by sorry`.
There are no other sorries in this delivery and no definitions with sorry/data
chosen from existence. This is a decomposition: one old hole closed, one new
hole added, net zero holes removed in this set. The main theorem is not yet
axiom-clean; no claim of complete target progress is made.

## No longer needed

None of the old proof dependencies are removed: `def-sp-exact-couple` and
`def-sp-convergence` are both used. No module is claimed pruned from the target
closure. Every added import supplies a used declaration; in particular, removing
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject` from the cycle module
was tested and failed on `Subobject.exists_obj_pullback_obj`, then restored.

## Where the brief, the DAG or earlier work was wrong

The first report called the proof complete without counting the new boundary
hole, repeated an inaccurate visibility-change claim, and did not update the
item's proof plan. Those reporting/DAG faults are repaired. New-node Lean
signature records are now verbatim rather than whitespace-flattened. Search
records now correspond to actual msearch.py logs instead of invented queries.

The cycle proof directly uses the already proved generic tool
`pageCouple_image_prefix` (node `lem-sp-derived-couple-image-prefix`, in the
proper-base-change unit). Its statement supplies precisely the recursive
monomorphic inclusions/image equations needed here; it does not substitute
another geometric route for this unit. The unit
`dag/units/sk-prop-av-pqf-finite.json` has empty `realized.statement` and
`realized.steps[0]`; no realized node or unit route is removed or altered.
That pre-existing unit placement is unrelated to the algebraic proof repair.

The cited literature files are absent on this machine. Read the official online
[Stacks 011T](https://stacks.math.columbia.edu/tag/011T) and
[Stacks 012W](https://stacks.math.columbia.edu/tag/012W): the former supplies the
finite boundary/cycle formulas; the latter motivates the finite-tail application.
The abelian exact-couple generalization and its full chase are agent-written,
not a verbatim claim that Tag 012W already states this generalized theorem.

## New nodes

`lem-sp-finite-cocone-limit-cycles` identifies limiting cycles with image
initialG under the upper zero tail. Its proof is complete and independent of
the left tail and of the open boundary formula.

`lem-sp-finite-cocone-limit-boundaries` identifies limiting boundaries with
initialG of the cocone kernel under the invertible left tail. It is strictly a
part of weak convergence: it asserts no epimorphism or equal quotient kernels.
The theorem docstring gives the induction and eventual-LUB argument in full.
Both nodes retain the item's chapter/unit and trace their blueprint origin
through the finite-cocone reduction to `thm-sp-spectral-object-yields`.

## Second reading by F2

1. Compared the item against the repository with `diff -u`. The only existing
   declaration, `finiteCocone_weakMaps`, has a byte-for-byte identical signature
   from `theorem` through its conclusion. There are no definition edits or
   public-import changes. Both other modules are new. Verdict: unchanged public
   meaning; no interface change record needed.

2. Compiled all three modules in dependency order through `lcompile.py --all`,
   with no errors or warnings. In temporary copies, printed axioms of all five
   private helpers and all three public theorems. Helpers and limitCycles have
   only `propext`, `Classical.choice`, `Quot.sound`; weakMaps and limitBoundaries
   additionally have `sorryAx`, exactly as expected from the one reported hole.
   Read all bodies: no axiom, unsafe, opaque, implemented_by, extern, hidden
   sorry or data construction from an arbitrary unproved existence witness.
   The choices in the cycle proof are of uniquely specified derived maps and
   recursively specified image/inclusion families. Verdict: sound reduction,
   with the boundary statement explicitly still open.

3. Read both formula signatures against 011T and the actual tower/cocone
   definitions. Cycle proof uses the zero bound on total degree p+q+1 at
   (p+2,q-1), with no positivity restriction on p or q. Boundary induction starts
   at r=0 (invertible iterate, zero boundaries) and remains valid at negative
   indices. If j_p is invertible, all outgoing iterates have zero kernel by the
   cocone equation, and both boundary expressions are zero. If j_p=0, eventual
   outgoing iterates vanish since their tail factor is invertible, giving all
   of image initialG. The all-zero couple also satisfies both equalities. The
   proof works in arbitrary abelian categories using epimorphic refinements,
   not element lifts without refinement. Repeated Mathlib searches with
   different queries through msearch.py (LeanFinder, Loogle, grep), and rg on
   Sheaf/upstream. No matching formula found; finiteCycle_kernel_presentation
   has an additional next-D vanishing condition and a quotient-kernel
   conclusion, so it does not directly replace the boundary theorem. Verdict:
   true and strictly simpler split-off; no restatement of the item.

4. Read the main proof top-down: hZ makes the page map epic, the graded map is
   epic by its construction, quotient_kernel and pullback_image calculate the
   two kernels, and exact_g plus A.comm identifies the next filtration image.
   The last equality is commutativity of sup. The cycle proof obtains hZ from
   the mono/image prefix and f_comm instead of adding a general cycle-formula
   hole. Checked every import against its uses, including the failed-removal
   test above. Checked the unit's realized fields; none is bypassed. Verdict:
   genuine quotient/kernel reduction with no missing old dependency to prune.

5. Checked Lean/node declaration names and verbatim signatures, source places,
   proof-step dependency unions and creation metadata. Rewrote the old generic
   plans to describe the exact Lean proof or the remaining boundary induction.
   The cycle node now cites the image-prefix theorem actually used, and the
   main node cites both new formulas and the refinement tool. Updated the
   new-node blueprint ancestry and replaced unverifiable search records with
   recorded real searches. Verdict: DAG agrees with the delivered proof.

Changes in this reading: expanded the boundary docstring; repaired all three
DAG proof plans, proof dependencies, origin/signature/search/blueprint records;
removed the inaccurate change record; corrected hole accounting and the report.
Removed the new section-level variable command and wrote its binders explicitly
on each private helper, so no new command can affect subsequent public declarations.
The compiled proof bodies and all public signatures were retained. Recorded the
actual unavailable LeanSearch attempt as well as the successful three search kinds.
