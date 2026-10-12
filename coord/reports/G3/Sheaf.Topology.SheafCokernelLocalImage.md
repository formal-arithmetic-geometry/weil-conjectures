## What changed

Proved `AlgebraicGeometry.RingedSpace.sheafified_cokernel_local_image` in
`Sheaf.Topology.SheafCokernelLocalImage`, preserving its signature and visibility.
The proof uses the sheafification adjunction for epimorphy, evaluated cokernel
exactness for local lifts, and Mathlib local injectivity and separatedness for
local vanishing. Added the proof-only import
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`. Updated the node's proof and
proof dependencies to this route. The second reading removed three redundant direct Mathlib public imports; their
exports remain available through the retained imports.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.RingedSpace.sheafified_cokernel_local_image`
(node `lem-weil-pbc-sheaf-cokernel-local-image`). No holes remain in the item and
no holes were added. This is a complete proof, not a decomposition. Local
compilation succeeds without warnings. The delivery dry run checks axioms.

## No longer needed

Removed proof import `Sheaf.Paper.SiteSheafificationSectionsLocal`, corresponding
to node `lem-weil-pbc-site-sheafification-sections-local`. Its local-representative
and descent assertions are unnecessary: epimorphy follows directly from the
adjunction, while the kernel criterion uses Mathlib's local injectivity instance.
Also removed proof dependency `lem-weil-pbc-module-sheafification-underlying-sets`:
the proof operates on the underlying additive-group sheafification directly and
needs no additional comparison with set-valued sheafification. No unit statement
or realized unit step is bypassed. No other module is newly imported from Sheaf.

Second-reading import cleanup removed the redundant direct imports
`Mathlib.Topology.Sheaves.Sheaf`, `Mathlib.CategoryTheory.Sites.LeftExact`, and
`Mathlib.Algebra.Category.Grp.FilteredColimits`. These modules remain transitively
publicly imported, so this removes no exported declaration or dependency module
from the closure. The only removed Sheaf dependency edge is the site-local-sections
module; whether it becomes globally unreachable depends on other target paths.

## Where the brief, the DAG or earlier work was wrong

The delivery tool falsely flags the original docstring line beginning with the
word `axiom` in “sheaf axiom”. Reflowed that sentence without changing its text.
No incorrect statement was found. The DAG's construction of a local-image
subsheaf and its local-representative proof of epimorphy are unnecessary for the
actual Lean signature, which asks for the sectionwise criterion, epimorphy, and
the zero composite. The second reader updated the proof docstring to match the implemented argument;
the node records the same shorter argument. The empty open causes no exception:
covering-sieve separatedness includes the empty cover. Neither local lifts nor
any definition chooses data from an unproved existence theorem.


## Second reading by G3

1. **Unchanged interface — pass.** Compared the delivered module with the repository
   using `diff`, and checked its sole theorem signature byte for byte through `:= by`.
   No declaration, hypothesis, conclusion, definition, universe, or visibility changed.
   The import-only change record is
   `coord/changes/SheafCokernelLocalImage-imports.md`; there are no forced adaptations. The three redundant public
   imports removed in this reading remain publicly available through retained imports.
2. **Proof and axioms — pass.** Independently compiled the original delivered proof
   and the final import cleanup using `lcompile.py`. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.RingedSpace.sheafified_cokernel_local_image`:
   only `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   No `sorry`, forbidden declaration, or data choice from an unproved existence
   theorem occurs. Checked each argument: forgetful faithfulness for the zero
   composite, adjunction injectivity and epic cancellation for epimorphy,
   evaluated cokernel exactness for lifts, local injectivity for forward local
   vanishing, and separatedness for the reverse implication.
3. **Split statements — pass, none.** No new theorem or node and no new hole was
   introduced. Checked small cases: on the empty open the local condition is
   vacuous and separatedness for the empty cover forces the section to zero;
   the zero morphism and an isomorphism give the expected kernel criteria.
   Independent `rg` searches for cokernel/sheafification and local/image in
   Mathlib's module-presheaf files and the library found no existing theorem
   replacing this combined statement. Read the Mathlib exactness and local
   injectivity declarations used in the proof; they already supply the needed
   intermediate results.
4. **Route and pruning — pass after cleanup.** The proof uses proved Mathlib
   results throughout and adds no project dependency. Both old proof dependencies
   absent from the implemented argument are listed in `No longer needed`.
   Checked `dag/units/sk-thm-p1.json`: neither removed dependency nor this node is
   a realized unit statement or step. No unit route is bypassed. Removed three
   redundant direct Mathlib imports and confirmed compilation with the remaining
   two public imports and one proof-only import. Kept the working proof unchanged.
5. **DAG agreement — pass.** Compared node JSONs: only `proof`, `proof_deps`, and
   `proof_origin` differ. Checked that `proof_deps` is exactly the union of the
   steps' `uses`, and that the four steps describe the Lean argument. The node's
   statement, Lean statement, source, unit, and chapter remain unchanged. No new
   nodes require metadata checks.

Changed in this reading: removed three redundant direct Mathlib imports; replaced
an obsolete local-image-subsheaf proof description with the actual adjunction,
exactness, local-injectivity, and separatedness argument; corrected the report to
record that cleanup. Closed one existing hole, added zero holes, split off zero
statements. No mathematical proof repair was needed.

Import-only change record: `coord/changes/SheafCokernelLocalImage-imports.md`.
The first dry run required this record for redundant public-import removal.
All 658 downstream modules are recorded; their visible declarations and
instances are preserved by the verified transitive public import closure.
