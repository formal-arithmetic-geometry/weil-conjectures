## What changed

Removed the unused public import `Mathlib.Algebra.Category.ModuleCat.Abelian` from
`Sheaf.RingTheory.ProjectiveResolutionExtDegree`. The two public imports remaining supply
`HasProjectiveResolutionLE` and `HasProjectiveDimensionLE` in the theorem's signature.
The two plain imports supply Ext cocycle representation and bounded-resolution splicing
used only in its proof. Change record: `coord/changes/ProjectiveResolutionExtDegree-import.md`.
No declaration, proof body, definition, or DAG node changed.

## Proved and sorry left

`ModuleCat.projective_resolution_ext_degree` is proved, but was already proved in the
repository baseline. Holes closed by this delivery: none (0 of 0 baseline holes).
Holes added: none. Holes remaining in the delivered module: none. No statements split off.
This is import pruning on a listed repair, not new proof progress or decomposition.

## No longer needed

Removed import: `Mathlib.Algebra.Category.ModuleCat.Abelian`. It is not needed directly
by the statement or proof; the proof's module-specific instances are available through
its proof imports. No existing `proof_deps` node is removed: the proof still uses
`def-weil-pbc-finite-global-dimension`, `def-pc-ext`, and
`lem-weil-pbc-projective-resolution-succ-splice`. No whole library module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The first report described the theorem as proved without distinguishing its already
proved baseline. The delivery closes no holes. Removing a public import is an interface
import change, not merely a proof import change; its change record is retained.

## Second reading by X3

1. Compared the complete delivered module with the repository using `diff -u`: the only
   difference is deletion of the public Abelian import. All existing declaration signatures,
   visibility, docstrings, and proof bodies are byte for byte unchanged. No target or
   definition changes; the import change has the named change record. Verdict: pass.
2. Compiled the delivered file using `lcompile.py`: clean, no warnings. Compiled a scratch
   copy ending in `#print axioms ModuleCat.projective_resolution_ext_degree`: only
   `propext`, `Classical.choice`, and `Quot.sound`. No sorry or forbidden declaration forms.
   The forward proof kills a cocycle because its resolution term is zero. The reverse proof
   constructs a resolution, rather than selecting an arbitrary unproved witness. Verdict: pass.
3. No new declarations or split-off statements, hence no new nodes or holes to validate.
   Checked the boundary n=0: dimension zero gives a projective module and its identity
   resolution. At n+1, the projective epimorphism's kernel has bound n; the existing splice
   theorem adds exactly one degree. The zero module and zero ring require no extra case
   restriction or nonzero hypothesis. Verdict: pass.
4. Read Stacks Tag 065R at https://stacks.math.columbia.edu/tag/065R and the imported
   `GlobalDimension` and `ProjectiveResolutionSuccSplice` files. Inspected Mathlib
   `projective_iff_hasProjectiveDimensionLE_zero`, `extMk_surjective`, and
   `ShortExact.hasProjectiveDimensionLT_X₃_iff`; these are the criteria and shift the proof
   uses. Searched Lean and upstream RingTheory for the explicit-resolution equivalence;
   Mathlib's Ext criterion alone does not construct this library's bounded resolution.
   Both remaining public imports serve the signature and both plain imports serve the
   proof. The three direct callers import this module only for proofs; the two Ext callers
   already publicly import ModuleCat.Abelian themselves. The unit `sk-thm-p1` realized
   statement and steps are untouched; this node is below those steps. Verdict: pass.
5. Read `lem-weil-pbc-projective-resolution-ext-degree`: its four steps match cocycle
   vanishing, the identity resolution, kernel dimension shifting, and the existing splice
   theorem respectively. Its `proof_deps` and `proof_origin` still describe the unchanged
   proof. No node edit or new node is needed. Verdict: pass.

Second reading changed only this report and the import change record: clarified zero
new holes closed, public import effects, and the concrete review evidence. Lean unchanged.
