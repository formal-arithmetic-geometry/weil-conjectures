## What changed

Reduced `CategoryTheory.Sheaf.exists_cechDoubleComplex` to the column and total
comparisons for a specified, explicitly constructed injective-resolution Čech double
complex. The proof chooses Mathlib's `injectiveResolution F`, constructs D by applying
the Čech functor termwise and flipping its indices, and pairs the two comparisons.
The existing enough-injectives spectral-sequence assembly remains complete.
All existing signatures and definitions in the assigned module are unchanged.

Added three modules:
- `Sheaf.CategoryTheory.CechResolutionDoubleComplex`: an actual construction with a
  proved zero-morphism preservation instance; no `sorry` in any data or proof.
- `Sheaf.CategoryTheory.CechResolutionColumns`: the column-complex comparison for any
  specified injective resolution and any family, without a covering hypothesis.
- `Sheaf.CategoryTheory.CechResolutionTotal`: the total-homology comparison for a
  specified injective resolution and a covering.

The new comparisons are strictly separate parts of the original argument: neither
asserts existence of a double complex with both properties, nor a spectral sequence.
The source module imports their modules privately. The construction has Cech degree
first, so its column homology has the orientation required by the existing spectral
sequence. Updated `lem-sc-cech-spectral` to describe the partial implementation.

## Proved and sorry left

One of the assigned module's two original sorries is reduced by a complete Lean proof:
`CategoryTheory.Sheaf.exists_cechDoubleComplex`. Its proof still depends transitively
on the two named comparison statements below. This is a reduction, not an axiom-free
proof of the entire Cech-to-derived theorem.

Every remaining direct sorry in this delivery:
- `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`, existing node
  `lem-sc-cech-spectral`: untouched independent-universe general theorem.
- `CategoryTheory.Sheaf.cechResolutionDoubleComplex_columns`, new node
  `lem-sc-cech-resolution-columns`.
- `CategoryTheory.Sheaf.cechResolutionDoubleComplex_total`, new node
  `lem-sc-cech-resolution-total`.

Hole accounting: one original direct hole is closed by decomposition, two new direct
holes are added, and one original direct hole remains. Thus zero of the two originally
holed declarations is proved independently of open comparison statements; the net
change is one additional direct hole.

The new construction and its zero-preservation instance are fully proved.
`exists_cechToDerivedSpectralSequence_of_enoughInjectives` keeps its complete assembly.
Local compilation of all four delivered modules succeeds without warnings.

Edge cases checked mathematically: an arbitrary non-covering family is permitted in
the column lemma; the total lemma requires a covering. For an empty indexing type,
all products in the Cech complex are zero; if this is a covering, the free abelian
sheaf on X is zero, so its Ext groups vanish too. For a singleton identity covering,
the alternating complex of the constant cosimplicial object has differential
alternating between zero and identity, and retracts to evaluation in degree zero.
For the zero sheaf, any injective resolution is acyclic and the comparisons reduce
to zero cohomology. No extra smallness, finite-cover, or localization-exactness
hypothesis is introduced. Hom sets, sheaf values, and the family index all use v.

## No longer needed

Removed the direct proof import `Sheaf.CategoryTheory.SiteInjectiveCechAcyclic` from
the assigned module; its role moves to `CechResolutionTotal`, whose future proof
uses injective row acyclicity. The old direct dependencies `lem-weil-pbc-site-injective-cech-acyclic` and
`def-weil-pbc-sites-and-cohomology` are replaced in `lem-sc-cech-spectral.proof_deps`
by the two comparison nodes. Both old nodes are still needed transitively by those
comparisons; neither is globally pruned. No globally pruned nodes or modules are claimed.
The general double-complex spectral-sequence module remains required by the final
assembly. No public imports were removed. The unit's steps remain: explicit double
complex, column calculation, and row-acyclicity/total comparison.

## Where the brief, the DAG or earlier work was wrong

The DAG node names only the general spectral-sequence declaration, while the assigned
module also has the unproved `exists_cechDoubleComplex`. The delivery gives that
auxiliary declaration a concrete reduction; the independent-universe general
statement is not covered by it. The source's localized-resolution description is
unnecessary for computing H^q(V,F): the free abelian sheaf on V represents evaluation,
so Ext is computed directly with the global injective resolution.

`SiteInjectiveCechAcyclic` is marked disputed for independent universes. The new total
comparison uses only the equal-universe situation; this avoids the stated size
counterexample, and its docstring records why the free representables have the
required size. That existing disputed statement has not been changed.

The second reading also found that the total comparison must transport the
chosen-product version of injective Čech acyclicity to Mathlib's complex using
`SiteCechComplex.mathlib_complex_iso_exists`. Its proof import, docstring step and
DAG dependency are now explicit.

The literature tex files are not present on this machine. The blueprint proof and
DAG proof were read, and Stacks Tags 03AW, 03AZ and 03F6 were checked at their official
online pages. LeanSearch returned HTTP Internal Server Error; recorded as unavailable,
not as a failed mathematical match. Loogle, LeanFinder, and source grep were run.

## New nodes

`def-sc-cech-resolution-double-complex`: source Step 1, module
`Sheaf.CategoryTheory.CechResolutionDoubleComplex`, specified-resolution construction.
Its data and structural proof are fully defined and compiled.

`lem-sc-cech-resolution-columns`: source Step 2 and `lem-sc-cech-spectral` Step 1,
module `Sheaf.CategoryTheory.CechResolutionColumns`. The proof in words identifies
Ext via evaluation and uses exact products, then naturality to assemble a complex
isomorphism. This statement remains sorry and is the first new proof item.

`lem-sc-cech-resolution-total`: source Step 3 and `lem-sc-cech-spectral` Step 2,
module `Sheaf.CategoryTheory.CechResolutionTotal`. The proof in words uses injective
row acyclicity, the augmentation cone and its finite filtration, and the
injective-resolution computation of Ext. This statement remains sorry and is the
second new proof item. No definition or statement change records are needed.


## Second reading by U1

Independent second reader, 2026-10-12; I did not write the initial reduction.

1. Compared the assigned module with the repository using diff and the declaration
   parser. Every existing signature and definition is unchanged byte for byte.
   Only the two private proof imports and the body of exists_cechDoubleComplex
   change. The three added modules contain new declarations only. No target or
   existing public import changes. Verdict: pass.
2. Compiled all four files in import order with lcompile.py. Scratch copies with
   #print axioms show only propext, Classical.choice and Quot.sound for the actual
   double-complex construction; the comparisons and the existing theorems also
   show sorryAx as explicitly reported. No forbidden declaration form, definition
   hole or unlisted direct sorry occurs. The delivery's automatic probe checks all
   declarations, including the zero-preservation instance. Verdict: pass as a
   decomposition, not as a completed sheaf-cohomology proof.
3. Read the new construction and both comparison statements and their proofs in
   words. Checked orientation: termwise Cech initially has resolution degree as
   outer index; flip makes Cech degree outer and resolution degree inner, exactly
   as required by mapHomologicalComplex of the homology functor. Products of
   abelian groups are exact, and the free-abelian Yoneda/sheafification adjunction
   identifies evaluation with Hom from the free representable. Equal hom/group
   universes make those representables small. The empty-family, singleton identity
   covering and zero-sheaf cases introduce no exception. The column statement
   needs no covering; the total statement does. Neither comparison asserts the
   other comparison or existence of the double complex, so these are strictly
   separate parts of the argument, not renamed copies of the item. Independently
   searched LeanFinder, Loogle, Mathlib source and lean/ using evaluation, Ext,
   product homology and augmented-bicomplex language. The Ext/cohomology-class
   equivalences are useful components, but do not close either comparison in a
   few lines. Checked Stacks 03AW and 03F6 against the total proof sketch and 03AZ
   against the conclusion. Verdict: pass; both comparisons remain open.
4. Read the old proof dependencies and dag/units/sk-thm-picard-cech.json. The
   unit's realized arrays are empty, so no existing realized association is
   bypassed or edited. The route still constructs the resolution double complex,
   identifies column cohomology, proves the row-acyclic total comparison and uses
   the general spectral-sequence assembly. Global evaluation computes the stated
   Ext groups directly, as the old node's already-reviewed plan does. All old
   direct dependencies removed from proof_deps are listed above and retained
   transitively; no global pruning is claimed. New imports needed only for proofs
   are private. Verdict: pass.
5. Checked each new node against its Lean declaration, source, proof steps,
   dependency union, creation record, chapter, unit and blueprint ancestry. Fixed
   lean.statement to contain the verbatim multi-line signature from the def/theorem keyword (the parser
   excludes the noncomputable modifier). The total proof
   sketch had omitted the transport from the chosen-product Cech complex to
   Mathlib's Cech complex; added its existing comparison node and private import.
   Existing-node metadata correctly distinguishes the equal-universe reduction
   from the still-open general theorem. Verdict: pass after repair.

Changes by the second reader: added the chosen-product/Mathlib comparison step,
private import and DAG dependency; made the three new node signatures verbatim;
recorded the independent searches; completed the old-dependency accounting and
made the one-hole-to-two-holes decomposition explicit. No Lean statement,
definition or proof body was changed by the second reader.
