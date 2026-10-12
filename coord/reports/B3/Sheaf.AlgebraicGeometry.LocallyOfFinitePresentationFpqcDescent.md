## What changed

Proved `AlgebraicGeometry.locallyOfFinitePresentation_of_fpqc_cover` without changing
its signature or existing docstring. Replaced the proof-only import of
`Sheaf.AlgebraicGeometry.FpqcLocalOnBaseCriterion` with
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`. The proof generates the covering
sieve, supplies the canonical pullback squares, and applies the proved source-library
family-descent theorem using Mathlib's finite-presentation descent instance.
The two public imports still supply the statement's notions.

## Proved and sorry left

Proved `AlgebraicGeometry.locallyOfFinitePresentation_of_fpqc_cover`
(node `lem-weil-pbc-fpqc-descend-locally-finite-presentation`). No sorry remains in the
item, and no sorry or Lean declaration is added elsewhere. The dry run checks the
transitive axioms. The source theorem works with arbitrary index universes and does
not assume the index type is nonempty or finite. The canonical squares match precisely
the second projections in the hypothesis, so no transport of the statement is needed.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.FpqcLocalOnBaseCriterion`, and no longer use
its declaration `AlgebraicGeometry.fpqc_local_on_base_criterion`. There were no other
proof-dependency imports present to remove. The following old node dependencies are
removed from the item's proof route (some definitions remain statement dependencies,
and other targets may still need these nodes):

- `def-pc-scheme`
- `def-weil-pbc-finitely-presented-algebra`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `def-weil-surjective-morphism`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-flat-ring-map-iff-flat-affine`
- `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat`
- `def-weil-pbc-faithfully-flat-ring-map`
- `lem-weil-pbc-open-preimage-fibre-product`
- `lem-weil-pbc-cartesian-square-pasting`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`
- `lem-weil-pbc-fpqc-local-on-base-criterion`

Recorded modules for the pruned node dependencies (none needs a direct proof import
in this item):

| Node | Module |
| --- | --- |
| `def-pc-scheme` | `Mathlib.AlgebraicGeometry.Scheme` |
| `def-weil-pbc-finitely-presented-algebra` | `Mathlib.RingTheory.FinitePresentation` |
| `lem-weil-pbc-qcqs-morphism-permanence` | `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` |
| `def-weil-surjective-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` |
| `def-weil-affine-spectrum` | `Mathlib.AlgebraicGeometry.Scheme` |
| `lem-weil-pbc-flat-ring-map-iff-flat-affine` | `Mathlib.AlgebraicGeometry.Morphisms.Flat` |
| `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat` | `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` |
| `def-weil-pbc-faithfully-flat-ring-map` | `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` |
| `lem-weil-pbc-open-preimage-fibre-product` | `Mathlib.AlgebraicGeometry.Restrict` |
| `lem-weil-pbc-cartesian-square-pasting` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` |
| `lem-weil-pbc-fibre-product-affine-spectra` | `Mathlib.AlgebraicGeometry.Pullbacks` |
| `lem-weil-pbc-lfp-affine-opens-finite-presentation` | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` |
| `lem-weil-pbc-fpqc-local-on-base-criterion` | `Sheaf.AlgebraicGeometry.FpqcLocalOnBaseCriterion` |

Some Mathlib modules remain available transitively through the statement imports. The ring-level finite-presentation descent node remains because Mathlib's
single-morphism descent instance uses that ring theorem. The generic source family
theorem has its own proved node, rather than an imported sorry-backed statement.
The unit `sk-thm-p1` has neither this item nor its former criterion in `realized`;
none of its required statements or proof steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing node's searches already found the proved source-library covering-family
lemma, but its Lean proof was still sorry-backed. The shortest route is to use that
proved lemma and the Mathlib descent instance directly. The sources confirm Tag 02KY;
its finite-type wording in the proof is the already documented slip. No statement is
changed or disputed. The local literature TeX is absent on this machine; checked
[02KY](https://stacks.math.columbia.edu/tag/02KY) and
[02KP](https://stacks.math.columbia.edu/tag/02KP) online. The LeanSearch service returned
Internal Server Error; Loogle, LeanFinder and local source searches were available.

## New nodes

`lem-weil-pbc-fpqc-family-descent-of-single-morphism-descent` records the existing proved
`AlgebraicGeometry.Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`, including its
Zariski-locality, base-change stability, and single-morphism descent hypotheses.
This attaches a source-library tool; it creates no duplicate Lean module and no
unproved intermediate statement. No change record is needed because every public
signature and public import stays unchanged.

## Second reading by B3

1. **Public statements unchanged — pass.** Compared the whole delivered module with
   the repository using diff. Its sole existing theorem signature, universe binders,
   docstring, public imports and namespace are byte for byte unchanged. Only its proof
   and two proof-only imports differ. No definition or change record is introduced.
2. **Proof and axioms — pass.** Independently compiled the module locally without errors
   or warnings (1.7 seconds). A scratch copy with `#print axioms` for the item and the
   imported generic family theorem reports exactly `propext`, `Classical.choice`,
   `Quot.sound` for both; neither has `sorryAx`. The delivered module contains no sorry,
   axiom, unsafe, opaque, implemented_by or extern. The covering-sieve conversion and
   canonical pullback squares elaborate directly, with no altered hypothesis.
3. **Split statements and edge cases — pass.** There are no split-off Lean statements
   or unproved dependencies. The new node attaches an existing proved generic theorem;
   its hypotheses include all three section assumptions (target Zariski locality,
   single-morphism descent, base-change stability). Read its family, sieve and affine
   proofs in the source module. Arbitrary index universes and an empty index are allowed:
   an empty family covers only the empty base, where target locality is vacuous. No
   finiteness or nonemptiness assumption was silently added. Independent LeanFinder and
   local searches found no shorter family result or duplicate generic node attachment.
4. **Top-down route and pruning — pass.** The direct application of the proved source
   family theorem and Mathlib's finite-presentation descent instance closes the item.
   Removing either proof-only import in a scratch copy fails (missing descent instance
   or missing family theorem), so both are needed. Compared old and new proof_deps:
   all 13 removed nodes are listed under No longer needed. The ring-descent dependency
   remains justified by the Mathlib instance's proof. Read sk-thm-p1.realized: this item
   and its former criterion realize no required unit step, so the route is preserved.
5. **DAG correspondence — pass.** The existing node changes only
   proof, proof_deps and proof_origin, and its uses union agrees with proof_deps. The new
   node accurately records the existing generic theorem and its source proof, with no
   new Lean module or sorry. Added the independent LeanFinder search, supplementing the prior Loogle, grep
   and unavailable LeanSearch records. Preflight confirmed that an existing-declaration
   attachment must omit lean.file; retained that format. Existing theorem statements and unit records are unchanged.

Second reading changed only new-node metadata and this review report; the Lean proof
needed no repair. Local axiom checks establish that the item is fully proved.
