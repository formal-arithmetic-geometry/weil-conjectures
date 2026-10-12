## What changed

The statement and public imports of `Sheaf.RingTheory.KoszulConormalComparisonQuasiIso`
are unchanged. Its proof now obtains the existing conormal basis, checks the induced
homology map degree by degree, and combines two strict subcalculations with Mathlib's
single-complex homology and isomorphisms between zero objects.

A private helper proves vanishing above degree r without any regularity hypothesis:
the exterior-power basis has an empty index type, so the exterior term, its dual,
and its homology are zero. The below-top and top calculations are stated in separate
new modules, each with its own DAG node and complete mathematical proof in words.
The top calculation assumes the specified conormal basis instead of regularity;
the existing conormal-basis theorem discharges that hypothesis in the main proof.

All three modules compile without non-sorry warnings through lcompile.py. No existing
signature, definition, visibility, or public import changed. No forced adaptations.

## Proved and sorry left

Closed the sole original hole:
`ExteriorAlgebra.koszul_conormal_comparison_is_quasiIso`
(node `new-s3-koszul-conormal-comparison-quasi-iso`). No sorry remains in the item.

Added two holes, each strictly part of the original argument:

- `ExteriorAlgebra.koszulDual_isZero_homology_below_top`
  (node `lem-sc-koszul-dual-below-top-homology`): only degrees n < r.
- `ExteriorAlgebra.koszul_conormal_comparison_isIso_top_homology`
  (node `lem-sc-koszul-conormal-top-homology`): only degree r, given a conormal basis,
  with no regularity hypothesis or assertion about other degrees.

This is a decomposition (one hole closed, two added; net -1), not a complete proof
of the underlying Koszul duality calculation. The private above-top helper
`koszulDual_isZero_homology_above_top` is fully proved from Mathlib and definitions.
The previously existing conormal-basis theorem is used; its underlying basis-data
hole is unchanged and not added by this delivery.

Edge cases checked in the mathematical arguments: r=0 has no lower degrees, I=0
and no incoming top differential; I=A gives zero quotient and determinant;
the zero ring and characteristic 2 require no nontriviality or sign exceptions.
For r=1 the top incoming image is (f_0); for r=2 the normalized top scalar is -1,
which is still a unit. No arbitrary data is chosen from an existence assertion:
the conormal basis is specified by the images of all basis vectors.

## No longer needed

Removed the direct proof imports `Sheaf.Paper.KoszulComplex` and
`Sheaf.RingTheory.KoszulDualComplex` from the item: its unchanged public imports
already expose their definitions. Their modules and definition nodes remain
transitively needed; no whole module is claimed pruned from the targets' closure.

The original direct proof dependency `lem-sc-exterior-power-dual-pairing` is now
used in the two calculation nodes, rather than in the combining proof. It remains
needed below them and is not pruned. All other original proof dependencies remain
needed either directly or transitively. The node copy records the two new
calculations and the Mathlib exterior-power basis needed by the above-top helper.
The other original direct proof dependency absent from the new `proof_deps` is
`def-weil-pbc-koszul-regular-sequence`: its vanishing computation is now used by
`lem-sc-koszul-dual-below-top-homology`, while the original regularity hypothesis
is still passed to that theorem and the conormal-basis theorem. Both removed
original direct dependencies remain transitively needed; no original mathematical
calculation or unit-level route is discarded.

Second reading also removed redundant imports `Mathlib.Algebra.Homology.QuasiIso`
and `Mathlib.LinearAlgebra.Finsupp.VectorSpace` from the item, and the redundant
`public import Mathlib.LinearAlgebra.Basis.Defs` from the new top-calculation module.
The remaining imports already expose these declarations; the original module's
public imports are unchanged. These removals prune import lines, not whole modules.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature error was found. The planned elementary top
cokernel calculation is substantial Lean glue: top exterior bases, the image of
signed contraction, and identification of categorical homology with that quotient.
It is isolated with determinant normalization in the top calculation node.

`KoszulRegularSequenceDualComplex` has stronger cohomology results, but they depend
on this item's comparison quasi-isomorphism through comparison existence.
import_direction.py refuses that import as a cycle, so those results cannot be
used to close this item.

The local literature .tex and unit _section.md files are not present on this
machine; the unit JSON was read, and the actual source proof was read at
[Stacks Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ).
No blueprint unit or chapter was edited. LeanSearch returned Internal Server Error
for both new calculations; this is recorded as unavailable. LeanFinder and Mathlib
source searches found no exact computation, and blueprint_refs.py found no existing
blueprint match for Koszul cohomology or conormal comparison.

## New nodes

`lem-sc-koszul-dual-below-top-homology`, in
`Sheaf.RingTheory.KoszulDualBelowTopHomology`, states only the lower-degree vanishing
part of complementary Koszul duality. Its proof uses the complementary-wedge
isomorphisms and the given original positive-homology vanishing.

`lem-sc-koszul-conormal-top-homology`, in
`Sheaf.RingTheory.KoszulConormalTopHomology`, states only invertibility of the top
homology map, assuming the specified conormal basis. Its proof computes the top
cokernel and identifies the normalization with multiplication by a unit sign.
No change records are needed because existing interfaces are unchanged.


## Second reading by D3

1. **Interfaces: pass.** Compared the item with the repository by `diff` and
   checked its existing theorem signature byte for byte. Its statement, docstring,
   visibility, definitions and public imports are unchanged. The two additional
   modules introduce only their named calculation statements; no change record
   or forced adaptation is needed.
2. **Proof and axioms: pass as a decomposition.** All three files compile with
   `lcompile.py`. There are exactly two `sorry`s, in the two reported public
   calculation theorems, and none in a definition, anonymous or private theorem.
   Scanned for forbidden declarations and implementation attributes: none.
   Scratch `#print axioms` checks of the original theorem and both new theorems
   show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The fully proved private above-top helper uses only the three allowed axioms,
   with no `sorryAx`.
3. **Split statements: pass.** Read both statements, their full docstring proofs,
   matching nodes, and the actual signed boundary and determinant normalization.
   Lower vanishing asks only about n < r and does not mention a comparison map;
   top invertibility needs no regularity and asserts only one homology degree.
   Neither restates the original quasi-isomorphism. Checked r=0 (I=0 and no
   lower degrees), r=1 (incoming image generated by f_0), r=2 (unit sign -1),
   I=A, the zero ring, and characteristic 2. The conormal basis is fixed on
   every basis vector, so its existence is not an arbitrary-witness data hole.
   Independent searches used LeanFinder's complementary perfect-pairing query,
   Loogle's homology/single query, and Mathlib grep for complementary wedges,
   dual contraction, and Koszul homology, plus `rg` through both library roots.
   They found useful pairing and single-homology results, but no missing exact
   calculation. The stronger comparison results in
   `KoszulRegularSequenceDualComplex` depend on this item through comparison
   existence and would create an import cycle. Neither open calculation can be
   closed by a short existing-lemma application.
4. **Route and pruning: pass after import cleanup.** Read the original
   `proof_deps`, the basis theorem, Koszul definitions, and unit JSON
   `dag/units/sk-thm-picard-duality.json`. The new proof retains the conormal-basis,
   complementary-wedge vanishing, top-cokernel and normalization route of the
   original proof plan. No unit statement, step or `realized` entry changes.
   The above-top calculation is proved directly, without regularity. Both old
   dependencies moved out of the combining node are explicitly accounted for
   under No longer needed; they are still needed below the new nodes. Removed
   three redundant import lines after scratch compilation confirmed they were
   unnecessary; all proof-only imports that remain are plain `import`.
5. **DAG: pass.** Checked the unchanged original statement and Lean record;
   the updated proof steps, dependency union and origin describe the actual
   degree-by-degree combining proof. Both new nodes have the required source,
   self-contained statement, dependencies, mathematical proof, search records,
   creation and blueprint provenance, chapter, unit, and verbatim Lean signature.
   Both open calculations are recorded as split, not as proved.

Changes by the second reader: removed the three redundant imports listed above
and made the report's accounting of the old regularity dependency explicit.
The proof bodies and split statements needed no repair. This remains one original
hole closed and two holes added (net -1), with no whole module pruned.
