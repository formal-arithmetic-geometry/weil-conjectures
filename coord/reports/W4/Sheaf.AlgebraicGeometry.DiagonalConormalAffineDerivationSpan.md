## What changed

Replaced the whole proof of
`AlgebraicGeometry.diagonalConormal_affine_derivation_span` with a complete Lean
proof from the affine diagonal ideal class map, the existing normalization
hypothesis, and Mathlib's tensor-ideal span theorem. Its signature and docstring
are unchanged. Added the private proof import
`Sheaf.AlgebraicGeometry.DiagonalConormalAffineIdealClass`.

The new module states the geometric part of the original plan: tensor-product
coordinates on the affine fibre-product open and a surjective linear map from
its multiplication ideal to the actual conormal sections. Its formula is pinned
to the actual kernel inclusion and the canonical tensor-pullback unit for EVERY
ideal element. This theorem has no derivation parameter, no span assertion,
and no differential comparison or injectivity assertion. The parent independently
uses normalization to identify the images of tensor differences, proves that
these differences span the ideal subtype, and transports their span through the
surjective map. Thus the new hole is the geometric chart/unit calculation, not
the parent's assertion under another name or with its hypothesis repackaged.

Updated the parent's proof, proof_deps and proof_origin to match this route.
The new node retains the geometry dependencies of the original plan. The unit
route and all existing public signatures and imports are preserved. There are
no adaptations or changes to existing definitions.

Both delivered modules compiled cleanly together with lcompile.py. The source
calculation was read at https://stacks.math.columbia.edu/tag/08S2,
https://stacks.math.columbia.edu/tag/01R3 and
https://stacks.math.columbia.edu/tag/01KJ; the local Stacks TeX checkout is absent.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.diagonalConormal_affine_derivation_span`
(node `stage3-diagonal-conormal-affine-derivation-span`). The item has no sorry left.

Added one hole, with exactly the whole proof `:= by sorry`:
`AlgebraicGeometry.diagonalConormal_affine_ideal_class`
(node `lem-sc-diagonal-conormal-affine-ideal-class`), in its own new module.
Its docstring and node give the full geometric argument and source.

This delivery is a decomposition: one upper hole closed and one geometric hole
added, so the hole-count net is zero. The normalization and span transport are
proved; the geometric restriction and unit comparison remains to be formalized.
No data definition or private declaration uses sorry, and no axiom was added.

## No longer needed

No existing import was removed and no globally unnecessary module is claimed.
The parent's direct proof dependencies on `def-sc-diagonal-conormal`,
`lem-pc-module-pullback-adjunction`, `lem-weil-pbc-diagonal-immersion` and
`lem-weil-pbc-affine-conormal-sections-existence` now belong to the new geometric
node. They remain needed there and are not pruned from the route.

The proof needs no injectivity theorem, no affine differential/conormal
comparison theorem, and no chosen normalized derivation. In particular it does
not import the existing comparison/sections modules, which depend on the item
and would create a cycle. These were not imports of the original item, so this
is not counted as removal of an existing import.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect source was found. The original plan accurately
warns that affine_conormal_sections_existence applies to a closed immersion and
its ideal-sheaf module, rather than directly to the original diagonal and its
actual kernel. Reading its complete signature and proof confirmed that the
restriction comparison and compatibility of the chosen adjunction units must
still be supplied. That specific geometry is the new named theorem.

The new statement was checked on empty U (zero rings and section modules), on
A = R (zero multiplication ideal), and on R[x] (the usual nonzero diagonal
ideal and its quotient). For nonseparated f only the diagonal over U ×_V U is
used, so no global closed-immersion hypothesis is inserted. No global
quasi-coherence assertion about the actual diagonal kernel is made.

LeanSearch was unavailable (HTTP Internal Server Error). LeanFinder found
`diagonal_Spec_map` and closed-subscheme section-surjectivity lemmas, which do
not establish the actual kernel/tensor-unit restriction comparison. Loogle
confirmed `KaehlerDifferential.submodule_span_range_eq_ideal`. The logged grep
searches and additional rg searches located the generic affine conormal theorem
but no exact existing geometric class-map statement. The entire imported
blueprint was searched for conormal and diagonal statements; neither matching
result states the new unit-compatible affine class-map theorem.

## New nodes

`lem-sc-diagonal-conormal-affine-ideal-class`, in
`dag/nodes/sec-picard-framework/lem-sc-diagonal-conormal-affine-ideal-class.json`,
is realized by `Sheaf.AlgebraicGeometry.DiagonalConormalAffineIdealClass` and
`AlgebraicGeometry.diagonalConormal_affine_ideal_class`. It isolates the affine
geometric restriction, tensor coordinates, class-map surjectivity, and unit
compatibility from the parent's normalization/generation proof. It inherits the
parent's chapter, unit and blueprint ancestor, records the three executed search
kinds (including the unavailable service), and carries a complete source-based
proof in words. No change record is required because no existing interface changed.


## Second reading by W4

1. **Interfaces: pass.** Compared the delivered span module with the repository
   using diff. Only its proof and a plain proof-only import were added; the
   existing declaration signature and docstring are byte-for-byte unchanged.
   There are no adapted modules, changed definitions, or change records.
2. **Kernel proof and axioms: pass, with the reported open geometry.** Compiled
   both modules together using lcompile.py, without errors or warnings. Separate
   scratch copies with `#print axioms` for both declarations printed exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The only delivered
   sorry is the whole proof of `diagonalConormal_affine_ideal_class`; no data
   definition, private helper, or forbidden declaration was added. In particular,
   the parent eliminates the geometric existence theorem inside a proof, rather
   than defining data by choosing an arbitrary unproved witness.
3. **Split statement: pass as a strict geometric part of the argument.** Read
   its full statement, docstring and node, the actual diagonalConormal definition,
   the normalization definition, the pinned tensor-pullback adjunction theorem,
   and affine_conormal_sections_existence with its ideal-tensor proof. The latter
   applies to a restricted closed immersion and its ideal module; it cannot
   directly identify the original diagonal kernel or its restricted unit.
   Re-read Stacks Tags 08S2, 01R3 and 01KJ online. The new theorem supplies exactly
   that chart/class-map calculation, without a derivation, normalization, span,
   or differential comparison. The parent still proves normalization on tensor
   differences and their span transport independently. Checked empty U, A = R,
   polynomial A = R[x], and the local nature of the argument for nonseparated f:
   the source has the stated quotient map and no additional hypothesis is needed.
   Independent LeanFinder searches for sections of the pulled-back affine
   diagonal kernel found ideal-sheaf ring-kernel lemmas, not this class-map
   theorem. Loogle confirmed the existing ideal span and quotient results;
   msearch grep for kernel/tensor and rg over the library found no exact usable
   replacement. This geometric hole requires substantial restriction and
   pullback comparisons and cannot be closed by a short application of the
   existing affine conormal theorem.
4. **Route and pruning: pass.** Followed the parent top down: obtain the class
   map, specialize its formula to a tensor difference, apply hD, use Mathlib's
   A-module span theorem (not merely ideal generation), and map the span through
   a surjective linear map. No shorter existing scheme-level route was found.
   The parent has one signature import and one plain proof import; all three
   public imports of the new module provide symbols in its statement. No old
   import was removed. All four old proof_deps removed from the parent are listed
   in No longer needed and retained in the geometric node. Read the unit record:
   its realized fields are unchanged, and this isolates a node-level calculation
   without replacing a unit step or chapter route.
5. **DAG: pass.** Compared the existing node with the repository and checked
   the new node against Lean. The existing node changes only proof,
   proof_deps and proof_origin; its three proof steps match the actual reduction.
   The new node has the required source, full proof in words, searches, creation,
   blueprint ancestry, chapter/unit and matching Lean record. Its dependency
   union agrees with its stated geometric proof plan. No statement field changes.

Second reading changed only this report, adding the independent checks and their
verdicts. No Lean repair was needed. The delivery remains a decomposition:
one original hole closed, one strictly geometric hole added, net zero; no module
is claimed pruned.
