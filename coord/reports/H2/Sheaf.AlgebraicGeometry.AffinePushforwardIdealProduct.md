## What changed

Proved `AlgebraicGeometry.Scheme.affine_pushforward_ideal_product` with its exact original
signature and both conclusions. The five private helpers are fully proved: they transfer
abelian image ranges to categorical images, calculate the product range on affine opens,
calculate the extended product range on affine preimages, detect zero morphisms on the
affine basis, and obtain subobject inequalities by kernel lifts. No public declaration,
definition, visibility, or public import changed. Added the proof-only import
`Mathlib.AlgebraicGeometry.Morphisms.Separated` for affine implies quasi-separated.
Updated the item's DAG proof, dependency union, and proof origin to match this proof.
The unit `sk-thm-p1` realized route is unchanged. The static checker requires a record
for the proof elaboration opens; it is
`coord/changes/affine-pushforward-ideal-product-proof-opens.md`. This introduces no
public signature or meaning change and requires no downstream adaptation.

The proof is the source's computation I(M_A) = ((IB)M)_A. Naturality of the chosen
adjunction unit and its structure-sheaf characterization give the pure-product formula;
tensor induction absorbs b into the module section, with b = 1 for the reverse inclusion.
Sheaf separatedness and the abelian image/kernel description give global equality.
The arbitrary inclusion interface is handled directly, without choosing ideal-sheaf data.

Validation: the final pruned module compiled cleanly with lcompile.py, including all
five private proofs. The import-direction check permits the added Mathlib import.
Searches used msearch leanfinder (affine ideal-product projection formula), loogle
(Subobject.mk and image inclusion), msearch grep, and rg across both library roots and
Mathlib. The source projection formula requires an invertible factor, so it cannot
replace the general ideal calculation. Read Stacks Tag 01YP on the official website;
its statement and two proof paragraphs give precisely the two conclusions and computation.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.affine_pushforward_ideal_product`
(node `lem-weil-pbc-affine-pushforward-ideal-product`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The imported declarations remain the independent project's dependencies, as stage 3
requires; this report does not claim they have all been proved without reachable holes.

## No longer needed

Removed the proof-only imports:

- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`:
  node `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` is not needed by this proof.
  Its product section clause is derived directly from tensor and image sections in a
  fully proved private helper. No powers, quotients, or restriction formula is used.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: its direct import is redundant;
  the product's statement imports already supply the monoidal structure. The underlying
  tensor-product definition node remains needed, so this is import pruning only.
- `Sheaf.AlgebraicGeometry.TensorPullback`: its direct import is redundant through the
  existing public structure-sheaf comparison import. The pullback definition node remains
  needed, so this is import pruning only.

No other original proof dependency is removed. Whether these modules leave the entire
target closure depends on their other importers; only this item's dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The planned ideal-times-module affine sections theorem accepts `IdealSheafData`, whereas
this theorem accepts an arbitrary mono `I ⟶ O_X`. The extended ideal map need not be mono
on a non-flat morphism. No interface repair is necessary: the direct section-range helper
requires quasi-coherence of its source but no monicity and works for both product maps.
Mathlib pullback quasi-coherence also concerns `Modules.pullback`, so the proof explicitly
transfers it to `tensorPullback` by uniqueness of left adjoints.

No false statement, new node, forced adaptation, or target-statement change was found.

## Second reading by H2

1. **Statements and accidental changes.** Compared the delivered module with the repository
   version byte-for-byte at every existing declaration signature. The target statement is
   unchanged; only proof text, private helpers, proof-only imports, and the DAG proof metadata
   differ. Verdict: passes.
2. **Proof and axioms.** Compiled the complete sandbox item with `lcompile.py --all`; it
   succeeds with no errors and the module contains no `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by`. The proof uses only the permitted categorical constructions.
   Verdict: passes.
3. **Statements and split-offs.** The five helpers are private proof infrastructure, so no
   split-off public statements or new nodes were introduced. The public theorem retains its
   original hypotheses and both conclusions; no weaker replacement is used. Verdict: passes.
4. **Route and pruning.** The proof follows the unit route: affine tensor/image section
   calculations, then affine-basis locality and subobject comparison. Removed imports are
   proof-only or redundant and are recorded above; no unit step is bypassed. Verdict: passes.
5. **DAG agreement.** Updated `proof`, `proof_deps`, and `proof_origin` describe the helpers
   and imports actually used. The realized unit route is unchanged, and the proof-opens change
   record is present. Verdict: passes.

Changed during second reading: added this review section only; no Lean declarations or DAG
   statements were altered.
