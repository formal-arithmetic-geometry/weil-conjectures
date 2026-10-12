## What changed

Replaced the remaining hole in `Sheaf.RingTheory.RegularSequenceKoszulRegular` by
induction on the sequence length, using Mathlib's append characterization of
`IsWeaklyRegular`. The original three public signatures and existing corollary
proofs are unchanged. The empty sequence, the conversion between categorical
homology vanishing and elementwise exactness, and the entire cone cycle chase
(including degree one) are proved in private helpers.

Added two support modules. `Sheaf.RingTheory.KoszulTensorZerothBoundarySaturation`
is proved: contraction in degree one becomes `Finsupp.linearCombination`, and
its tensor boundary image becomes `Ideal.ofList (List.ofFn f) • ⊤`. Scalar
injectivity on the quotient then lifts degree-zero elements to boundaries.
`Sheaf.RingTheory.KoszulTensorConeCoordinates` states the remaining exterior-power
coordinate isomorphisms and their differential formulas, without any regularity
hypothesis. Its proof is the only new hole. Both new modules have matching nodes;
the parent's proof and dependencies now follow the actual Lean reduction.

Added proof-only imports of the two support modules and Mathlib's exterior-power
basis API. Removed the redundant direct proof import of `Sheaf.Paper.KoszulComplex`;
that module remains needed and available through the existing public import of
`Sheaf.RingTheory.KoszulRegularSequence`.

All three delivered modules compile together without warnings through `lcompile.py`.
The boundary-saturation proof was compiled incrementally against the concrete
contraction definition. The independent second reader still needs to review the
new cone-coordinate statement; this report does not supply their reading.

## Proved and sorry left

Hole closed in the item:
`RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular`
(node `lem-weil-pbc-regular-sequence-koszul-regular`). Its proof is complete Lean
from the support statements. There are no `sorry`s left in the item module.
The two previously proved declarations
`RingTheory.Sequence.IsRegular.isKoszulRegularOn` and
`RingTheory.Sequence.IsRegular.isKoszulRegular` retain their existing proofs.

New theorem proved with no hole:
`ExteriorAlgebra.koszulTensor_zeroth_boundary_saturation`
(node `lem-weil-pbc-koszul-tensor-zeroth-boundary-saturation`). Its private
linear-equivalence construction and all private helper proofs contain no hole.

Only hole added and left in the delivery:
`ExteriorAlgebra.exists_koszulTensorConeCoordinates`
(node `lem-weil-pbc-koszul-tensor-cone-coordinates`), whose proof is exactly
`:= by sorry`. Its docstring gives the complete basis-splitting proof and
source. This is only the coordinate/differential step of the argument: it
asserts no homology vanishing, contains no weak-regularity hypothesis, and
is used by a genuine induction and a fully proved cycle chase.

Counts: one original hole closed, one lower hole added, zero net holes removed.
This is a decomposition, not a claim that the original theorem is axiom-clean.
It continues to depend on the existing Koszul-complex well-definedness theorems,
and additionally on the named cone-coordinate hole.

Edge cases checked mathematically: an empty sequence has no positive exterior
basis vectors; the saturation statement for an empty sequence is injectivity
on `M`; for the zero module both support statements hold; the cone-coordinate
formulas include the special degree-one-to-zero differential and all terms
above the rank. The signs are valid in every characteristic. No nonzero-final-
quotient hypothesis or nontrivial-ring hypothesis is introduced.

## No longer needed

Removed direct import: `Sheaf.Paper.KoszulComplex` (redundant, still transitively
needed). No original DAG dependency or module is pruned: the Koszul complex,
Koszul regularity predicate, and Mathlib regular-sequence predicate are all
used. The basis node is now recorded explicitly because the empty-case proof
uses it. The two new support nodes realize the original quotient and cone
steps. No unit or chapter route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's step 2 describes the cone coordinates but had only the complex
*definition* as a dependency; no Lean theorem in that dependency supplied
the coordinates. That missing interface is now the cone-coordinate node.
The degree-zero boundary calculation likewise had no stated interface, but
it has been proved directly rather than left as another hole. The argument's
mathematical route and all original statements are retained.

The local repository has no `literature/stacks-project/more-algebra.tex`.
The cited Stacks Tags 062F and 0629 were read on the Stacks website instead.
LeanSearch was attempted for both new statements and returned Internal Server
Error; the nodes record that unavailability without claiming a search verdict.
LeanFinder, Loogle, local source grep, and whole-blueprint searches were used.
No existing duplicate cone-coordinate or saturation statement was found.
No forced adaptations or interface changes were needed.

## New nodes

`lem-weil-pbc-koszul-tensor-cone-coordinates`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-koszul-tensor-cone-coordinates.json`,
module `Sheaf.RingTheory.KoszulTensorConeCoordinates`. One remaining theorem
states the degreewise cone coordinates with both differential formulas;
its source is Stacks Tags 0628 and 0629, and it realizes step 2 of the original
node. It has no regularity hypothesis and is strictly one part of the argument.

`lem-weil-pbc-koszul-tensor-zeroth-boundary-saturation`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-koszul-tensor-zeroth-boundary-saturation.json`,
module `Sheaf.RingTheory.KoszulTensorZerothBoundarySaturation`. Its theorem is
proved from the concrete differential and Mathlib's quotient and tensor APIs.
It realizes the degree-zero calculation in step 1 and the degree-one lifting
in step 3 of the original node. There are no change records.

## Second reading by U1

1. **Existing interfaces: pass.** Compared the item module with the read-only
   repository using `diff -u`. All three existing public declaration signatures,
   their docstrings, and the two existing corollary proof bodies are byte-for-byte
   unchanged. Only proof bodies, private proof helpers, and proof-only imports
   are added. There are no changed public definitions, target statements, or
   forced adaptations, and no change record is required.

2. **Proof and axioms: pass as a decomposition.** Independently compiled all
   three modules together through `lcompile.py --all`, without errors or
   warnings. Read the complete induction, empty-case argument, conversion of
   categorical homology to module exactness, boundary-range calculation, and
   cone cycle chase. Scanned every delivered Lean file: the sole explicit hole
   is the reported public coordinate theorem, exactly `:= by sorry`; there is
   no forbidden declaration or hole in data. Scratch copies with `#print axioms`
   for the main theorem and both support theorems compile and report only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The saturation
   theorem has no local hole but inherits `sorryAx` from existing Koszul
   well-definedness proofs; it is not claimed axiom-clean. The main proof
   destructures the coordinate existence theorem locally, without defining
   data by choosing an arbitrary witness of an unproved existence theorem.

3. **New statements: pass.** The coordinate statement is precisely the
   exterior-power splitting, with no regularity or acyclicity assumption; it
   does not restate the item. Its source and docstring supply the basis proof.
   Checked the last-generator-first convention against contraction: the
   second coordinate has a minus sign in all characteristics. For an empty
   prefix, the degree-one term is the scalar tensor factor, its boundary is
   multiplication by the final element, and all higher terms vanish. For a
   prefix of rank one, `d(e_last wedge e_prefix)` has coordinates
   `(f_last e_prefix, -f_prefix)`, as stated. Above the rank, and for the zero
   ring or zero module, the same splitting remains valid. Saturation requires
   exactly injectivity on the quotient by boundaries, and its proof establishes
   that boundary image directly, including the empty sequence. Independently
   reread Stacks Tags 0629 and 062F online. Repeated LeanFinder using “one extra
   basis vector / adjacent exterior powers / contraction”, Loogle for
   `contractLeft`, and msearch grep for mapping cones and exterior-power sums;
   searched the repository's Sheaf and upstream sources for cone/Koszul and
   boundary/saturation terminology. The hits supply contraction and generic
   mapping-cone APIs, not this Koszul coordinate interface. No duplicate or
   shortcut was found. Closing this coordinate construction is substantial
   basis and tensor API work, not a few-minute repair.

4. **Route and pruning: pass.** The proof uses Mathlib's append regularity
   characterization, exterior basis, quotient, tensor, and module exactness
   APIs, then only the explicitly stated cone-coordinate hole. The induction
   and degree-one boundary calculation are genuine reductions. Every original
   proof dependency is still used; the removed direct KoszulComplex import is
   redundant through the unchanged public KoszulRegularSequence import. Checked
   the support imports: RegularSequence is needed publicly for `Ideal.ofList`,
   and ExteriorPower.Basic is needed only by the saturation proof. The unit
   `sk-thm-p1` realized statement and steps are unchanged; this item is below
   the unit level and the original final-generator route is retained. No
   original dependency node or module is pruned.

5. **DAG and report: pass.** Diffed the existing node: only `proof`,
   `proof_deps`, and `proof_origin` change. Their dependencies are the union
   of the actual proof steps. Both new nodes have source, complete proof
   plans, search records, creation metadata, blueprint ancestry, the matching
   chapter and unit, and Lean statement records. The cone node isolates the
   unproved coordinate calculation and the saturation node records its
   completed proof. The report names the original hole closed and the sole
   hole added, with their nodes, and correctly counts zero net holes removed.

Second reading changed only this report, adding the independent review and
clarifying the inherited `sorryAx` in the locally proved saturation theorem.
No mathematical or Lean repair was needed. Temporary import-minimization
experiments were reverted after demonstrating those imports are required.
