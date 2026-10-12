## What changed

The target uses the hom and inverse of `affine_finite_free_model_term_iso_free`.
The new module proves that isomorphism by finite-basis reindexing, `tildeFinsupp`,
`mapFreeIso`, and the extension term formulas. Its imports used only by proofs
(`FreeModule.Finite.Basic`, `Adjunction.Limits`) are plain imports. The target's
new helper import is also plain. Existing signatures and definitions are unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.affine_finite_free_model_retracts` (the sole original hole).
Also proved: `AlgebraicGeometry.affine_finite_free_model_term_iso_free`.
Added holes: none. Sorry left: none in either delivered module. This closes one
original hole, rather than decomposing it into new holes.

## No longer needed

No imports or modules pruned. The old proof dependency
`def-affine-finite-free-model-complex` is still needed as a statement dependency
and imported; the target's proof now uses the proved term-isomorphism lemma.

## Where the brief, the DAG or earlier work was wrong

The first worker left the entire finite-basis transport argument as one stronger
isomorphism hole. This did not constitute a useful decomposition. The second
reading completed that argument using existing Mathlib APIs.
Tag 068C discusses finite-free Koszul resolutions, rather than stating the
transport assertion itself; the transport is the explicit basis calculation
recorded here. Tag 08C4 supplies the direct-summand criterion. Sources read:
https://stacks.math.columbia.edu/tag/068C and https://stacks.math.columbia.edu/tag/08C4.

## New nodes

`lem-affine-finite-free-model-term-iso-free`, in
`Sheaf.AlgebraicGeometry.AffineFiniteFreeModelTermIsoFree`, is fully proved.
No change records are needed. Searches found generic transport tools, no duplicate
of this model-specific statement. LeanSearch returned an Internal Server Error;
LeanFinder, Loogle and local searches succeeded.

## Second reading by E3

1. Compared the target module with the repository using `diff -u`: only a plain
   proof import and the proof body changed. The existing theorem signature is byte
   for byte unchanged. No existing definitions or target interfaces changed.
2. Compiled both modules locally through `lcompile.py`. The term-isomorphism proof
   reindexes an actual finite basis; no arbitrary existence witness defines data.
   Neither delivered file contains sorry, axioms, unsafe code, opaque declarations,
   extern or implemented_by. Explicit `#print axioms` in a scratch copy showed
   only propext, Classical.choice and Quot.sound for both declarations; no sorryAx.
   The delivery axiom probes and dry-run preflight also passed.
3. The proposed split was too close to the entire argument; repaired by proving it
   completely. Checked positive degrees (outside the embedding image), degree zero,
   zero modules, rank zero, the zero ring and the empty affine open. The finite-basis
   instance handles a subsingleton coefficient ring. The out-of-range proof uses
   the empty coproduct, with no nontriviality assumption. Searches used different
   terms: restriction preserving free modules and the mapFreeIso API; local searches
   included upstream restrictFreeIso and overIsoFreeEquiv. They are generic tools,
   not duplicates of the delivered statement.
4. The proof follows the explicit model from the top: extension term formulas,
   basis coordinates, tilde, restriction, inverse site equivalence, then retract.
   All remaining imports are used. No old proof dependency or module is bypassed:
   the affine model definition remains imported. Read sk-thm-picard-duality.json;
   its realized statement and step lists are empty, and this local transport
   calculation does not change the unit's route.
5. Read both node records against the Lean proofs. Updated the new node with the
   actual finite-basis and coproduct transport steps and exact multiline signature;
   the target's proof dependency is the proved isomorphism lemma. Its original
   definition dependency remains in stmt_deps. No new unproved statements remain.

Changes by the second reader: closed the helper hole; added two plain Mathlib
proof imports; supplied source/module documentation; corrected proof steps,
search records and dependency accounting; rewrote the report to count no new holes.
