## What changed

Proved `AlgebraicGeometry.exists_etale_lift_isIdempotentElem` in
`Sheaf.RingTheory.LiftIdempotentUpstairs`, keeping its full signature unchanged.
The proof chooses a representative, applies the existing integral annihilator and
étale coprime-factorization declarations, evaluates the factors in the tensor
product, makes their values coprime by localization, and constructs the idempotent
from a Bézout identity. Both canonical quotient equivalences and their action on
representatives are proved, including compatibility with the further base change.

Added `Sheaf.RingTheory.EtaleMakeTensorPairCoprime`, with the proved theorem
`AlgebraicGeometry.exists_etale_isCoprime_tensor_of_isCoprime_quotient`.
It realizes the separation/localization steps of Stacks 07M4, using the existing
separation declaration. Its private helper proves that localization at an element
congruent to one induces a bijection on the quotient, by constructing inverse maps.
The integral tensor map and the closed-image disjointness argument are also proved.
This theorem only constructs coprimality, and assumes no idempotent or zero-product
condition; it is a strict part of the original argument, not a restatement.

Added proof-only imports of `Mathlib.RingTheory.TensorProduct.Quotient`,
`Mathlib.RingTheory.Coprime.Lemmas`, and the new
module. The item's public imports are unchanged. Updated its docstring and DAG
proof to the actual route and added the new theorem's node. No statement or
existing definition changes, and no change record is required.

## Proved and sorry left

The original module had one sorry and now has none:
`AlgebraicGeometry.exists_etale_lift_isIdempotentElem` is proved.
Its private helper `tensor_quotient_equiv` is proved.

The new module also has no sorry:
`AlgebraicGeometry.exists_etale_isCoprime_tensor_of_isCoprime_quotient` and its
private helper `quotient_localization_bijective` are proved.
No sorry is split off or added by this delivery.

The proof uses these existing declarations, whose own proofs remain items:

- `Polynomial.exists_monic_aeval_eq_zero_map_eq_of_isIdempotentElem_quotient`
  (`lem-weil-pbc-integral-idempotent-annihilating-polynomial`).
- `Polynomial.exists_etale_lift_coprime_factorization`
  (`lem-weil-pbc-lift-coprime-factorization-etale`).
- `PrimeSpectrum.exists_one_mod_mem_of_disjoint_closure_image_zeroLocus`
  (`lem-weil-pbc-separate-image-closed-from-closed`).

Both delivered modules compile together, in import order, with the prescribed
local compiler and no warnings. The theorem includes zero rings, `I = ⊤`,
`I = ⊥`, and the idempotents zero and one; no nontriviality or proper-ideal
hypothesis was introduced. The new lemma's localization may be the zero ring,
which correctly handles the zero-quotient case. With `I = ⊥`, separation and the
quotient condition force the localization to preserve the base ring quotient.

## No longer needed

Pruned `lem-weil-pbc-spec-clopen-idempotent`. The main proof does not use
`PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen` or
`PrimeSpectrum.isIdempotentElemEquivClopens`: the formula `e = u*x` proves
idempotence, and multiplication of the reduced Bézout identity proves the lifting
condition directly. There was no standalone Sheaf module imported for this
Mathlib leaf, so no such module was removed.

Removed the item's direct proof import
`Sheaf.RingTheory.SeparateImageClosedFromClosed`; it is still imported and used by
the new module, and is NOT pruned from the theorem's dependency closure.
The original direct DAG dependencies integral-base-change, integral-spec-closed-map,
principal-localization-open-immersion, and separation are now dependencies of the
new proved node. They remain needed transitively. Étale composition also remains
needed directly. No unit realization or unit route is bypassed.
The old proof dependency `def-weil-etale-morphism` is now only a statement
dependency; the definition remains required by the unchanged statement.
The second reading also removed the unused proof import
`Mathlib.Algebra.Ring.Idempotent`.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's clopen construction was unnecessary:
the explicit Bézout formula already mentioned in its step 6 removes both the
existence and uniqueness applications of the clopen correspondence. Reduction of
the second factor need not be simplified to a signed complementary idempotent:
evaluating the coprime polynomial powers gives the required quotient coprimality,
and its zero product with the first factor gives the reduction calculation.

The local `literature/stacks-project/more-algebra.tex` and blueprint unit source
are absent in this read-only clone. The unit record `dag/units/sk-thm-p1.json`
was read, and Stacks Tag 07M4 was read in full at
https://stacks.math.columbia.edu/tag/07M4. The proof follows its factorization,
closed-image separation, and localization route. LeanSearch returned HTTP 500;
this is recorded as unavailable, not as a no-match result. Loogle, LeanFinder,
and source grep were actually run through `msearch.py`, and their records are in
`searches.jsonl`. Searches of the blueprint and existing modules found no duplicate
of the coprimality/localization statement.

## New nodes

`lem-weil-pbc-etale-make-tensor-pair-coprime`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-make-tensor-pair-coprime.json`,
realized by the proved declaration in
`lean/Sheaf/RingTheory/EtaleMakeTensorPairCoprime.lean`.
It states the separation/localization part of the source proof for a tensor pair
coprime modulo an extended ideal. It inherits the item's chapter and unit and
blueprint ancestor, records the actual searches, and names exactly the existing
nodes used by its natural-language proof. There are no new unproved nodes and
no change records.

## Second reading by N2

1. Compared the entire delivered main module and node against the repository with
   `diff`. The existing theorem signature is byte-for-byte identical, and its
   public imports are unchanged. There are no changed existing definitions,
   hypotheses, conclusions, or statement fields, and no change record is needed.
   Verdict: pass.
2. Independently compiled both modules in import order with `lcompile.py`, with
   no errors or warnings. Neither module contains `sorry` or a prohibited
   declaration mechanism. Scratch copies with `#print axioms` for both public
   theorems and both private helpers show only `propext`, `Classical.choice`,
   `Quot.sound`, and (for the public theorems) `sorryAx` from the existing open
   separation, annihilator, and factorization declarations. Both private helpers
   use only the three permitted axioms. Verdict: pass as a reduction to existing
   open nodes, not a claim that the entire dependency closure is sorry-free.
3. No unproved statement was split off. Read the new proved coprimality theorem
   and its full natural-language proof and node. It assumes no idempotence or
   zero-product condition and proves only the separation/localization step, so
   is strictly part of the original argument. Checked zero rings, zero quotient
   (`I = top`), `I = bottom`, and the original idempotents zero and one: no
   proper-ideal or nontriviality assumption is needed; localization at zero is
   allowed when the quotient is zero. Independently searched with LeanFinder
   for unit-ideal generators after localization, Loogle `IsCoprime,
   IsLocalization`, and source grep for quotient/coprime and localization
   variants (the actual patterns are in `searches.jsonl`). Also searched both
   library roots directly. Results supply no duplicate of the new theorem.
   Verdict: pass.
4. Read the proof top downward: the tensor quotient equivalences are Mathlib
   constructions, evaluation and the explicit Bezout formula close the algebra,
   and only the existing three open source lemmas remain dependencies. There is
   no shorter matching theorem in the independent searches. Checked every old
   proof dependency against the new direct and transitive dependencies, and
   `dag/units/sk-thm-p1.json` including `realized`: no unit step is bypassed.
   The clopen-idempotent node is the sole substantive pruning; the etale
   definition remains a statement dependency. Verdict: pass after import and
   report cleanup.
5. Read both delivered nodes beside their Lean declarations. Their proof steps,
   unions of `proof_deps`, source-based `proof_origin`, and Lean records agree
   with the actual code; the new node has the required creation, blueprint,
   chapter/unit, source, searches, and verbatim normalized signature fields.
   Verdict: pass.

Changes by the second reader: removed the unused
`Mathlib.Algebra.Ring.Idempotent` proof import; restricted the new module's
public integral-closure import to `Algebra.Defs` and made `Algebra.Basic` a
proof-only import, since its tensor integrality and surjective transport facts
are used only in the proof; completed the pruning report for the old etale
definition dependency; added this independent review. No proof body or
statement needed repair.
