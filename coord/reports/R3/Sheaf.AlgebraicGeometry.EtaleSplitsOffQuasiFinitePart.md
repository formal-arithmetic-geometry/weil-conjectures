## What changed

Proved `AlgebraicGeometry.exists_etale_splits_off_quasiFinitePart`.
The proof enumerates isolated fibre points, applies the technical étale splitting,
proves finiteness of the finite union by induction and coproducts, and compares the
complementary fibre with an open subscheme of the original fibre. Mathlib's fibre
homeomorphism and Jacobson discreteness finish the finite-fibre case. Added a private
fibre open-immersion helper and private finite-union helpers.

## Proved and sorry left

The item's sole theorem `exists_etale_splits_off_quasiFinitePart` is proved. No `sorry`
was added or left in the item.

## No longer needed

No original import removed; only the proof import
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` was added (empty union case).
A trial import `Mathlib.Data.Fintype.EquivFin` was removed after compiling without it.

The route does not require these DAG leaves as separate steps:
`lem-weil-pbc-open-preimage-fibre-product` (use generic pullback pasting and stability of
open immersions instead), `def-weil-pbc-finite-type-algebra`, and
`lem-weil-pbc-finite-type-over-field-prime-intersection-maximal` (use Mathlib's already
proved Jacobson fibre and finite Jacobson discreteness instances). All other original
proof dependencies remain. No Sheaf or WeilConjectures module is pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omitted the concrete coproduct and fibre open-immersion glue; these
are supplied as private helpers. The statement is unchanged. The unit sk-thm-p1's realized statement and steps are
untouched. The source TeX is absent on this machine, so Stacks Tags
[02LP](https://stacks.math.columbia.edu/tag/02LP),
[02LN](https://stacks.math.columbia.edu/tag/02LN), and
[02NG](https://stacks.math.columbia.edu/tag/02NG) were read online.

The proof still depends on the existing sorry in
`AlgebraicGeometry.exists_etale_splits_off_isolated_points`
(node `lem-weil-pbc-etale-splits-off-isolated-points-technical`); it is the next existing
item, not a newly added hole. Net holes closed: 1; holes added: 0.
Local compilation passed without warnings, including the empty-family branch. The
delivery dry run also compiles and probes axioms; second reading is left to the reviewer.

## Second reading by R3

1. Compared the complete delivered module against the repository version and verified
   the existing theorem signature byte for byte, including both finite hypotheses and
   every conclusion. No definition or public import changed; the sole added import is
   proof-only. Verdict: unchanged statement and meaning.
2. Compiled the module locally without errors or warnings. No sorry or forbidden
   declaration occurs in it. A scratch copy with `#print axioms` for the theorem and
   all three private helpers shows only propext, Classical.choice and Quot.sound in
   the helpers, and additionally sorryAx in the theorem, coming from the existing
   `exists_etale_splits_off_isolated_points`. No arbitrary data is chosen from an
   unproved existence theorem in a definition. Verdict: a genuine reduction closing
   one hole, with zero holes added; not a decomposition into new holes.
3. No split-off statement or new node exists. Read all three proved private helpers:
   the disjoint-open union is a coproduct, induction includes Fin 0, and pullback
   pasting produces the open immersion of fibres when residue fields agree.
   LeanFinder search for finite morphisms on unions of disjoint open subschemes finds
   `IsFinite.instDescScheme`, already used; grep of Mathlib, upstream and lean/ found
   no replacement proving the full elementary-neighbourhood conclusion. Verdict:
   helpers are true, sufficient, and fully proved; no duplicate open lemma added.
4. Checked the enumeration, dependent fibre transport, avoidance contradiction, open
   image of a singleton, and finite-fibre conclusion. Read Mathlib Fiber's Jacobson
   instance and Topology.JacobsonSpace's finite discreteness instance. The empty
   isolated family is handled by the empty union branch; a finite empty fibre also
   satisfies the argument. All imports are needed by signatures or proof; the report
   lists exactly the three removed proof dependencies. Read sk-thm-p1's realized
   statement and steps: none is bypassed or changed by this below-unit reduction.
   Verdict: route and pruning accepted, no shorter full proof found.
5. Compared the node JSON: only proof, proof_deps and proof_origin differ. Checked
   every remaining dependency's Lean record or Mathlib match against the actual
   construction and instances; proof_deps is the union of step uses. No new node or
   change record is needed. Verdict: DAG agrees with Lean.

Second reading changed documentation only: added explanations to the three private
helpers and corrected outline steps 5 and 7 to describe pullback pasting and Mathlib
Jacobson discreteness instead of the pruned leaves. No proof or signature changed.
