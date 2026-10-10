# lem-weil-pbc-projective-dimension-ses-kernel

Source: Stacks Algebra Lemma 065S (lemma-exact-sequence-projective-dimension), part (1), using Lemmas 065R (lemma-projective-dimension-ext) and 065P (lemma-reverse-long-exact-seq-ext). Read their statements and proofs in `algebra.tex`; verified the tag-label mappings in `tags/tags`.

The item now has three steps. For any module N, 065R turns the resolution bounds for M and M'' into the vanishing of Ext^{m+1}(M,N) and Ext^{m+2}(M'',N). The exact segment of 065P forces Ext^{m+1}(M',N)=0. The converse direction of 065R yields the claimed resolution of M'. This includes m=0 and the zero modules; no Noetherian or finiteness hypothesis enters.

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-projective-dimension-ses-kernel.json`: split item; statement unchanged.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-projective-dimension-ext-characterization.json`: Stacks 065R, unsplit; Mathlib's Ext-defined dimension does not give the bounded-resolution equivalence in one line.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ext-long-exact-first-variable.json`: Stacks 065P, Mathlib leaf, `CategoryTheory.Abelian.Ext.contravariantSequence_exact` and `precomp_mk₀_injective_of_epi` in `Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean` (lines 268 and 299).

Blueprint: searched the whole blueprint with `tools/blueprint_refs.py search` for `projective dimension`, `exact sequence projective`, `065S`, `Ext groups vanish`, `projective resolution`, and `long exact sequence Ext`. No blueprint node states these algebraic results. The item and both new nodes carry the step-7 ancestor `thm-weil-pbc-finite-etale-lifting` and the via chain; their `same_as` fields are empty lists.

Attachments: none.

WANTED: none.

The existing Mathlib candidate on the item is only an Ext-defined analogue. It needs the unsplit 065R bridge before it can prove the resolution-length statement. No error found in the item's statement or blueprint route.

Unfinished: the new 065R node needs its own Stage 1 split.

## Review by E1

I read Algebra Lemma 065S (`lemma-exact-sequence-projective-dimension`), 065R (`lemma-projective-dimension-ext`), and 065P (`lemma-reverse-long-exact-seq-ext`). The item retains the short exact sequence and the bounds on the middle and quotient modules. The new 065R statement exactly gives the bounded-resolution/Ext-vanishing equivalence. The new 065P statement matches the contravariant long exact sequence; its Mathlib leaf is `CategoryTheory.Abelian.Ext.contravariantSequence_exact` in `Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean:268`, with the degree-zero injection at line 299. Blueprint searches and fields were checked by the worker; no same-as blueprint node was found.

Step 1 applies 065R at degrees m+1 and m+2; the inequalities are correct even at m=0. Step 2 uses the exact segment Ext^{m+1}(M,N) to Ext^{m+1}(M',N) to Ext^{m+2}(M'',N), so exactness and the two zero outer terms force the middle group to vanish. Step 3 applies the converse direction of 065R for arbitrary N. The cited node statements supply all non-elementary facts, and the Mathlib result is recorded as an ingredient for the 065P statement rather than as the full resolution theorem. I checked zero modules and m=0; no finiteness or Noetherian hypothesis is silently used. No A-F issue remains and no worker repair was needed.
