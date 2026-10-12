## What changed

Replaced the proof of `CategoryTheory.essentiallyConstantPro_hom_colimit` with a complete
construction. The map is the `ColimitType` quotient lift of the cone maps
`f ↦ u.app j ≫ f`; surjectivity uses the chosen retraction and injectivity uses a common
cofiltered stage followed by the factorization clause. No imports were added or removed.

## Proved and sorry left

Closed: `CategoryTheory.essentiallyConstantPro_hom_colimit`
(node `lem-pc-essentially-constant-pro-hom-colimit`), the sole original hole.
Added holes: none. Remaining holes: none. This is a proof, not a decomposition.
No new nodes were added.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

None.

## New nodes

None.

## Second reading by E1

1. **Interface preserved: PASS.** Diffed the sole delivered module against the
   repository version. After the repair below, everything through `:= by` is
   byte-identical: both public imports, universes, docstrings, binders, hypotheses,
   conclusion, and visibility. No definition or existing statement changed, and
   no change record is necessary.
2. **Proof and trust: PASS.** Compiled the delivered file with `lcompile.py` without
   errors or warnings. Compiled a scratch copy with
   `#print axioms CategoryTheory.essentiallyConstantPro_hom_colimit`: only
   `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, forbidden declaration, or
   data selected from an unproved existence theorem. The map is constructed
   explicitly as `F.descColimitType c`; `r` and the refinement arrows are
   witnesses of the theorem's explicit hypothesis, eliminated within its proof.
3. **Split statements: PASS (none).** No new declarations, new nodes, or lower
   holes. Read Definition [05PU](https://stacks.math.columbia.edu/tag/05PU),
   part (2), and Lemma [05PZ](https://stacks.math.columbia.edu/tag/05PZ).
   The retraction and factorization hypotheses match that definition with Lean's
   left-to-right composition. The singleton-index case gives the ordinary
   retraction bijection; an empty index cannot satisfy `h.1 : IsCofiltered J`.
4. **Route and pruning: PASS.** Read the node's three elementary steps and
   `dag/units/sk-thm-picard-duality.json` (`realized` has no entry for this node).
   The proof keeps the Hom-computation route: naturality constructs the quotient
   map; `u.app j₀ ≫ r = 𝟙 X` proves surjectivity; injectivity uses a common
   stage `l`, then the factorization at `l` to obtain `m`. Both representatives
   at `m` factor through the same `D.map q ≫ r`, so `hxy` identifies them.
   Read Mathlib's `descColimitType`, `ιColimitType_jointly_surjective`, and
   `ιColimitType_eq_of_map_eq_map`; these supply the quotient operations exactly.
   Searched `lean/Sheaf/CategoryTheory` and upstream CategoryTheory for
   essential-constancy results, and repeated LeanFinder with "A cone with an
   eventual retraction gives a bijection from the filtered colimit of
   contravariant Hom sets". Hits concern universal properties, partial adjoints,
   or the whole coyoneda diagram, not this eventual-factorization conclusion.
   The nearby pro criterion is the converse; the ind Hom theorem is still open.
   No shorter applicable declaration was found. Both public imports occur in
   the existing signature (`IsEssentiallyConstantProDiagram` and `ColimitType`),
   so neither is proof-only or unused. Old `proof_deps` is empty: nothing to prune.
5. **DAG agrees: PASS.** The existing node's steps are precisely the cocone,
   retraction-surjectivity, and common-refinement injectivity argument written
   in Lean. `proof_deps = []` and the document-based `proof_origin` remain
   accurate; no node edits are needed and the unit record is unchanged.

Changed the proof's `haveI : IsCofiltered J := h.1` to ordinary `have`, which
registers the same local instance. Removed the unnecessary module-wide
`linter.style.haveILetI` suppression and its inaccurate change record.
Recompiled successfully; the mathematical construction needed no repair.
