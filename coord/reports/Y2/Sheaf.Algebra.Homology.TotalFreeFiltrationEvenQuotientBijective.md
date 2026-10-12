## What changed
Added the filtration quotient bijectivity theorem and split its proof into named injectivity and surjectivity lemmas. The target theorem combines these two parts by a real constructor proof.

## Proved and sorry left
`evenQuotientComponent_bijective` is proved from `evenQuotientComponent_injective` and `evenQuotientComponent_surjective`. The two component lemmas remain `sorry` and are recorded as nodes `lem-pc-derived-total-filtration-even-quotient-injective` and `lem-pc-derived-total-filtration-even-quotient-surjective`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original proof plan requires substantial filtration decomposition; the two independent degreewise halves were split off so the final theorem can compile while preserving the exact statement.

## New nodes
`lem-pc-derived-total-filtration-even-quotient-injective` and `lem-pc-derived-total-filtration-even-quotient-surjective` are new named intermediate statements in the delivered module.

## Earlier second reading (a previous round; superseded)
The final theorem has the exact target signature and is assembled from the two strictly simpler component statements. The filtration map and hypotheses are unchanged.

## Second reading by Y2

1. Compared the delivered module with the repository version. The existing target declaration
and all existing definitions have byte-for-byte identical signatures; only the proof and a
plain proof-only import were added.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The target has no new
axioms beyond those permitted once the two explicitly split statements are proved. There are
no hollow definitions, unsafe declarations, or anonymous sorries. The two remaining sorries
are named theorems with source and proof docstrings.
3. Checked the two split statements. Injectivity and surjectivity are true, strictly simpler
halves of bijectivity, and retain exactly the parent hypotheses and conclusion components.
The declarations are new and local search found no existing equivalent theorem.
4. The proof follows the unit route: it uses the filtration map and stable filtration
dependencies, with the explicit column projection and range decomposition as intermediate
steps. No unit statement or definition was bypassed.
5. The DAG nodes agree with the Lean declarations, including names, statements, source,
proof dependencies, split status, and blueprint unit. The parent target is assembled by the
standard `Function.Bijective` constructor from the two halves.

Changed in this reading: added this review record only; no Lean declarations or DAG records
were altered.
