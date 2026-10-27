# Q92: lem-sfb-separably-closed-field-colimit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-separably-closed-field-colimit.json — statement, now split; no exact Mathlib match.
- citations.json — one verbatim statement quotation per cited node per proof step.
- searches.jsonl — search-command records, retained without alteration.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched WeilConjectures by the exact node id and by separably closed / IsSepClosed and directed, filtered, colimit terminology. The field-theory declarations concern separable closures, finite extensions, root characterizations, or ring-equivalence transport, not this ring-colimit assertion. The isolated mention in ConstantCohomologicalDimension.lean concerns cohomological dimension and is not an attachment.

## Literature wanted

WANTED: none.

## Findings and changes

The statement is correct and unchanged; its statement dependencies are unchanged. Stacks algebra.tex Tag 04GI, lemma-colimit-henselian, explicitly asserts that the colimit of separably algebraically closed residue fields has the same property, but omits its proof. The delivered proof supplies that argument and is marked agent-written. I read that paragraph, the current blueprint finite-data lemma and its proof, the chapter record and current chapter text, the unit record, and the definition of separability in fields.tex Tag 09H1, definition-separable. The general-polynomial Bezout formulation actually used is stated explicitly in def-pc-separable-polynomial.

The full item is not a Mathlib leaf. Searches in two natural-language phrasings return Algebra.IsAlgebraic.isSepClosed, which needs algebraicity over a fixed field; that hypothesis is not available and was not added. The Loogle results include Polynomial.separable_map, a legitimate alternative for reflecting separability, but not the whole item. The proof avoids needing a new reflection node by descending the finite Bezout certificate with an existing node. Search results are recorded as run, in addition to preserving the imported searches.

## Not duplicates

No new nodes. Reused lemma-nagata-filtered-colimit-finite-data rather than creating polynomial-coefficient descent or separability-certificate descent nodes. Whole-DAG and whole-blueprint searches for separably closed fields, polynomial separability and filtered colimits found no existing node stating the item other than this item. The Tag 04GI nodes concern local-ring colimits, residue-field identifications, and root lifting, not a second version of this field assertion. In particular its parent lem-sfb-filtered-colimit-strictly-henselian-local already depends on this item and is not used, avoiding a cycle.

## Review by Q92

I checked the actual source assertion in Tag 04GI against the delivered statement: nonempty directed systems of fields are a valid instance of the residue-field situation, and the finite-data proof works even when the field embeddings are transcendental. There is no statement dispute. The inherited blueprint ancestry has from.node null, exactly as blueprint_refs.py ancestor reports; I retained its place and complete via chain, and searched same_as rather than inventing an ancestor. I changed neither chapter nor unit bindings, since this item is not the unit key theorem.

Step 1 uses def-pc-separable-polynomial, whose statement expressly supplies U and V with Uf+Vf'=1. This is an unpacking of that definition, with finite coefficient lists for p, U and V; no irreducibility or monicity is assumed. Both U=0 and V=0 are allowed by the padded zero coefficient lists.

Step 2 uses lemma-nagata-filtered-colimit-finite-data. I opened its full statement: it supplies simultaneous lifts of finitely many elements and finitely many equalities between ring expressions at a common stage. It assumes a nonempty directed index and a colimit of commutative rings, all present in this item. The displayed coefficient equations are integer-coefficient ring expressions, including the derivative factors r, so the lemma really applies to them. The finite bound N covers every possible product coefficient. This is a generic tool use from the Nagata unit, declared in split_report.tool_uses; it does not change the geometric unit route.

Step 3 uses def-pc-separable-polynomial again. Coefficient-by-coefficient equality gives the Bezout equation at the stage, hence separability by precisely its definition. The leading coefficient maps to a nonzero c_n, so it cannot itself be zero. This needs no reflection theorem, no flatness theorem and no extra field extension hypothesis. This short calculation is elementary, not a new node or a hidden lemma.

Step 4 uses the root formulation explicitly stated in def-pc-separably-closed and the finite-sum evaluation formula stated in def-weil-polynomial-root. I checked that the stage polynomial is nonconstant before applying separable closedness. The displayed sum proves that a stage root maps to a root of p, using only ring-homomorphism laws. I did not cite lem-weil-polynomial-root-ring-hom: its statement is limited to integer-coefficient polynomials, which would not cover this use (C4).

Against delivery-errors B through E: there are no new statement-only nodes to disguise a proof, no clause restatement, and no uncited non-elementary input; the one substantive descent operation is the existing cited lemma. All statements cited by all four steps were opened and quotations are copied literally into citations.json. Tested a one-stage diagram, a constant diagram, characteristic p (the derivative factors are integer ring expressions, so they reduce correctly), linear polynomials, and vanishing Bezout polynomial U or V. Nonempty and directedness are used exactly by finite-data descent. No step exceeds 2000 characters, and the full assembly is under 3000 characters. No Lean file was written, and no compiler or local DAG/preflight checker was run.

## Unfinished work

None in the split. Required server dry run and delivery follow this report.
