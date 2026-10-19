# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-excellent-base-marked-semistable-curve.json`: repaired statement node and proof; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-excellent-base-generic-curve-preparation.json`: repaired statement-only child; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-dejong-arbitrary-base-marked-semistable.json`: new statement-only arbitrary-base marked semistable theorem; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-etale-marking-sections.json`: new statement-only finite-etale splitting lemma; no Mathlib match.
- `citations.json`: verbatim statement quotes for every item proof-step citation.

## Attachments

No Lean declaration in `WeilConjectures/` states this item exactly or carries its blueprint tag.

## WANTED

- WANTED: local archival copy of `literature/de-jong-families-curves-alterations-1997.pdf`, Theorem 2.4, Lemma 2.8, and §§2.7–2.10, for the item and `lem-trf-excellent-base-generic-curve-preparation`.
- WANTED: local de Jong 1997 source for the finite-etale divisor-to-sections base-change argument recorded by `lem-trf-finite-etale-marking-sections`.

## Not duplicates

- `lem-trf-excellent-base-generic-curve-preparation` vs `lem-weil-pbc-field-curve-completion-insep`: the new statement starts with a proper family over an excellent scheme and alters total space and base, while the existing node is only a field-level completion/normalization statement.
- `lem-trf-excellent-base-generic-curve-preparation` vs `lem-trf-generic-smooth-boundary-preparation`: the existing node is restricted to a field or excellent trait and assumes a relative-curve factorization; this child handles an arbitrary excellent Noetherian base.
- `lem-trf-dejong-arbitrary-base-marked-semistable` vs `lem-trf-dejong-relative-marked-semistable`: the existing node requires a projective-over-affine base; the new theorem has arbitrary excellent integral Noetherian base and no separatedness or projectivity hypothesis.
- `lem-trf-dejong-arbitrary-base-marked-semistable` vs `lem-trf-relative-marked-nodal-reduction`: the existing node also requires a projective base and states a finite-etale divisor; the new node is the arbitrary-base alteration theorem used to repair this item.
- `lem-trf-finite-etale-marking-sections` vs `lem-trf-dejong-relative-marked-semistable`: the existing node produces an etale Cartier divisor, whereas the new node is the separate base-change/splitting assertion that turns horizontal finite-etale components into disjoint sections and reselects an integral dominating component.

## Source and statement checks

The returned version incorrectly required the generic-preparation child to produce a base projective over an affine scheme. I checked the counterexample in the return (the affine line with doubled origin and its projective-line family): a separated projective-over-affine alteration cannot serve as the asserted preparation over that non-separated base. I therefore marked the old route `STATEMENT-DISPUTED` and removed that false conclusion from the child. I read ILO arXiv 1207.3648, Exposé IX Theorem 1.2, pp. 131–132: its weak de Jong 2.4 form has no separatedness or projectivity hypothesis on the base, and it explicitly says the output is separated only when the input is separated. The new arbitrary-base marked node records exactly the trivial-group clauses (i), (iii)–(vi), including the divisor and exceptional closed subset.

Step 1 uses only the repaired generic-preparation child, whose statement supplies the two alterations, commutative square, smooth geometrically integral generic fibre, and finite-etale reduced generic boundary. Step 2 uses the new arbitrary-base marked theorem; I checked each of its hypotheses against Step 1 and each output clause against ILO IX 1.2. Step 3 uses the new finite-etale splitting statement. It explicitly passes to dominating open-and-closed components, normalizes the finite compositum of their function fields, chooses an integral dominating component after base change, and invokes the open-and-closed diagonal to prove that the resulting sections are disjoint and remain in the smooth locus. This repairs the returned C3/C4 issue about treating a proper etale divisor as sections without a base-change argument. Step 3 also cites the proper-composition permanence statement for the vertical-boundary image. Step 4 checks composition of alterations, properness, surjectivity, dense-open finiteness, and all remaining nodal, flat, finite-presentation, generic-fibre and ordinary-double-point clauses.

I checked the empty-boundary case (the finite-etale splitting node yields zero sections), the case of a non-separated original base, and the case where the marked divisor has several horizontal components. The child and both new theorem statements are intentionally statement-only for later stages; they do not hide an unsupported proof in this stage. No Lean was written or compiled.

## What was wrong or incomplete

STATEMENT-DISPUTED: the former generic-preparation statement was false because its projective-over-affine base conclusion fails for non-separated bases; adding separatedness would weaken the imported item and break `lem-trf-de-jong-geometrically-irreducible-tower`. The route is repaired using the arbitrary-base ILO/de Jong theorem, followed by finite-etale splitting into sections.

The returned proof also treated the divisor supplied by the marked semistable theorem as sections without a base-change argument. The separate splitting node and revised Step 3 provide the missing component, diagonal, and integrality checks. The local de Jong PDF remains WANTED.

## Could not finish

The two new theorem nodes remain statement-only, as required for a stage-1 split. Their source proofs are the ILO/de Jong alteration and finite-etale normalization constructions recorded in their source fields.

## Review by Q57

I reread the repaired item, the generic-preparation child, both new nodes, ILO IX Theorem 1.2 pp. 131–132, the existing projective-base marked node, and the statements of every node cited by the four item steps. I verified that no step relies on the false projective-over-affine clause. The item’s hypotheses still allow arbitrary integral excellent Noetherian bases, including non-separated ones. Step 1 takes exactly the repaired child’s output. Step 2 takes exactly the arbitrary-base theorem’s smooth generic fibre and finite-etale boundary hypotheses and receives the proper flat finitely presented nodal family, divisor, and exceptional set. Step 3 checks the finite-etale component splitting and open-and-closed diagonal argument before asserting sections, and separately verifies the vertical boundary image. Step 4 checks alteration composition and every remaining conclusion. I checked every citation quote against the current node statement and regenerated `citations.json`; all recorded Mathlib searches were rerun with `msearch.py` for the item and both new nodes. The projective-base counterexample and the missing divisor-to-sections inference identified by the maintainer are corrected in the sandbox.
