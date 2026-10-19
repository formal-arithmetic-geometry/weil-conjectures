# Worker report: lem-pur-frobenius-roots-of-unity-power

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-frobenius-roots-of-unity-power.json`: existing item split into four proof steps; statement and statement dependencies retained, blueprint ancestry completed, and the prior Mathlib search records replaced by the actual 2026-10-16 msearch results.
- `citations.json`: seven verbatim statement quotations for the cited nodes in the four steps.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the item id, Frobenius/root-of-unity terms, and the candidate cyclotomic declarations. `cyclotomicCharacter_frobeniusEquiv_pow` and `cyclotomicCharacter_frobeniusEquiv_pow_inv_mul` are sorry-free, but they state only the cyclotomic-character scalar and its inverse relation, not all three clauses of this item, so they are not whole-item attachments. The reusable closed declaration `AddCommGroup.tateModule.nonempty_linearEquiv_of_natCard_eq` is already represented by `lem-av-tate-module-group-rank`, and the primitive-root result is already represented by `lem-sc-primitive-root`; I cite those nodes rather than recreating them. The upstream master checkout was read only as reference and was not treated as evidence of a finished proof.

## WANTED:

None. The proof follows the archived cyclotomic blueprint and uses existing DAG statements for the primitive-root and Tate-module rank inputs.

## What was wrong or corrected

The imported item had an unspecified blueprint location and `same_as: null`; I set the location to the Frobenius-on-coefficient-twists sentence of its ancestor and set `same_as` to the empty list after searching the whole indexed blueprint. Its proof was empty even though the item has three substantive clauses. I added the four steps, including the finite-field specialization needed to apply the existing generic Tate-module rank theorem. I did not create a node for the rank-one conclusion because that would restate clause 3 (D1/D2), and I did not create a node for divisibility or the $ell$-torsion count because each follows directly from the algebraic-closure definition and the existing primitive-root statement in a short specialization. The two off-unit lemmas are declared as generic tool uses in `split_report`.

## Review by Q49

I read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-def-purity-conv.json`, the imported item, and the current `def-weil-frobenius-coefficient-twists` ancestor. I also read Deligne Weil I (2.2), Weil II (1.1.7), the current `sk-p-cyclotomic` blueprint and its proof, and the source modules `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`, `WeilConjectures/NumberTheory/TateModule.lean`, and `WeilConjectures/GroupTheory/TateModule.lean`. The source declarations confirm that the arithmetic Frobenius theorem gives only the cyclotomic-character scalar, so the whole item cannot attach to one declaration.

Step 1 uses `lem-sc-primitive-root`, whose statement gives exactly the distinct-root count, primitive root, and cyclic identification for an algebraically closed field with N prime to the characteristic. The preservation by an arbitrary field automorphism is checked explicitly by applying the automorphism to the equation ζ^N=1. Step 2 uses `def-weil-frobenius-substitution`, whose statement defines φ_q as z ↦ z^q and γ as its inverse. I checked that gcd(q,N)=1 follows from q=p^a and N prime to p, and that changing q′ by a multiple of N leaves ζ^{q′} unchanged. Step 3 reads `def-weil-algebraic-closure` for the root of X^ell−x, checks that this root is nonzero, identifies the additive-group ell-torsion with μ_ell(k), and applies the exact hypotheses of `lem-av-tate-module-group-rank` with r=1. The `def-tate-module-abelian-group` statement supplies the inverse-limit and ℤ_ell-action identification. Step 4 uses the same definition for componentwise action; raising a root to q is q-fold addition in the additive unit group, and the compatible inverse residues give q^{-1}. Every citation in `citations.json` is copied verbatim from the cited node statement and corresponds to the fact taken in its step.

I checked small cases N=1 (the trivial cyclic group and q′ arbitrary), N=2 with odd p, and ell=2 with p odd. For the Tate module, the divisibility argument works for x=1 and for every nonzero x, and the torsion count is exactly ell, including ell=2. The inverse residues are compatible under reduction, so the geometric action is well-defined. No hypothesis on N beyond N≥1 and p∤N was added, and the separate prime ell in clause 3 remains constrained by ell≠p.

Against delivery-errors B–E, the item statement remains self-contained and TeX is escaped once; no new node has a hidden proof or duplicate clause. Every non-elementary fact in the steps is an existing node citation, while the short automorphism, exponent-congruence, and coordinate-scalar calculations are marked elementary or written explicitly. The proof dependency union equals the uses union. The only cross-unit citations are the two generic tools named in `split_report.tool_uses`; neither is used to replace the cyclotomic route. No SGA source, Lean edit, compiler, Lake, or live-project write was performed.

## Not duplicates

- `lem-sc-primitive-root` vs `lem-pur-frobenius-roots-of-unity-power`: the existing node proves primitive roots and cyclicity for an arbitrary algebraically closed field and n prime to the characteristic; this item additionally identifies arithmetic/geometric Frobenius and the inverse-limit Tate-module action.
- `lem-av-tate-module-group-rank` vs `lem-pur-frobenius-roots-of-unity-power`: the existing node is the generic divisible-group rank theorem with hypotheses on an arbitrary abelian group; this item specializes it to Additive(k^×) and adds Frobenius formulas.
- `def-tate-module-abelian-group` vs `lem-pur-frobenius-roots-of-unity-power`: the existing node only defines the inverse limit, compatible ℤ_ell action, and coordinatewise automorphism action; this item proves cyclic roots, rank one, and the q and q^{-1} scalars.

## Second reading by Q49

- Item statement: checked the three clauses against Deligne Weil I (2.2, p. 281), Weil II (1.1.7, pp. 150–151), the current cyclotomic blueprint and the cited finite-field conventions. All hypotheses agree: N is positive and prime to p, and ell is prime and different from p. The N=1 trivial group, N=2 for odd p, and ell=2 for odd p cases pass.
- Step 1: checked against the full statement of `lem-sc-primitive-root`; its algebraically closed and prime-to-characteristic hypotheses hold. Its cyclic identification supplies clause 1. Applying sigma and then its inverse to the root equation proves preservation onto the subgroup. Verdict: pass.
- Step 2: checked against `def-weil-frobenius-substitution`; q-power arithmetic Frobenius and its inverse give the formulas. Bezout applies since q=p^a and p does not divide N, and changing the inverse exponent by a multiple of N changes no root. Verdict: pass.
- Step 3: checked against `def-weil-algebraic-closure`, `lem-sc-primitive-root`, `lem-av-tate-module-group-rank`, and `def-tate-module-abelian-group`. The nonconstant polynomial X^ell-x gives an ell-th root, nonzero since x is nonzero; the ell-torsion has cardinality ell; the rank theorem applies with r=1 and the transition map is precisely ell-th powering. Verdict: pass.
- Step 4: checked against `def-tate-module-abelian-group`; q-th powering is q-fold addition in the additive version of the unit group. Reduction of an inverse modulo ell^(r+1) is the unique inverse modulo ell^r, so the inverse residues form q^{-1}. Both field automorphisms commute with ell-th powering. Verdict: pass; this is a coordinate calculation from the definition.
- New nodes: none. No B1–B7 fault, duplicate node, or disguised restatement was introduced. The two existing general lemmas are already Lean-closed tools; their full statements were opened and checked rather than relying on their proofs.
- Changes: expanded the citation quotations to cover cyclicity, both Frobenius definitions, the full inverse-limit definition, and the scalar rule; made inverse-residue compatibility and transition compatibility explicit in Step 4; retained `split_report.tool_uses` as a request for maintainer review under the later SETUP decision (not an approval in maintainer-owned `tool_uses`). The original `created.item` records its actual origin in the ancestor split and is a maintainer field, so it remains unchanged.
- Source attribution: corrected Step 3, which had attributed a rank-one argument absent from the cyclotomic proof to that proof. It now names the general group-theoretic theorem actually used, with the finite-field specialization written in the step. Step 2 is marked elementary because it is the direct inverse-map and exponent-congruence calculation from the cited definition.
- No statement correction was necessary. The finite-field datum excludes a=0; r=0 coordinates, if included in the limit indexing, are the trivial mu_1 factor and make no difference. Zero fields and empty schemes are outside the statement. No Lean or build tools were used.

- Independent Mathlib audit: ran LeanFinder on the inverse-limit rank-one statement, Loogle on `"rootsOfUnity", "card"`, and greps in `NumberTheory` and `GroupTheory`; actual outputs remain in `searches.jsonl`. The finite-root cardinality lemmas and character residue lemmas are relevant building blocks, not the full item. Corrected two earlier grep verdicts whose subdirectory was erroneously `Mathlib/` (targeting nonexistent `Mathlib/Mathlib/`), and removed an unlogged error assertion from the second Loogle record.
- Process check: `split_report.tool_uses` is the permitted request for review under SETUP, “Claims and tool uses, fourth decision”; no maintainer-owned `tool_uses` approval is written. The existing `created.item` correctly records the ancestor split that created this item.
