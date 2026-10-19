## Worker report

Item: lem-trf-injective-graded-filtration-splits. Group: Q10. Date: 2026-10-17.

Files written: dag/nodes/sec-trace-formula/lem-trf-injective-graded-filtration-splits.json (statement, now split; Mathlib searches found no exact finite-filtration theorem), citations.json, and this report. searches.jsonl contains the actual search-command records; write_split.py is sandbox-only preparation code. No new nodes and no new Mathlib leaves.

Attachments: none. I searched the supplied slopmaster2 WeilConjectures source for the exact blueprint tag and for filtration/splitting/injectivity and graded/injective combinations. The bicomplex stupid-filtration splitting found there is a specific complex construction, not the general statement about finite filtrations with injective graded pieces. No declaration states every clause of this item under its hypotheses.

WANTED: none. The required Stacks TeX sources and current blueprint are present locally.

What changed: the item originally had no proof. I retained its statement, source, statement dependencies, blueprint ancestry, and all Q24 Mathlib searches. The proof now has six steps realizing the omitted induction in Tag 05TP. Its only substantive tools are the existing Mathlib leaves lem-weil-pbc-product-injectives and lem-weil-pbc-ses-injective-kernel-splits. The former guarantees that the next filtration subobject is injective, and the latter splits the corresponding quotient sequence. The proof constructs inverse maps and verifies compatibility with all filtration inclusions, rather than merely finding unrelated isomorphisms of objects.

Nothing was found wrong with the item or its source, and its statement was not corrected. A potential incorrect inference was expressly avoided: injectivity of a quotient does not generally split an extension. Descending induction proves injectivity of the kernel F^(n+1) before applying the splitting lemma. No claim of canonical or functorial choices is made. Nothing mathematical remains unfinished at this one-level split; no further node needs creating.

## Sources and route

I read literature/stacks-project/derived.tex, label lemma-filtered-injective (Tag 05TP, lines 7852 onward), including the definition immediately preceding it. It states exactly a finite split filtration by injectives and says the proof follows because injections out of injectives split, with details omitted. The item's fixed interval and the identification J_n = gr^n I are the precise version proved by the descending construction.

For the tools I read homology.tex, lemma-characterize-injectives (Tag 0136, lines 7095 onward), specifically (1) implies (3), and lemma-product-injectives (Tag 0137, lines 7119 onward). I opened both existing tool node files and the three definition node files, and read Mathlib/Algebra/Homology/ShortComplex/ShortExact.lean:205 and the structure Splitting in ShortComplex/Exact.lean:497. These give the actual retraction, section, and sum-of-projections identities used in the proof. The finite biproducts needed here exist in any abelian category; no infinite-product existence or enough-injectives assumption is added.

The chapter and unit records were read. In the current main-20261015 blueprint I read sk-i-global-additivity/_section.md and prop-trf-trace-additivity-open-closed.md and its proof, especially Step 3, which requires a common filtered origin. This item supplies the existing filtered-injective model construction along its recorded ancestry, below that step. No chapter, unit, or realization record is changed. Both theorem tools are Mathlib leaves, so their use from another unit is already allowed without a route exception.

## Searches and reuse

Whole-DAG searches covered filtration with injective graded pieces, injective short exact splittings, finite products/biproducts of injectives, and the declaration names splittingOfInjective and Injective.instBiproduct. This located the two existing theorem tools. blueprint_refs.py ancestor confirmed prop-trf-trace-additivity-open-closed. Its whole-blueprint searches for "05TP", "filtered injective", "injective graded", "injective kernel", "split short exact", and "finite filtration" supplied no blueprint node stating this item or a more general replacement. The finite-filtration induction nodes concern isomorphisms on graded pieces, not existence of a splitting. blueprint.same_as therefore remains empty.

All fresh Mathlib searches ran through msearch.py and were read. The natural-language filtration query and a second phrasing about a finite chain of subobjects found splittingOfInjective, module-filtration results, injective dimension facts, and Injective.instBiproduct. The latter only handles injectivity of an existing biproduct; it does not construct compatible splittings of a filtration. Loogle CategoryTheory.Filtration, CategoryTheory.Injective had no hits; the filtration/splitting/graded grep in CategoryTheory had no hits. LeanSearch again found the one-short-exact-sequence splitting and unrelated complex/Grothendieck-category facts. The item therefore remains a split statement, not a Mathlib leaf. Additional searches for the splitting tool confirmed the existing leaf; no duplicate was created for it. All earlier Q24 records are preserved as received, and new Q10 records describe only commands actually run.

## Not duplicates

No new nodes are proposed. lem-weil-pbc-product-injectives already supplies injectivity of the finite tails as products, including the empty tail. lem-weil-pbc-ses-injective-kernel-splits already supplies each local splitting and its three identities. The coordinate calculations and inclusion-map induction are short elementary steps of the item, not standalone auxiliary nodes.

## Review by Q10

I compared the item with Tag 05TP and checked that it requires only an abelian category and a finite decreasing filtration, not a Grothendieck category or enough injectives. Choosing J_n to be the actual quotient objects gives their injectivity and the requested graded-piece isomorphisms immediately. There are no new node statements to review.

Step 1 uses def-sp-abelian for the zero object and finite biproducts and def-sp-filtration for subobject inclusions and graded quotients. The strengthened induction invariant is an equation of inclusions, with its base at the empty tail b+1. This avoids assuming the compatibility which must be proved.

Step 2 uses the full statement of lem-weil-pbc-product-injectives: it allows any set-indexed family when the product exists, so it applies to each finite tail and to the empty family. def-sp-abelian provides finite biproducts, which are products by their universal property. The definition of injectivity in def-sp-injective-resolutions is exactly the extension property used to transfer injectivity across theta_(n+1); that transfer is written explicitly with an arbitrary monomorphism and map. No injective object is chosen using an unproved existence theorem.

Step 3 uses def-sp-filtration for the quotient J_n, and def-sp-abelian for the kernel/cokernel interpretation of the quotient sequence. I checked that the actual first object F^(n+1) is injective by Step 2. The statement of lem-weil-pbc-ses-injective-kernel-splits supplies precisely r i = 1, q s = 1, and i r + s q = 1; the proof does not take anything from that node's proof. citations.json quotes its entire statement.

Step 4 uses those same three identities and finite biproducts from def-sp-abelian. I checked all four matrix blocks, including the necessary off-diagonal identity r s = 0, proved by monicity of i. This produces the isomorphism with the correct ordering of the graded labels. This short calculation is elementary from the cited statements.

Step 5 uses filtration composition from def-sp-filtration and the finite biproduct structure from def-sp-abelian. I checked the adjacent inclusion identity theta_n i_n = j theta_(n+1), then the displayed composition for any deeper inclusion. Because theta_p is an isomorphism, the equality identifies subobjects, giving both directions of the asserted identification. No unstated comparison lemma is used.

Step 6 uses the two endpoint hypotheses and decreasingness from def-sp-filtration. At p below a the subobject is all of I; above b+1 it is zero. The boundary p=b+1 is already handled by the empty tail in the induction. All injective J_n were fixed at the start, so the same theta works simultaneously for every p.

I tested the construction with I=0, a=b, repeated equal filtration steps (zero graded pieces), negative endpoints, and a two-step filtration. The singleton case is just F^a=I with quotient by zero; in the two-step case the kernel is the final injective graded object, explaining the descending direction. Finite tails avoid any assumption about infinite coproducts. The proof creates no circular dependency. Each cited statement was opened, and citations.json has a verbatim quote for every step/use pair. Every non-elementary step is below 2000 characters; none hides a further lemma. The original empty proof was the only missing content repaired.

## Validation

Required final check: python3 /home/ubuntu/weil-launcher-nt/deliver.py Q10 lem-trf-injective-graded-filtration-splits --no-push .

The dry run runs the DAG and split checks on the Weil server. The second reader receives this sandbox only after that command prints OK. No delivery push, Lean writing, compiler, Lake, or build command is part of this work.


## Second reading by Q10

I independently read the item node, its statement dependencies, the chapter and unit records, the current `main-20261015` blueprint ancestor, and the Stacks source. The maintenance recovery does not apply because this packet is Q10 rather than Q20. Tag 05TP (`derived.tex`, `lemma-filtered-injective`) says that a filtered object with injective graded pieces is a finite direct sum of injectives with each filtration step the corresponding tail. The item fixes arbitrary bounds `a ≤ b` with `F^a I = I` and `F^(b+1) I = 0`, chooses the graded pieces themselves as `J_n`, and therefore has the same hypotheses and conclusion, including the graded-piece isomorphisms. The zero object, a singleton interval, repeated equal filtration steps, negative bounds, and a two-step filtration all satisfy the statement.

- Step 1: PASS. I checked the zero object, finite biproducts, the empty tail, and decreasing-filtration inclusions against `def-sp-abelian` and `def-sp-filtration`; the descending induction invariant is explicitly stated and its base at `b+1` is valid.
- Step 2: PASS. I checked Tag 0137 and the full statement of `lem-weil-pbc-product-injectives`. A finite biproduct is a finite product in an abelian category, and the empty product is the zero object. The displayed extension-property transfer through `theta_(n+1)` proves injectivity of `F^(n+1) I` without assuming enough injectives.
- Step 3: PASS. I checked the quotient sequence against `def-sp-filtration` and the abelian-category kernel/cokernel clauses, and checked Tag 0136 (implication (1) to (3)) through the complete statement of `lem-weil-pbc-ses-injective-kernel-splits`. The kernel is already injective by the descending induction, so the split lemma applies with exactly the required hypotheses.
- Step 4: PASS. I recomputed all four biproduct blocks from the three splitting identities. The extra identity `r_n s_n = 0` follows by composing with `s_n` and using monicity of `i_n`; the two displayed maps are therefore inverse and define the next `theta_n`.
- Step 5: PASS. I checked the adjacent inclusion equation and its iteration for every deeper filtration index. The composition order of `u_(p,n)`, `i_n`, and `u_(p,n+1)` is correct, and the corresponding tail inclusions compose identically. Since each `theta_p` is an isomorphism, the equation identifies the actual subobject with the stated tail biproduct.
- Step 6: PASS. I checked the endpoint cases `p < a` and `p > b+1` using decreasingness and the two endpoint hypotheses; the empty tail at `b+1` is already covered by Step 2. The same `theta_a` works for all integer `p`.

There are no new nodes in this split. The cited product and short-exact splitting nodes are existing Mathlib leaves; their declarations and source lines were reread (`Injective.instPiObj`, `ShortExact.splittingOfInjective`, and `Splitting`), and the recorded searches include LeanSearch, Loogle/LeanFinder, and Mathlib grep. Whole-DAG and whole-blueprint searches found no duplicate finite-filtration splitting theorem. Every `citations.json` quote was checked verbatim against the cited node statement. No statement, proof step, dependency, citation, or source correction required repair. The only handoff change is this independent review record and the second-reader marker; the original worker report and `## Review by Q10` section remain intact.

Small-case checks: `I = 0`; `a = b`; a two-step filtration; equal adjacent filtration steps (zero graded piece); negative endpoints; and the empty tail at `b+1`. No infinite product, coproduct, Grothendieck, enough-injectives, functoriality, or canonical splitting assumption is used.
