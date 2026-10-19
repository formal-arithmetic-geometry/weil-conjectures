# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-localization-system-kernel-stabilization.json`: statement, split; no exact whole-item Mathlib match. Four proof steps, unchanged statement and statement dependencies, no new nodes.
- `citations.json`: one verbatim statement quote for each of the four step/node citations.
- `report.md`: this report. `searches.jsonl` is the genuine search-command log; the item's inherited searches were retained and six fresh logged searches appended.

## Attachments

None. Searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, localization/kernel stabilization wording, finitely generated kernels and colimit/kernel/injectivity combinations. No declaration states this whole directed-system assertion. The existing `powTorsion_eq_ker_localization` describes one principal-localization kernel, not eventual injectivity of these cocones. No Lean files were written or compiled.

## WANTED

None. The source passages needed are present in `literature/stacks-project/algebra.tex`.

## Findings and corrections

The node was unsplit with no proof. Its statement is correct as written: in particular it specifies additive colimits, compatible varying scalars, semilinear transitions, and actual module-localization comparison maps. No statement correction or dispute is needed. The finite kernel belongs to the fixed initial module, not to each later module. The proof must use localization directly from that initial stage to every later stage; assuming later modules are generated as modules by its image without allowing denominators would be wrong.

Read Stacks Tag 046Y, label `lemma-mod-injective-general`, the middle proof paragraph at lines 32804–32843; Tag 00D7, label `lemma-zero-directed-limit`, lines 811–822; and the fraction construction preceding Tag 07JZ, label `definition-localization-module`, lines 1138–1165. The two-stage fibre/residue-field presentation in 046Y has already been abstracted in this item's hypotheses. Once those hypotheses are supplied, the exact finite-generator and fraction argument needs neither Noetherianity nor finite generation of the full modules. The parent split supplies these hypotheses separately and invokes this item in its Step 5.

The chapter record, unit `sk-i-curve-zero`, and current main-20261015 blueprint `lem-trf-local-term-locality` were read. This remains an algebraic helper below the established 0GSG/046Y ancestry; it does not replace any unit step or alter the unit's statement. The item is not the unit's key node, so no unit file is changed.

## Not duplicates

No new nodes. DAG searches by 00D7, 046Y, localization, kernels and eventual vanishing found the already existing `lem-weil-pbc-filtered-colimit-modules-elementwise` and `def-weil-pbc-module-localization`, which are reused. Blueprint searches for `localization kernel` and `kernel finitely generated` found no whole-item duplicate; the sole localization/kernel match is `lemma-nagata-power-torsion-kernel-localization`, about one power-torsion kernel. `blueprint.same_as` is therefore empty, and the existing precise ancestry/place is retained.

## Mathlib search assessment

Ran LeanFinder with two distinct whole-item phrasings, Loogle `IsLocalizedModule, Function.Injective`, LeanSearch for finite-kernel stabilization, a whole-Mathlib kernel/colimit grep, and a narrower grep in Algebra/Module. All services returned successfully. The log records the exact queries and returned declaration lists; no unavailable search is called a negative result.

Read `IsLocalizedModule.injective_of_map_zero` and `injective_of_map_eq` in `Mathlib/Algebra/Module/LocalizedModule/Basic.lean:1201–1219`. They assume the already-established vanishing condition on the initial image and do not obtain a common later index from finite generation. `Module.DirectLimit.of.zero_exact` is only the individual-element vanishing assertion, already carried by the cited elementwise-colimit Mathlib leaf. The whole item requires these ideas to be combined and hence is not a one-line Mathlib specialization. No new Mathlib leaf is created.

## Unfinished work

None in the one-level split. Delivery validation is recorded below after it runs.

## Review by Q117

I checked the statement against 046Y's finite-kernel paragraph with all the item hypotheses in view. The source's Noetherian fibre rings are used to obtain finite generation upstream, not inside this abstract lemma. I retained the statement including its explicit absence of Noetherian/full-module-finiteness assumptions. The source route is the finite-generator/denominator argument, and every calculation using that route is written in the steps.

Step 1 reads the finite-generation definition's actual finite linear-combination clause and the elementwise-colimit lemma's actual eventual-zero clause. The latter assumes a fixed scalar ring and a module colimit, so I explicitly use the ring of integers: additive groups, additive transitions and additive cocones are exactly integer modules, linear maps and linear cocones. This makes its universal property identical to the assumed abelian-group colimit. Smallness, nonemptiness and directedness give precisely its small filtered index category. There is no appeal to a colimit in modules over a varying ring.

Step 2 again cites the finite-generation statement for the linear-combination expression. The common upper bound is constructed by finite repetition of directedness, and the semilinearity calculation displays the changed coefficient `d(b_a)` explicitly. Composition and additivity are hypotheses. This is an elementary calculation from the cited definition and Step 1, not a separate finiteness lemma. For an empty generating family the chosen bound is exactly the given initial index.

Step 3 cites the localization definition whose statement explicitly realizes every element as a class of a pair. The hypothesis's specified isomorphism then gives the displayed fraction formula using the localization from i_0 to l, with numerator in P_i0, not in an unspecified stage. Invertibility of the denominator follows from the stated ring localization. This is a direct unpacking of that definition and the item's hypothesis, with no flatness or localization-exactness theorem hidden in it.

Step 4 cites no extra node because it only substitutes Step 3's equation into the assumed cocone and linearity identities, and then uses Step 2. The displayed equation puts the numerator in the original kernel. Multiplication by an actual unit then kills the fraction, and the final subtraction argument proves injectivity of the additive map. Every scalar in the equation acts on P through its given D_l-module structure, so it does not assume a nonexistent common scalar ring for the entire diagram.

I checked delivery-errors B–E against these files: there are no new-node shape, missing-definition, duplicate, tag-only or relabelled-clause issues; all non-elementary input is the cited existing colimit lemma; citations use its statement rather than its proof. All verbatim quotes were checked against the current node statements. The three other inputs are explicit hypotheses, elementary finite-directedness/linearity calculations, or the cited fraction and finite-generation definitions. No dependency can lead back to this item: the only statement input is an existing Mathlib leaf. All four steps are shorter than 2000 characters and hide no extra comparison or standard lemma. No SGA source is used.

For edge cases I checked: singleton I (the colimit cocone is already an isomorphism); initial kernel zero (the empty family gives j=i_0); zero modules and localizations at a set containing zero (the relevant localized module is zero); and zero-divisor denominators (the proof only uses their invertibility after localization). To check that arbitrary modules really are allowed, take the constant system on an infinitely generated module with identity cocones: the initial kernel is zero and j=i_0 works. Conversely, without finite generation the example D_n=Z[1/(p_1...p_n)], P_n the localization of the direct sum over all primes p of Z/p, has zero colimit and nonzero P_n at every finite stage; its initial kernel is not finitely generated. Thus the finite-kernel hypothesis supplies exactly the common-bound argument. There was no earlier sandbox split/report to repair; I wrote out the missing proof and kept the inherited statement, metadata, and searches.

## Validation

The required `deliver.py Q117 lem-trf-localization-system-kernel-stabilization --no-push` completed successfully and wrote its durable passing-preflight receipt for commit `05dc88cc71`. It checks the sandbox overlay on the server, including `check_dag.py` and `review_split.py`. No local checker, compiler or Lake command was run. The final dry run below revalidates this report addition before the direct push.
