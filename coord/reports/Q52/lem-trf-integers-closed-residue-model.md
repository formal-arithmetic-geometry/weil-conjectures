# Stage-1 delivery: lem-trf-integers-closed-residue-model

## Files written

- dag/nodes/sec-trace-formula/lem-trf-integers-closed-residue-model.json: split the unchanged statement into five complete proof steps; no new nodes and no new Mathlib leaves.
- citations.json: ten exact step/node quotations from the current shared DAG statements.
- searches.jsonl: the unmodified log produced by msearch.py; the item retains its inherited searches and records the fresh actual queries.
- report.md: this report. Sandbox helper scripts only assemble JSON; no Lean was written or compiled.

## Attachments

None. I searched the live lean/WeilConjectures tree for the blueprint tag and the integer residue, purely-inseparable and regular-model concepts. SpecialValues.lean:86 has a private cardinality result for the integer residue field, not the complete image-model assertion; the purely-inseparable project declarations concern different field-extension statements. Nothing found states every clause of this item with a finished proof.

## Wanted literature

None. All sources used are available locally.

## Statement and route audit

The statement is true as written and remains unchanged. In particular, B=L means equality of the image subring with the full subring of L, not equality of field types. The structure map is the specified composite through the actual localization residue field. The generator 1 asserts finiteness as a Z-module, not that L is finite over Z with an unspecified algebra structure. No hypothesis was added and no conclusion was dropped.

I read the trace-formula chapter, sk-i-curve-zero unit, the latest blueprint ancestor lem-trf-local-term-locality and its proof, and the parent arithmetic-excellence node and retained argument handoff. The ancestry places this arithmetic model below the same normal-cone/spreading-out excellence input. This split does not change a chapter or unit route. The one off-unit non-leaf citation, lem-weil-pbc-z-localizations-dvr, is declared in split_report.tool_uses as generic arithmetic.

I read Stacks more-algebra.tex, Tag 07PJ (proposition-ubiquity-J-2), especially the proof's maximal-prime finite field model and its reference to condition (4) of Tag 07PC (lemma-J-2). That condition requires a finite algebra domain whose fraction field is the extension and which has a nonempty regular open. The proof here gives exactly the prescribed image ring and the whole spectrum. Stacks does not spell out the stronger integer-residue/Frobenius calculation in the item: I wrote it explicitly and set proof_origin.by to agent, retaining the genuine source and place rather than claiming it is a verbatim Stacks proof. I also read fields.tex, Tag 09HE (definition-purely-inseparable) and its following p-power calculation, and the existing Frobenius and field-regularity nodes with their source descriptions.

## Searches and duplicates

There were only dispatcher brief markers in this sandbox initially; no previous item split, report or citations existed. I copied the live item before editing. I retained its inherited searches, and read the previous Q89 handoff's logged results instead of replacing or fabricating them. The fresh msearch.py queries and returned results are in searches.jsonl and exactly represented in the item's mathlib_searches. Two natural-language phrasings, two Loogle patterns, two greps and LeanSearch were actually run. The first Loogle pattern reported unknown identifier Ideal.Quotient and is recorded with that actual result; the later pattern was valid and returned no results.

The hits concern finite residue-field extensions, formally unramified residue maps, perfect closures, integer ideal quotients and purely-inseparable separability. I inspected Mathlib/FieldTheory/PurelyInseparable/Basic.lean:158-166 and RingTheory/Ideal/Int.lean:36-46. The former's surjectivity theorem additionally assumes separability and proves only the extension component; the latter's maximal integer ideal and cardinality facts prove only quotient components. Neither gives the specified finite image model and all its clauses in a one-line specialization. The item therefore remains a split, not a Mathlib leaf.

Whole-DAG searches included 07PJ, integer residue, field regularity, Frobenius, purely-inseparable extensions, and Bezout. Whole-blueprint searches included purely inseparable, residue field, Bezout, Frobenius, prime field, integer residue and 07PJ. Existing localization, Frobenius and field-regularity statements are reused. There are no newly created facts to compare for duplicate-node pairs: the least-positive-linear-combination calculation, quotient inverse, and image generator/fraction witnesses are written as proof steps.

## Not duplicates

No new nodes. The item itself does more than lem-weil-pbc-field-regular-ring (which assumes a field and gives regularity), lem-weil-pbc-z-localizations-dvr (integer prime/localization structure), or the J-2 criterion (which assumes the regular models rather than constructing this one).

## Review by Q52

I checked delivery-errors B through E against the actual node and sources, and reopened all nine distinct proof-cited statements. No statement-only auxiliary task is needed: all new arithmetic is explicitly calculated in steps, and existing DAG nodes state the non-elementary tools. TeX is singly escaped in decoded strings, proof_deps is exactly the union of uses, and citations.json has one verbatim quotation for each of the ten step/node uses. The statement's definition dependencies and the item's blueprint provenance are preserved; same_as is empty after the whole-blueprint searches.

Step 1 uses the exact integer prime and maximal-localization-ideal clauses of lem-weil-pbc-z-localizations-dvr and the actual fraction/residue description in def-weil-pbc-localization-at-prime. I checked that its denominator is an integer not divisible by p. Instead of leaving Bezout as an uncited theorem, I proved it by the least positive integer linear combination and division with remainder; primality makes its positive common divisor 1. The sign is correct: a/s-au=avp/s when us+vp=1. Thus the step proves surjectivity for the actual residue quotient, not only Z/pZ in isolation.

Step 2 cites precisely the equality relation on localization fractions. For t/1=pa/s, w(st-pa)=0 has w nonzero; the domain Z permits cancellation. Multiplying us+vp=1 by t proves the kernel inclusion by the explicit formula t=p(ua+vt). The induced quotient map is explicitly well defined, bijective and a ring homomorphism; its inverse preserves operations by injectivity. The characteristic-p assertion uses p prime, p=0 and the nontrivial field hypothesis, not a tacit perfectness assumption. This is a calculation from Step 1 and the localization definition, so it is marked elementary.

Step 3 uses both clauses of the Mathlib Frobenius node: p-power and every iterated p-power are unital ring endomorphisms. Its hypotheses hold because p is prime and p times 1 is zero in L. The purely-inseparable definition really states that every x has a p-power in the image of k. Every element of k is an integer multiple of 1 by Step 1, so the endomorphism fixes its image. The displayed (x-j(a))^(p^n)=0 then forces x=j(a) in a field. I corrected the first draft to cite the ring-Frobenius node explicitly, rather than using only the purely-inseparable definition for this theorem. The proof works even for infinite purely-inseparable extensions, but the statement retains the finite-extension hypothesis requested by the source.

Step 4 proves equality of the actual image subring with the whole field from the two surjections. It cites the exact finite-module definition, and the equality b=m times 1 verifies the required Z-action and single generator. The fractions are explicitly x/1, with 1 nonzero. It introduces no hidden integral-closure or field-of-fractions theorem and is elementary.

Step 5 applies the exact existing field-regularity statement to B, which Step 4 makes a field: that statement explicitly gives Noetherianity, the only prime (0), and its regular-local localization. The Noetherian/regular definitions are cited only for their meanings, not as substitutes for that theorem. The affine-spectrum node explicitly states that a field spectrum has one point, giving nonemptiness; the full space is open by the topology axioms. Thus every required regular-local clause and the nonempty regular open are accounted for.

For edge cases I checked p=2, arbitrary larger prime p, n=0, and the identity extension L=k. The linear-combination set is nonempty since p>0, denominators are nonzero since p does not divide them, and w is nonzero for the same reason. When n=0 the power exponent is 1. A field has no nonzero nilpotents; that is what closes the Frobenius calculation. The zero ring, composite p and p=0 are excluded by the hypotheses, and no assertion about those cases is smuggled in. I found no statement dispute. The longest proof step is 941 characters; none exceeds the long-step review threshold. No new node renames an item clause, and no cited node depends on the item, so there is no circular proof.

## Unfinished work

None for this stage-1 split. It contains no new unsplit nodes. Delivery still receives the maintainer's independent review. Server dry-run and delivery results follow below when complete.
