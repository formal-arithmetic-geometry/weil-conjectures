## Worker report

Files written:
- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-algebra-normal-formal-fibres.json: item, split into five steps; statement unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-geometric-normality-finite-inseparable-test.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statements for all seven step citations.
- searches.jsonl: actual results from the required msearch command.

Attachments: none. The project search for the item's blueprint tag and for geometrically normal formal fibres found no declaration establishing the item. Existing regular-formal-fibre results do not establish the normal-fibre assertion under its weaker hypotheses. Project RingTheory also contains no declaration for the new finite-inseparable normality test.

WANTED: none. All sources used are present in literature/stacks-project/.

The original item had no proof. The full essentially-finite-type permanence theorem 0BIV is unnecessary for a module-finite algebra: the source's quasi-finite argument 0BIT is precisely its finite subcase. This keeps the existing normal-formal-fibre route; it does not assume regular formal fibres or excellence. The one new node is a theorem about arbitrary field algebras and has no completions or finite ring extensions in its statement. It cannot restate the item. Its future split should follow 037Z (3) implies (2) via making the ground-field extension separable, smooth ascent, localization, and faithfully flat normality descent, then (2) implies (1) via filtered colimits. Those are source instructions for the future worker, not an embedded proof in the new statement.

Nothing mathematical remains unfinished in the item's assembly proof. The one new theorem remains statement-only as required by a one-level split. No Lean was written or compiled, and no repository or launcher file was changed.

## Searches and blueprint provenance

Read the current latest blueprint chapter and unit sections, and lem-per-artin-gabber-affine-curve.proof.md, including Step 3. The already recorded completion subbranch is the provenance of the item; it supplies finite-normalization permanence to lem-per-nagata-normal-formal-fibres-lifting. Retained the ancestor and its full via chain; the new node adds this item to that chain. This is not a new claim that the current blueprint's Step 3 explicitly states the commutative-algebra lemma.

Before creating the new node, searched all DAG nodes by 037Z, by geometric normality, and by finite purely inseparable normality, and searched the entire imported blueprint with blueprint_refs.py search 'formal fibres', 'geometrically normal', '037Z', 'completion', and 'quasi-finite'. The first three give no blueprint match. The latter two locate the existing completion tools, which are reused. Read the statements of both 037Z nodes and of the tensor-normality nodes, not just their titles. No existing node gives the finite-inseparable test. No same_as match was found.

Ran leanfinder twice with distinct phrasings, loogle, leansearch and grep for the new node, and a separate set for the item. The complete records are retained in each node. The geometric-normality searches returned Algebra.IsGeometricallyReduced and its closure criterion, which concern reducedness rather than integrally closed prime localizations, and IsPurelyInseparable.normal, which concerns normal field extensions rather than normal rings. Read the corresponding Mathlib file descriptions and the normal-field-extension instance at FieldTheory/PurelyInseparable/Basic.lean:471. The item searches returned quasi-finiteness, formally unramified localization, and Noetherianity; only the last is one clause of the item, already carried by lem-weil-pbc-finite-algebra-noetherian. None is an attachment or a leaf for the entire item or the new test.

## Not duplicates

lem-per-geometric-normality-finite-inseparable-test vs lem-per-finite-algebra-normal-formal-fibres: the new node is 037Z's criterion for a general field algebra, with no Noetherianity or completion; the item proves permanence between rings using a completion product decomposition and a direct-factor argument.

lem-per-geometric-normality-finite-inseparable-test vs lem-weil-pbc-geometrically-normal-perfect-closure-criterion: the existing statement tests normality after one specified perfect purely inseparable overfield, not after every finite purely inseparable extension. Passing from the finite tests to the infinite perfect closure needs normality under filtered colimits, absent from its statement. The new node states the distinct equivalence (3) with (1) of 037Z, while the existing node states (4) with (1).

The tensor-normality theorem lem-weil-pbc-geometrically-normal-tensor-normal assumes geometric normality to start with; it supplies no finite-inseparable criterion. The source-overlapping completion nodes are reused rather than duplicated.

## Review by Q46

I read more-algebra.tex at labels proposition-finite-type-over-P-ring (0BIV), lemma-P-ring-goes-up-quasi-finite (0BIT), and lemma-formal-fibres-normal (0BIX). For a finite algebra the proof of 0BIT factors the completed base change and then extends the field. I also read algebra.tex at lemma-completion-finite-extension (07N9) and lemma-geometrically-normal (037Z). The item agrees with the finite specialization: it tests all contracted pairs of primes, not just maximal or generic fibres. The new statement agrees with 037Z (3) and (1), including arbitrary commutative algebras with no finite-type or Noetherian assumption.

Step 1 uses the actual statement of lem-weil-pbc-finite-algebra-noetherian: module-finiteness over a Noetherian base gives Noetherianity of S. Its hypotheses are exactly the item's. Contraction preserves inclusion. I wrote the injection of residue fraction fields explicitly; I do not assume the composite E/k is purely inseparable (it need not be). No residue-degree finiteness theorem is needed because the new criterion allows arbitrary field extensions.

Step 2 uses exactly the new test's implication (1) to (2), with A equal to k tensor_R C. For each finite purely inseparable L/k, N(R) applies at the contracted pair q contained in p. The cited tensor definition supplies its balancing relation, and the step writes the cancellation isomorphism and inverse. There is no hidden change from the base prime q to the maximal prime p. This is the substantial field-extension fact that required a new node.

Step 3 uses the full statement of lem-weil-pbc-completion-finite-extension, which explicitly gives a finite product of completed local rings as S-algebras and compatibility with the completed base. The selected prime b lies over p by construction. Grouping the other factors is elementary, including a zero complementary factor when there are no others. I did not use only the underlying ring isomorphism or appeal to an unstated compatibility from its proof.

Step 4 uses the stated universal tensor construction, and explicitly writes the maps in both directions for cancellation and product distribution. Finite products are essential here; no claim about arbitrary products is made. The S-algebra compatibility in Step 3 makes the tensor over S the desired formal fibre. The two coordinate idempotents prove the inverse and multiplication assertion directly, so this is an elementary step rather than a hidden tensor-product theorem.

Step 5 uses the actual normal-ring definition (all prime localizations are integrally closed domains) and the localization-at-prime definition. It proves factor normality by the prime r times U and writes the localization isomorphism and inverse. No false claim that all quotients of normal rings are normal is used. Isomorphic local rings have the same fraction-field integrality test. This is elementary and does not need a new factor-normality node.

For edge cases, S=0 has no primes; a one-factor completion product has B=0 and the tensor formulas still work. The new criterion allows A=0, where normality is vacuous at primes. For A=k it gives the normality of field extensions. Over characteristic-zero or perfect ground fields its finite purely inseparable tests include the identity extension; 037Z imposes no positive-characteristic restriction. Over an imperfect field k of characteristic p, the purely inseparable field algebra A=k(u) with u^p in k but u not in k is normal as a ring yet fails the test after L=A: A tensor_k A contains the nonzero nilpotent u tensor 1 minus 1 tensor u. This confirms that the new node retains the genuinely needed geometric hypothesis and cannot be replaced by normality alone.

Checked delivery-errors B through E: the new node is self-contained and statement-only, all its notions have definition citations, source tags and labels are exact, TeX uses single escapes after JSON decoding, all searches are actual logged commands, and the two same-tag pairs are distinguished above. Every step citation was opened and is backed by its verbatim statement in citations.json; no proof-only data is used. The five steps each have fewer than 2000 characters. The only off-unit non-leaf tool is the existing finite-completion theorem, declared in split_report.tool_uses because it is a generic commutative-algebra tool used exactly as in 0BIT. No maintainer-owned tool_uses field was set. The item retains its original statement and its provenance fields. No statement dispute or source error was found.
