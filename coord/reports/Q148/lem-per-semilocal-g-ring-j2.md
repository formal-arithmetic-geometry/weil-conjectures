# Stage-1 report: lem-per-semilocal-g-ring-j2

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-semilocal-g-ring-j2.json: statement; split; unchanged statement; no Mathlib match.
- citations.json: the verbatim statement of every cited node for each of the nine steps (30 entries).
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The finite product calculation and the finite-type base-change generator calculation are written in the proof rather than made into nodes.

## Attachments

None. Searched lean/WeilConjectures/ by the blueprint tag and by semilocal, semi-local, G-ring and IsJ2. Excellent.lean defines IsJ1, IsJ2 and IsExcellentRing and proves finite-type inheritance assuming J-2. Neither that declaration nor the semilocal Dedekind declarations proves this item. GRing.lean gives the exact definition used in Step 2. No upstream sorry declaration was counted as a proof.

## WANTED

WANTED: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber), Section 2, printed p.2, for lem-per-semilocal-g-ring-j2; the source URL was read with the web reader, but no local copy is present in literature/. https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf

WANTED: Matsumura, Commutative Algebra (1980), Theorem 76, for the original textbook proof cited by Kurano–Shimomoto Section 2. It is not present in literature/. The submitted proof is marked agent-written and instead gives an explicit assembly of existing Stacks-based nodes; it does not claim to reproduce the unread textbook proof.

## Problems found and changes

The imported statement is correct, including nonreduced rings, but had no proof. There was no statement dispute or statement change. I preserved all prior searches, the source, and blueprint ancestry. The proof uses a finite product of completions of maximal localizations, rather than an unspecified semilocal-completion theorem. This exhibits the faithfully flat cover and its exact regularity properties. It avoids silently assuming that regular loci descend under arbitrary faithfully flat maps: ascent needs the regular fibres, which Steps 2, 4 and 6 supply.

The current blueprint is literature/blueprint/latest/ (snapshot main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8). I read its ancestor lem-per-artin-gabber-affine-curve and the chapter/unit records. The current ancestor contains a statement rather than the historical expanded proof. This auxiliary commutative-algebra input serves the existing completion/quasi-excellence ancestry recorded in blueprint.from; it does not alter the perverse-sheaf unit route. blueprint.from.place is already specific and retained. Whole-blueprint searches for J-2, semilocal, and formal fibres found no blueprint node stating the item. Whole-DAG searches found the existing complete-local-excellence, regular-composition, local-regularity, faithful-flatness and quotient-topology inputs, all reused.

## Not duplicates

No new nodes were created. In particular, I reused lem-per-complete-local-excellence rather than creating a complete-local J-2 leaf, and reused lem-weil-pbc-flat-qc-surjective-quotient-map rather than creating a faithfully flat affine quotient-map lemma.

## Review by Q148

I read the item source Kurano–Shimomoto Section 2 on printed p.2 at its cited URL: the assertion of J-2 for semilocal G-rings and its quasi-excellence consequence agree with the item. I read the local Stacks sources more-algebra.tex at definition-G-ring (07GH), lemma-regular-local (07C0), lemma-regular-base-change (07C1), lemma-regular-composition (07QI), proposition-ubiquity-J-2 (07PJ), and proposition-ubiquity-excellent (07QW), as well as algebra.tex at lemma-flat-under-regular (00OF), lemma-flat-over-regular-with-regular-fibre (031E), lemma-hathat-finitely-generated (05GG), lemma-radical-completion (05GI), lemma-completion-Noetherian-Noetherian (0316), lemma-flat-base-change (00HI), lemma-ff (00HP), lemma-ff-rings (00HQ), and morphisms.tex at lemma-fpqc-quotient-topology (02JY). No new-node source needed checking because there are no new nodes. The item proof is an agent-written assembly, not a claim that Kurano–Shimomoto supplies these proof steps.

For Step 1 I opened the statements of lem-weil-pbc-localization-noetherian, def-weil-pbc-localization-at-prime, lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-adic-completion-mod-ideal and lem-per-complete-local-excellence. The first two give the Noetherian local source, the next three give the Noetherian local complete target and identify its maximal ideal, and the last requires exactly those hypotheses. The completion ideal is finitely generated because the localization is Noetherian. The zero ring is separated before listing maximal ideals; no local-ring theorem is applied to it.

For Step 2 I opened lem-weil-pbc-localization-regular, def-weil-pbc-g-ring, lem-weil-pbc-fibre-ring-noetherian and lem-weil-pbc-regular-composition. The G-ring statement quantifies over all prime localizations, so it applies at each maximal ideal without any localization-stability lemma. The composition theorem explicitly requires Noetherian composite fibres: the cited fibre theorem supplies exactly this since C_i is Noetherian. I checked that none of these dependencies nor complete-local-excellence reaches this item, so the assembly has no cycle.

For Step 3 I opened lem-weil-pbc-finite-product-flat-modules, lem-weil-pbc-local-completion-local-ring and lem-weil-pbc-flat-faithfully-flat-maximal-ideals. The first permits the finite family of flat A-modules. The second identifies the residue field of each completion, giving an actual nonzero quotient of B/m_i B. This is exactly the proper-extended-maximal-ideal hypothesis in the third. Merely citing the local-completion faithful-flatness theorem would not itself prove faithful flatness of A to the product; the proof supplies this missing argument.

For Step 4 I opened lem-weil-pbc-finite-type-algebra-noetherian, def-weil-pbc-finite-type-algebra, def-exc-excellent-ring and lem-weil-pbc-regular-base-change. Finite type after tensoring is proved by the displayed finite generator argument, so both Noetherianity applications have Noetherian bases. The regular base-change statement assumes a finite type base extension; here it is exactly A to D, not the generally non-finite-type A to C_i. Excellence of C_i gives the full finite-type regular-locus openness clause through the cited definition.

For Step 5 I opened def-weil-pbc-g-ring, lem-weil-pbc-flat-local-ring-maps and lem-weil-pbc-flat-under-regular. Their statements respectively give flatness, the flat local Noetherian stalk map, and descent of regular local rings. Step 4 has supplied both rings' Noetherianity, and the contracted prime is explicitly p=q cap D.

For Step 6 I opened lem-weil-pbc-regular-local-maximal, def-weil-pbc-g-ring, def-weil-pbc-localization-at-prime and lem-weil-pbc-flat-over-regular-with-regular-fibre. The first supplies regularity at every target prime (not just maximal primes), with Noetherian E_i as required. The definition of geometric regularity gives regularity by taking the identity finite purely inseparable extension. The fibre formula in the localization definition identifies the closed fibre, and the final node requires exactly the regular local source, regular closed fibre and flat local map already established. This proves the other direction of the regularity equivalence, with no smoothness or finite-presentation assumption.

Step 7 cites no node: it writes the inverse balanced-tensor map and the orthogonal-idempotent argument for a finite product. These are elementary constructions from the definitions. The product is finite because A is semilocal; I checked that neither tensoring with an infinite product nor openness after an infinite non-open cover is being used. The prime's unique surviving coordinate identifies its localization, and basic opens give the component topology. Thus the open sets used in Step 8 really are the inverse image of Reg(D).

For Step 8 I opened lem-weil-pbc-faithfully-flat-base-change, lem-weil-pbc-flat-ring-map-iff-flat-affine, lem-weil-pbc-faithfully-flat-surjective-spectrum, lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-flat-qc-surjective-quotient-map. Their statements give respectively faithful flatness of D to E, flatness of the scheme map, surjectivity on all primes, quasi-compactness of the inverse images of basic opens, and the exact openness equivalence needed. The proof writes the finite basic-open-cover argument checking quasi-compactness rather than inferring it from quasi-compactness of the whole source. I read the Mathlib quotient-map declaration at AlgebraicGeometry/Morphisms/Flat.lean:124–126 as well. I corrected the source label from the abbreviated lemma-fpqc-quotient to the actual lemma-fpqc-quotient-topology.

For Step 9 I reread def-exc-excellent-ring: the conclusion is quasi-excellence, and no universal catenarity is asserted. The Noetherian and G-ring hypotheses are retained throughout. I tested a field, a nonreduced complete local ring k[epsilon]/(epsilon^2), a finite product of such rings, D=0, D=A, and A=0. The empty regular locus in the nonreduced zero-dimensional case remains open, and no reducedness, domain, characteristic, excellence of A, or finite type of its completion was introduced.

The mathematical inputs filed outside this unit are declared as generic tool uses in split_report.tool_uses; they implement this auxiliary algebra argument and do not replace the unit's sheaf-theoretic steps. No step is longer than 2000 characters. I checked delivery-errors B–E: the item is actually proved by the argument; there are no new restatements, hidden non-elementary source assertions, new hollow definitions, unrecorded searches or unsupported tag-only steps. citations.json contains the full exact statement for every citation, and I checked each against what its step takes from it.

The new msearch queries are logged in searches.jsonl and appended to the item's preserved searches. Both semantic phrasings return Noetherianity, quasi-finiteness, smooth/unramified loci or regular sequences; those do not state openness of the absolute regular locus under the item's hypotheses. Loogle for IsJ2 and the Mathlib grep are empty. I read the smooth and unramified locus signatures at Mathlib/RingTheory/Smooth/Locus.lean:124 and Unramified/Locus.lean:141; these are different relative loci and cannot attach this theorem.

## Unfinished work

None in the requested one-level split. Existing cited nodes retain their own stage states. No Lean was written and no compiler, Lake or library build was run.
