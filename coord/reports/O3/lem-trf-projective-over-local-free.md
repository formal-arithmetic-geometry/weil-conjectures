# Stage-1 report: lem-trf-projective-over-local-free

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-projective-over-local-free.json`: item, split; arbitrary-rank freeness is not a Mathlib leaf.
- `dag/nodes/sec-trace-formula/lem-trf-projective-countable-decomposition.json`: statement-only, unsplit; Stacks 058Y, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-countably-generated-freeness-criterion.json`: statement-only, unsplit; Stacks 0591, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-projective-element-free-summand.json`: statement-only, unsplit; Stacks 0592, no Mathlib match.
- `citations.json`: one verbatim statement extract for each of the five citations in the four proof steps.
- `report.md`: this report. `searches.jsonl` is the search wrapper's unchanged log. `write_split.py` is sandbox-only preparation code, not a DAG delivery file.

## Attachments

None. The project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` was searched for the exact blueprint tag, arbitrary-rank local projective freeness, countably generated projective decomposition, free direct summands, and Kaplansky. It gives no exact project declaration for this item or the new statements. The source's Kaplansky file concerns unique factorization. The upstream master is reference material, not proof evidence.

## WANTED

None: all mathematical sources used here are in `literature/stacks-project/algebra.tex`.

## What was wrong or missing

The imported item had a correct complete statement but no proof, and no `lean_audit` field. Its inherited Mathlib-search records correctly distinguish arbitrary-rank freeness from finite local freeness. I retained its statement, source, dependencies, creation metadata, blueprint ancestry and old searches, and added this item's actually logged searches. There was no previous split or report in the sandbox, so no earlier dry run to repair.

The source proof of 0593 says only that it follows from 0590, 0591, and 0592. The split now supplies the complement-projectivity check and the exact applications, instead of using the theorem as its own dependency. Tag 0590 is an immediate direct-sum consequence of 058Y, so it is not a fourth new node: the decomposition and the coordinatewise basis argument implement that reduction directly. The three new statements are genuine subsidiary results, not the item or clauses of its conclusion: decomposition uses no local hypothesis and does not conclude free; the countable criterion uses a separate summand hypothesis for arbitrary commutative rings; the element lemma produces only one free summand containing a prescribed element.

The current main-20261015 blueprint's contracting-local-term proof and `dag/units/sk-i-curve-zero.json` were read, together with the chapter. This item is an algebraic sublemma inside the inherited flattening chain below the blueprint node, not the unit's key statement, and does not change the unit or chapter. Its exact `blueprint.from.place` is retained; new nodes extend it through 0593 and have the exact ancestor and via chain. No SGA source is used.

## Not duplicates

No existing node shares source Tag 058Y, 0591, or 0592 in its mathematical statement/source, and no existing blueprint node states any of these three facts. Whole-DAG text searches included the tags, `countably generated projective`, `projective-direct-sum`, `freeness-criteria`, and `free direct summand`; `tools/blueprint_refs.py search` was run for the tags and the concepts. The broad source/statement query also found `lem-weil-pbc-free-complex-residue-degree-cancellation` (068U), which is a statement about finite-free complexes after localization, not any of the three module lemmas. Existing direct-sum-projective nodes assert projectivity of a supplied direct sum, not existence of a countably generated decomposition. Existing finite-projective local-freeness nodes have finite-generation hypotheses. None is an arbitrary-rank substitute.

- lem-trf-projective-countable-decomposition vs lem-weil-pbc-projective-direct-sum-family: the new statement constructs countably generated projective summands of a given arbitrary projective; the existing statement says a direct sum of already supplied projectives is projective.
- lem-trf-projective-element-free-summand vs lem-weil-pbc-finite-projective-prime-local-free: the new statement treats an arbitrary projective module and a chosen element over an already local ring; the existing statement localizes a finite projective module near a prime.
- lem-trf-countably-generated-freeness-criterion vs lem-weil-pbc-free-complex-residue-degree-cancellation: the criterion concerns one countably generated module with a summand condition; the existing lemma cancels one degree in a complex with finite-free terms after localization.

## Review by N3

I read algebra.tex, theorem-projective-direct-sum (058Y), lemma-projective-free (0590), lemma-freeness-criteria (0591), lemma-projective-freeness-criteria (0592), and theorem-projective-free-over-local-ring (0593), including their proofs; tags/tags confirms these labels. I also opened the full statements of both existing definition leaves used by the item: def-weil-pbc-projective-module explicitly includes the split-embedding-into-free characterization, and def-weil-pbc-free-module explicitly includes arbitrary and empty bases and finite unique expansions. I read every new statement after writing it and checked the argument against those statements rather than their proof sketches.

Step 1 takes exactly the decomposition furnished by the 058Y node: each summand is both projective and countably generated. Its commutative-ring hypothesis is available; no finite assumption is introduced. Step 2 considers an arbitrary finite-free-summand decomposition of one such summand. The projective definition supplies split maps into a free module. Composing those maps with the inclusion and projection of the complement explicitly gives a split embedding of the complement; this elementary calculation warrants projectivity without an uncited closure theorem. The cited 0592 statement then applies to this complementary projective over the same local ring and gives precisely the free summand containing each chosen element. Step 3 cites the entire 0591 criterion, whose hypotheses are exactly countable generation from step 1 and the universally quantified complement property just checked. Step 4 uses only the free-module definition: finite coordinate support plus finite basis support yields existence of each expansion, and coordinatewise uniqueness proves independence; it includes the empty index set. Each cited statement's actual words are copied into citations.json. No non-elementary fact is hidden behind a definition citation, and no step is over 2000 characters.

For the new 058Y statement I checked that direct sum is defined as finite-support families and countable generation is stated explicitly, with no countability assumption on the summand index set. For the new 0591 statement all submodules and decompositions are introduced, a finite basis is the source's finite-free hypothesis, and the free summand inside a complement may have arbitrary rank, as in the source. For 0592 the ring is local and the element belongs to the projective being used; the statement asks for a free direct summand, exactly what the source supplies, rather than the whole module being free. These are complete statements only, with empty proof/proof_deps. Their notion dependencies are the existing Mathlib definition leaves, and neither countable generation nor direct summand is left undefined.

I tested zero modules (empty decomposition/basis and zero free summand), finite modules as countably generated ones, infinite free modules over a field and over a local ring such as Z_(p), and arbitrary-size direct sums. No Nakayama step is applied to an infinitely generated module. The source's minimal-support argument for 0592 is valid when x=0 (use zero summand) and when x is nonzero: coefficient irredundancy forces off-diagonal entries into the maximal ideal and diagonal entries to be units, so the indicated finite matrix is invertible. The countable criterion uses an increasing sequence of finite-free partial summands, not an assertion that an arbitrary union of split submodules splits. The 058Y input is the substantive transfinite decomposition theorem and remains a separate unsplit node.

I read the actual Mathlib-search hits and the relevant Mathlib sources: Algebra/Module/Projective.lean (the split-free equivalence and projective direct sums), RingTheory/LocalRing/Module.lean (finite/finite-presentation hypotheses on local freeness), and LinearAlgebra/Basis/Exact.lean (a basis construction requiring an already supplied split exact sequence and basis). None is an exact match or a one-line specialization for any new lemma. Each new lemma has leanfinder, leansearch, loogle, and grep searches recorded verbatim from the wrapper log; second semantic phrasings were tried. One Loogle query contained unknown `Submodule.IsCompl`; this actual result is kept, and the corrected `Module.Free, IsCompl` search was also run and returned zero hits. The whole-Mathlib Kaplansky grep returned only unrelated UFD, dual-rank, and topology results. No unrun query or service outage is represented as absence.

I checked delivery-errors B through E: self-contained TeX statements, correct source labels, definitions present, full-blueprint and whole-DAG duplicate searches, attachment check, no leaf claimed without an exact match, no re-labelling of the conclusion, no cycle introduced by downstream dependence, and the hypotheses of every cited result explicitly accounted for. The item statement needs no correction and is not disputed. No off-unit non-leaf tool is introduced: the only existing off-unit citations are Mathlib definition leaves; all three new lemmas belong to the item's chapter and unit.

## What remains unfinished

Nothing required for this one-level stage-1 split. The three new lemmas are intentionally left unsplit for later workers. No Lean file was written and no compiler, Lake, or build command was run.
