# Q92 stage-1 report: lem-sfb-rank-two-root-coordinate-classification

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-rank-two-root-coordinate-classification.json — item, statement; split, no Mathlib match; original statement and existing source/search records retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-reflection-simple-base-orbits.json — new statement-only supporting lemma, unsplit; no exact Mathlib match. General rational simple-base existence and simple-reflection orbit exhaustion, not a classification or one of the item's four cases.
- citations.json — verbatim statement excerpts for the two proof steps citing the new node.
- report.md — this report.

## Attachments

None. Searched the actual project under lean/WeilConjectures by the item blueprint tag, rational reflection/root-base terms, rank-two root/classification terms, and the likely LinearAlgebra and GroupTheory directories. No declaration of this project states this item. Mathlib declarations are candidates, not project attachments.

## WANTED

None for this split. Read the local literature/milne-algebraic-groups_iAG2017.pdf directly using pdftotext: PDF pages 620--626 cover printed pp.608--614; PDF pages 633--634 cover printed pp.621--622. No SGA source is used. The ancestor's unrelated historical WANTED notices are retained as provenance only.

## Corrections and scope

The item was unsplit, with no proof and no repair note, and the sandbox initially contained no node or report. Its statement is correct and unchanged. The source's sentence on printed p.622 saying that the two simple-root Cartan integers are both negative omits the orthogonal case (0,0), which the immediately following A1 x A1 diagram explicitly includes. Step 3 says nonpositive, retaining this case, and proves the stronger precise alternatives. This is a correction to the source's prose in the proof, not a dispute of the item statement.

The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor prints None. Kept that value and the full inherited via chain rather than inventing an ancestor. Read the chapter record and unit record. Also read the actual current latest blueprint unit at sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof (the unit record's older sec-six-functors path is absent from latest). This is an auxiliary root-theoretic input deep below the existing alteration/moduli/representation route, and changes no unit or chapter route and no realized fields.

## Mathlib searches and candidates read

All new-node searches recorded in its JSON were run by the mandated msearch.py command with this group's assigned item and are present in this sandbox's searches.jsonl. Two semantic phrasings were read. The grep was limited to Mathlib/LinearAlgebra/RootSystem. Read Mathlib source BaseExists.lean:305--330 (Base.mk' and nonempty_base), Base.lean:639--674 (positive height descent and induction_reflect), Basic.lean:240--295 (root-pairing constructors), and Finite/G2.lean:253--315 (allRoots, coordinate identities, allCoeffs and allRoots_eq_map_allCoeffs).

RootPairing.nonempty_base is for an already bundled reduced crystallographic root pairing. The new lemma starts with the raw finite spanning root set and rational linear functionals, with no injective dual family, dual reflection stability or spanning coroots supplied. Building that paired structure and verifying its hypotheses is not a one-line specialization, so this bridge is unsplit, not marked Mathlib. It can subsequently reuse nonempty_base and the existing Mathlib-leaf lem-sfb-root-base-reflection-induction after that construction. Neither the G2 list nor ofPairingInThree classifies all four possibilities. The item retains its earlier searches and adds freshly run searches; their hits still supply only these partial candidates.

## Not duplicates

Whole-DAG searches covered root-system, root-plane, simple-root, Cartan-integer, invariant-form, C.19, C.22 and table (180) terms, together with blueprint_refs.py searches for root, rank-two, simple root, reflection, positive definite and crystallographic. No imported blueprint node states the new bridge, so same_as is empty.

lem-sfb-rational-reflection-simple-base-orbits vs lem-sfb-crystallographic-positive-base: the existing Mathlib leaf proves only independence of positive indecomposables in a perfect integer root pairing; it assumes the paired integer structure and gives neither rational-basis existence from raw data nor root-orbit exhaustion.

lem-sfb-rational-reflection-simple-base-orbits vs lem-sfb-root-base-reflection-induction: the existing Mathlib leaf is an induction rule assuming an already bundled rational root pairing AND a chosen base; it does not construct either from the new lemma's raw reflection data.

lem-sfb-rational-reflection-simple-base-orbits vs lem-sfb-root-base-rational-integral-spans: the existing statement starts with a paired root system and a given simple-root set; it establishes coroot bases and lattice equalities, not existence of a base or orbit exhaustion from unbundled data.

lem-sfb-rational-reflection-simple-base-orbits vs lem-sfb-simple-root-reflection-generation: the existing statement assumes a real positive definite root system and an already chosen simple base, and concludes generation of root reflections, not existence of a rational simple base or every root being a simple-root image.

lem-sfb-rational-reflection-simple-base-orbits vs lem-sfb-root-chamber-simple-transitivity: the existing statement assumes real orthogonal root data and identifies the set of bases with chambers and a simply transitive group action. It does not supply the unbundled rational bridge or its specified simple-reflection orbit assertion.

lem-sfb-rational-reflection-simple-base-orbits vs lem-sfb-finite-spanning-reflection-uniqueness: the existing statement supplies only uniqueness of a functional for a prescribed root and finite spanning set. It supplies no simple base or root-orbit assertion.

The new node and the item share the same Milne PDF, as do many distinct root-theoretic nodes; no Stacks tag applies here. The new node is strictly smaller in content than the classification: it works in arbitrary finite rank, says nothing about possible Cartan integer pairs and contains none of the four complete coordinate sets. It is not an elementary fact, not a clause relabelled from the item, and has no proof or sketch hidden in its statement.

## Review by Q92

I read Milne Appendix C.3, C.8--C.9, C.11--C.22 and the entire rank-two classification on printed pp.621--622 for the item and the new bridge. C.14 matches exactly the functional hypotheses. C.18 supplies the exact reducedness convention. C.21--C.22 gives the new node's base and orbit assertions; C.11 says the words may use the simple reflections. These are substantial general inputs and are left as the one statement-only node, not asserted to be elementary and not replaced by an unsupported Mathlib attachment. In its future split, reflection uniqueness, construction of the dual family and simple-base/height descent are the actual work; the statement here contains no proof sketch.

Step 1 uses no cited node: I checked the displayed involution identity from c_r(r)=2, faithfulness on a spanning set and the explicit finite sum. Positivity holds over Q using the sum-of-squares form in a rational basis, with its identity summand, so no unspecified real scalar extension or external invariant-form existence theorem is needed. Invariance follows from the permutation w -> w s_r of the finite group. Pairing the explicit reflection formula with -r gives precisely the required c_r identity.

Step 2 uses exactly lem-sfb-rational-reflection-simple-base-orbits, whose statement I reread after writing it: the same finite spanning S, all of its given linear functionals, integrality, normalization and reducedness are present. Its conclusion is exactly a rational basis of roots with same-sign integer coordinates and exhaustion by simple-reflection words. Dimension two gives exactly two basis vectors by the existing definition of dimension, so no extra existence or spanning lemma is concealed here. citations.json quotes these actual conclusions verbatim.

Step 3 uses the already constructed form, chosen basis and same-sign coordinates only. I verified the strict Gram bound by substituting t-B(s,t)s/B(s,s) into positivity; this avoids citing a Cauchy--Schwarz theorem. Integrality gives product 0,1,2,3. Zero forces both zero from the common numerator B(s,t). A positive pair has a coefficient 1 and would make t-s or s-t a root with mixed signs, contradicting the base conclusion. Swapping basis vectors puts the negative pair in the orientation (-m,-1); it does not silently choose long/short roots in an incompatible order. The orthogonal pair remains (0,0).

Step 4 gives both reflection formulas and every image in each finite table. It uses no classification lemma or uncited dihedral-group theorem. I checked each substitution and both signs, including the m=0 case separately. Stability bounds all words by a direct induction on their length. The longest step is under 1000 characters, and no step exceeds 2000 characters.

Step 5 cites the new node's orbit-exhaustion statement, which is copied verbatim into citations.json for this step. I checked all words producing additional positive vectors, and checked that the negatives also occur by starting from -s=U(s) or -t=T(t). No transitivity of all roots is assumed: there may be two distinct orbits, as in the unequal-length and decomposable cases. The two inclusions establish equality with S, not merely containment of the displayed roots, and all coordinates remain rational in a basis contained in S.

Small cases: I checked the 4-, 6-, 8- and 12-vector lists by a finite Python coordinate calculation in this sandbox workflow: both maps preserve each signed set and iterative application to the two unit vectors reaches it all. The result also checks the B2/G2 orientation. The general supporting node allows V=0 with S=D empty and vacuous orbit assertion; in rank one it gives the singleton simple base and its positive/negative orbit. The finiteness, spanning and reducedness assumptions exclude empty rank-two sets, extra multiples on a root line and infinite/noncrystallographic dihedral examples; none has been smuggled in at application. The average is taken over a finite faithful permutation group, not over an infinite generated subgroup presumed finite.

I checked delivery-errors B--E in substance: all statement notions are explicit or have the same existing definition dependencies as the item; the new statement introduces its own objects and is not an apply-the-new-classification restatement; no theorem is cited only by a tag or its proof; all non-elementary input of the item is exactly the new bridge; no existing dependent node is cited, so no cycle is introduced; the computed equality proves all four clauses without changing hypotheses. No Lean file was written and no compiler, Lake or build tool was run.

## Unfinished work

The new supporting node is deliberately unsplit for the next stage-1 worker, as the one-level splitting contract requires. Nothing in the item's proof remains implicit beyond that named general input. Server dry run and delivery results are recorded below when available.

## Dry-run repairs

The first completed dry run rejected the combined definition-reference brackets on the new statement. Replaced them with individually bracketed node ids so the checker recognizes both existing definition dependencies. No mathematical statement changed.
