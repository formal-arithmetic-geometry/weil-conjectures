# Stage-1 report: lem-trf-maximum-history-intrinsic-cocycle

## Files written

- dag/nodes/sec-trace-formula/lem-trf-maximum-history-intrinsic-cocycle.json: statement unchanged; split into nine proof steps, using existing nodes. No new nodes, no Mathlib leaves.
- citations.json: fourteen verbatim citation records, one for each step/node pair.
- searches.jsonl: the actual current Mathlib searches, retained with their outcomes; inherited item search records also retained.
- write_split.py: sandbox-only JSON preparation script.

## Attachments

None. Read-only searches of lean/WeilConjectures for the exact blueprint tag, maximum histories, intrinsic comparison/cocycle, and the resolution invariant found no declaration stating the item. Existing project blowup declarations provide supporting geometry, not an attachment of this history theorem.

## Wanted sources

WANTED: Bierstone--Milman--Temkin, Q-universal desingularization, arXiv:0905.3580, Theorem 6.1 and Addendum, sections 6.1--6.3, archival copy, for the background of lem-trf-maximum-history-intrinsic-cocycle. This is already wanted in the inherited source. The present theorem assumes the entire calculus, so the proof is written explicitly by the agent from its stipulated conditions and existing blowup tools; no unprovided resolution-existence theorem is used.

## Findings and corrections

The imported item had no proof. Its statement is true under the fixed simultaneous calculus and was not changed. The calculus identifies values and maximum ideals only when an intrinsic comparison of earlier prefixes already exists. Accordingly Step 1 constructs the empty-prefix comparison, and Steps 2--5 extend only an already established comparison. This avoids circularly assuming the comparison being constructed.

No new nodes are needed: the non-elementary geometric facts are already thm-nagata-strict-transform-is-blowup, thm-nagata-blowup-principalizes-center, thm-nagata-blowup-universal-property, and the sibling lem-trf-maximum-history-smooth-deletion. The latter is a strictly different conditional assertion about smooth ambient maps; here it supplies the pulled-back histories and their deleted labels, while our Step 8 proves equality of their intrinsic comparison maps.

The current latest blueprint's lem-trf-local-term-locality and sk-i-curve-zero now use contracting correspondences. The inherited blueprint.from and source explicitly identify this item's historical alteration branch and ambient-comparison old Steps 5 and 7. I read the current latest files, retained that provenance, and did not revive or change the chapter/unit route. The assigned lemma is only a conditional finite-history construction. No use of SGA is made.

The old universal-property node has poorly imported introductory wording ('Under the data of' itself), but its statement explicitly asserts uniqueness for the chosen invertible quotient and finality. I read the current latest blueprint statement, Stacks 0806 and the project blowup lift usage. Every application in this split supplies the canonical quotient onto the extended ideal, rather than appealing to uniqueness for an unspecified quotient. This uses the node's stated assertion, not any internal construction in its proof.

## Not duplicates

No new nodes were created. Whole-DAG statement searches and blueprint_refs searches for intrinsic comparisons, maximum histories and blowups found the existing geometric nodes reused here. In particular, 080E is already thm-nagata-strict-transform-is-blowup; 0806 is already thm-nagata-blowup-universal-property. Creating new resolution-specific copies of these general tools would have been redundant.

## Review by Q60

I read the entire supplied checklist B--E, the worker brief, stage-1 contract, GOAL, the three blueprint levels in SETUP, chapter sec-trace-formula and unit sk-i-curve-zero. For the item's source I read ILO Expose VIII 2.3.1, 2.3.4--2.3.5 and 2.3.11--2.3.13, printed pp.91--94, by extracting the available PDF. These passages establish the blowup-tower, contraction, first-regular stopping and invariant-synchronization context; they do not give this particular conditional induction verbatim. Its proof_origin is therefore agent, with the induction fully written out. No new node has an unread source.

I read every cited node's statement, plus the actual local Lean definitions ResolutionInvariantCalculus and its intrinsicValues/intrinsicIdeals clauses to check the interface. The definition requires an intrinsic comparison at equal finite prefix lengths; the induction maintains exactly this. It does not assume independence for arbitrary incomparable histories. I read Stacks divisors.tex lemma-strict-transform (080E), lemma-blowing-up-gives-effective-Cartier-divisor (0804), lemma-universal-property-blowing-up (0806), and lemma-flat-base-change-blowing-up (0805), with tags checked against tags/tags.

Step 1 uses the raw-history definition to give the entire base comparison and vacuous earlier-ideal conditions. Prefixes of these maximum-extension histories are admissible by their defining closure. Step 2 uses precisely intrinsic values, regular-bottom and bijectivity of the constructed isomorphism, giving equal images and simultaneous stopping; it does not use invariance of regularity from an uncited theorem. Step 3 applies intrinsicIdeals only after that comparison exists and the maximum values agree. Both ideals are reduced maximum-stratum ideals because this is explicitly what a maximum extension means. The calculus supplies their coherence, so all finite-type center hypotheses used next hold.

Step 4 takes the full isomorphism in thm-nagata-strict-transform-is-blowup, including compatibility with projections, for each ambient closed immersion. The extended ambient ideal is the intrinsic center ideal because the given center has its specified closed immersion into the strict transform. These are scheme-theoretic constructions. Step 5 uses principalization to make the extended ideals invertible and then the universal property to construct forward and backward lifts. The quotient is the canonical map onto the same actual ideal inside the structure sheaf; the two composites induce that same quotient, which is exactly the uniqueness assertion cited. Thus the lifts really are inverse and commute with transitions.

Step 6 assembles this finite induction and uses only the calculus's strict-progress clause for distinct ordered labels; it invokes neither well-foundedness nor existence/termination of an algorithm not in the hypotheses. Step 7 compares actual morphisms, not just object isomorphism classes. The initial equality for composition is explicit, and equality at the next stage follows from uniqueness with the same canonical extended-ideal quotient. It includes identity and the three-embedding cocycle.

Step 8 cites the full smooth-deletion statement, which actually promises the cartesian strict-transform diagrams, center ideals and retained labels needed here. It does not infer these from the definition of a smooth comparison. The cartesian square gives the displayed equality of the two iterated extended ideals (checked on local generators), so the same labels are deleted on both sides. At each retained label both next maps induce exactly the same quotient; the universal property gives equality. Deleted labels are identity stages. This proves the compatibility of comparisons, including restriction, without assuming it as a separate node restating the item's conclusion. Step 9 is the explicit finite reindexing D ↦ k(D); naturality is the composite of already proved stage squares. No transfinite induction or limit existence is used.

I tested the statement on: a regular input (zero extensions); an empty input (empty invariant image, so no appeal to a greatest element); one singular blowup step; a finite disconnected input with components of different dimensions; an invertible intrinsic center whose blowup is an identity; an open restriction missing the next center or all centers; and a smooth cartesian pullback of varying relative dimensions. The proof retains the recorded ideals even for identity intrinsic blowups, and only uses smooth deletion when there is an actual specified ambient cartesian diagram. In particular it never asserts an isomorphism of the two ambient towers. At a missed center the inserted identity still has the original label convention, so cocycle and cut indexing remain consistent.

There is no new statement that merely repeats a clause of the item, no unsplit node with a hidden proof, and no novel Mathlib-leaf claim. Current Mathlib searches were run through the required msearch.py command, using two semantic phrasings, Loogle, grep and LeanSearch; I read the returned signatures. Open-cover cocycles, completion comparison maps, smooth ring maps and group-cohomology resolutions do not supply these histories. Search entries record the actual query text and actual logged results. All nine steps are shorter than 2000 characters, so no long step hides a subsidiary lemma. Every non-elementary step cites the definition condition or existing geometric theorem it needs. The three generic off-unit blowup theorems are declared in split_report.tool_uses, not in the maintainer-owned tool_uses field. citations.json quotes were tested literally against the live node statements.

## Unfinished work

None in this one-level split. The reused smooth-deletion lemma is an existing separate DAG obligation, not proved or modified by this delivery. Server validation and delivery are performed after this report is written.
