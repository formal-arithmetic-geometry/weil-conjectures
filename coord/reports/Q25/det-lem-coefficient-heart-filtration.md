# Worker report: det-lem-coefficient-heart-filtration

## Files written

- dag/nodes/sec-six-functors-basics/det-lem-coefficient-heart-filtration.json: statement, split into four proof steps; no Mathlib match.
- citations.json: one verbatim statement quotation for each of the nine step/node citations; local verification input.
- report.md: this report. The sandbox preparation script and search log are local working material.

No new nodes and no new Mathlib leaves. The statement, its statement dependencies, imported flags, blueprint metadata, chapter and unit are preserved. No Lean file, live project file, launcher file or unit record was written; no compiler or Lake command was run.

## Attachments

None. Searches under /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the precise blueprint tag, coefficient-heart terminology, constructible/sheaf filtrations, and extensionByZero did not locate a project declaration with all the clauses of this statement. Existing WeilSheaf extension-by-zero results have a different category and prove no finite filtration. Upstream master sorry declarations are not finished attachments.

## WANTED

None. The current blueprint and the Stacks source passages needed for this split are present.

## What was wrong and what changed

The repository contains a previous reviewed proof with status unsplit. Its third step exceeds 2000 characters and proves an independent mixed-factorization comparison inline. Under the current long-step rule I searched the whole DAG and the blueprint before introducing any lemma. The existing lem-sfb-locally-closed-extension-coherence states exactly the more general factorization-independence theorem on module sheaves over any commutative ring sheaf on a Noetherian scheme. I cite that existing statement for v_k! c_* = i_* u_!, and its normalized pure-open composition in step 1. Thus no duplicate helper was created. All four proof steps are below 2000 characters. The localization argument that actually proves the filtration remains in the item.

The original blueprint says that two extensions coincide because their restrictions are isomorphic. That alone does not specify a comparison map. The existing coherence theorem provides the canonical comparison, normalized on the stratum. For counit compatibility of nested open extensions I spell out that both maps are adjunct to the identity. These are repairs to the proof justification, not a change of route or statement.

The imported statement already correctly uses non-strict inclusions. I retained that correction: F=0 would contradict a requirement of strict inclusions for nonempty strata. There is no new statement dispute or weakening in this delivery. The unit's final filtration step is realized by exactly the localization argument in the current source.

## Mathlib and duplicate searches

Retained all inherited Mathlib searches, including the malformed historical Loogle query with its explicitly invalid verdict. Fresh msearch.py calls ran Loogle ("Sheaf", "filtration"), a full-source regular expression for constructible filtrations and extensionByZero/filtration, LeanSearch, and two LeanFinder phrasings. Loogle and grep returned zero hits. The semantic results concern finite local generators, free and quasicoherent module sheaves, constructible subsets of spectra, and algebraic module/ideal filtrations; they do not state the filtration theorem. The second LeanFinder completed during the interruption; I read its recorded result list before appending its actual query and verdict. Every newly appended query is in searches.jsonl, and no unavailable service was called a negative result.

Whole-blueprint searches for extension by zero, locally closed, interchange and locally-closed-extension, plus whole-DAG statement searches for mixed open/closed extensions and factorization, located the existing coherence theorem. The closest other candidates are det-nagata-density-normalization-sheaves (dense-open closure setting), lemma-weil-pbc-finite-pushforward-extension-zero (etale abelian sheaves), and proper/open support comparisons (finite etale coefficients or derived hypotheses). They are not replacements for this constructible pro-etale coefficient-heart filtration. No new node means no same-tag duplicate pairs require a Not duplicates entry.

## Review by Q25

I read coord/brief-stage1.md, stages/1-dag.md, SETUP.md's three levels, GOAL.md, coord/dag-sync.md and delivery-errors B through E. I read the chapter sec-six-functors-basics and unit sk-lem-coefficient-heart records before reviewing the item, and read both main-20261015 filtration files (statement and separate proof), together with the scalar-six-pullback proof (2) behind the existing coherence theorem. The relevant source is the current main snapshot, not the obsolete master snapshot. The item is a detail node rather than the unit's key node, so no realization record is changed.

Step 1 uses the final exact-pullback assertion and clause (1) of sk-prop-sfb-cartesian-coefficients, not its twist assertions: no invertibility of ell is needed. I checked that E and Qlb are among the admissible pulled-back condensed rings. The Noetherian-open node explicitly supplies local Noetherianity and quasi-compactness; the locally-Noetherian quasi-separatedness node explicitly supplies quasi-separatedness. Applying the first result inside an affine open also checks quasi-compactness of every open immersion used. The localization node's statement explicitly gives the monic counit via its short exact sequence and the exact open adjunction with invertible unit. The coherence node explicitly gives composition, normalized to the identity on the source, on module sheaves as well as derived categories; the proof uses the module-sheaf part only. That normalization and the open adjunction identify the composite inclusion with the original counit. Empty and identity opens yield the claimed endpoints without assuming a nonzero sheaf.

Step 2 cites the localization theorem's clause (3), whose displayed sequence has the exact maps needed, and clause (1), which says v_k! is exact. The complement S_k is closed in V_k by the ordered stratification in the statement, and V_{k-1} is a quasi-compact open by step 1. Restriction gives c^*v_k^*F=F|_{S_k}, and the kernel inclusion agrees with the inclusion over F already established. Hence the quotient is the actual subsheaf quotient, not an unspecified isomorphic subobject.

Step 3 uses the coherence theorem's statement that the closed-then-open functor v_!c_* agrees canonically with i_*u_! for an open-then-closed factorization. I verified both factorizations, the coefficient ring R=Lambda_X, its commutativity, and the Noetherian hypothesis on X. Inverse-image rings agree with the specified coefficients by step 1. This is a general-purpose black box, declared in split_report.tool_uses; it does not replace any route of the coefficient-heart unit. I also traversed its full statement/proof dependencies and found no return path to the item.

Step 4 cites the closure node's actual constructible/lisse characterization, not a definition of lisse alone. The localization statement supplies the invertible open unit, triangle-identity counit calculation, closed counit and exact sequence that force zero restriction to the closed complement. Each later stratum factors through that closed complement as the corresponding induced locally closed subscheme. Earlier restrictions equal those of F, and later ones are zero, which is free of rank zero. The same finite adapted stratification therefore proves that all filtration terms remain constructible. This argument does not assume that isomorphic restrictions alone determine an unspecified morphism.

For the source checks I read Stacks proetale.tex labels lemma-closed-immersion (09AA), lemma-closed-immersion-complement-retrocompact-exact (09BM), lemma-open-immersion (09BN), lemma-ses-associated-to-open (09AH), and sites-modules.tex lemma-extension-by-zero (03DI) and lemma-extension-by-zero-exact (03DJ). In particular 09AH needs a quasi-compact open immersion and 09BM needs retrocompact complement; the Noetherian hypotheses above supply these conditions. I use the existing arbitrary-ring module theorem for the linearized statements, rather than treating a finite constant-coefficient theorem as arbitrary coefficients. No SGA source is used.

I checked every cited node's statement and copied it verbatim into citations.json. These cover all non-elementary inputs; the remaining arguments are explicit adjunction identities, cokernel identifications, and rank-zero cases. I checked the small cases X empty (m=0), F=0, k=1 and k=m, a single stratum, empty strata if permitted, and closed strata with nonreduced ambient schemes. In particular the exact sequences still have the right endpoints and no strict inclusions or stalk-detection shortcut is required. No new statements were introduced to hide a clause of the item. I checked the union of step uses against proof_deps and verified that each cited proof dependency has no transitive path back to the item.

## Unfinished work

None in the mathematical split. The required final server dry run and push are recorded below after they complete.
