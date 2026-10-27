# Worker report: lem-sfb-semiabelian-trait-hom-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-trait-hom-extension.json`: item, statement unchanged, two proof steps identifying the generic-fibre notation and applying the existing equivalent trait theorem. Five searches refreshed from this item's actual `msearch.py` log; no Mathlib match.
- `citations.json`: three exact statement quotations, one for each node used by a proof step.
- `report.md`: this report. `searches.jsonl` was written by the prescribed search command.

New nodes: 0. Mathlib leaves: 0. No Lean, unit, chapter, repository, or launcher file was written. No compiler or build was run.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact blueprint tag and for `semiabelian`, `semi-abelian`, `semiAbelian`, and `SemiAbelian` found no declaration stating the item. The cited DAG theorem is an existing unsplit node, not a finished Lean attachment.

## Wanted sources

WANTED: G. Faltings, *Finiteness Theorems for Abelian Varieties over Number Fields*, Arithmetic Geometry (1986), Chapter II, section 2, Lemma 1, printed pp.10-11, for `lem-sfb-semiabelian-trait-hom-extension` and its already-existing equivalent input `lem-sfb-trait-semiabelian-hom-extension`. The named local PDF is absent. I read the primary scan online at https://www-fourier.univ-grenoble-alpes.fr/~lefourns/contenu/Zywina/Faltings.pdf, especially PDF pages 1-2 (printed pp.10-11). No document was downloaded into the repository.

## Existing duplicate and source limitations

The whole-DAG search found `lem-sfb-trait-semiabelian-hom-extension`, already present in the sibling graph-properness branch from Q09. Its statement is identical in mathematical content to this item. Both quantify over an arbitrary DVR, the same smooth separated commutative finite-presentation group schemes with the same definition of semiabelian geometric fibres, and every generic group homomorphism; both conclude a unique group homomorphism over the trait. The only differences are `F` versus `L`, the displayed base-change notation versus the term generic scheme fibre, and explicit explanatory exclusions of additional hypotheses. Absence of a properness or residue-characteristic assumption in the cited theorem is just as strong as the corresponding explanatory sentence in this item.

Stage 1 asks workers to reuse existing statements and the maintainer to merge duplicates. Accordingly this delivery creates no replacement theorem: it makes the item's dependency on the pre-existing equivalent node explicit. The maintainer should canonicalize the duplicate pair and repoint callers when merging is appropriate; I have not edited the other node or any caller. The substantive trait theorem remains on the queue under the already-existing node. This delivery does not claim to have supplied its independent mathematical proof.

Faltings Lemma 1 asserts extension over a normal base; its proof begins by treating the complete-DVR input as known and then gives a graph argument. Merely moving this whole item's assertion to a newly named complete-DVR theorem would fail D1/D2. I did not do that. The proof here is agent-written reuse of the existing input, and is marked `proof_origin.by = agent`; it does not pretend the omitted complete-DVR proof has been read in Faltings.

No statement dispute was found. The item's statement, source metadata, imported fields, inherited blueprint place and ancestry chain are retained. `blueprint_refs.py ancestor` returns `None`; no imported blueprint ancestor should be invented. The searches `blueprint_refs.py search semiabelian` and `search semi-abelian` return zero blueprint nodes. The latest chapter and unit were read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/`; the unit text differs from the older record, but this auxiliary, identical trait input does not alter its six-functor route. No unit or chapter is changed.

## Not duplicates

`lem-sfb-semiabelian-trait-hom-extension` vs `lem-sfb-trait-semiabelian-hom-extension`: these EXISTING nodes are exact duplicates after renaming `L` to `F`. This delivery cites the latter and creates no new node; the pair is flagged for maintainer canonicalization, not asserted to be different.

There are no new-node/existing-node pairs to justify.

## Review by Q08

I read the item's source passage in the primary Faltings scan, the statements of `lem-sfb-trait-semiabelian-hom-extension`, `def-pc-scheme-fibre`, and `def-pc-base-change`, and the common definition `def-sfb-semiabelian-geometric-fibres`. No new node needs a separate source. I checked B-E against the actual two-step proof, not against the titles of the cited files.

Step 1 uses `def-pc-scheme-fibre` for the defining fibre product, and `def-pc-base-change` for the same base-change construction and induced morphism. Thus the groups and homomorphism denoted with subscript `L` are exactly the ones denoted with subscript `F` after taking `F=L`. This is a notation identification, marked elementary, with no descent, extension, or density theorem hidden in it. The quotes in `citations.json` were copied verbatim from the respective statements and checked as substrings.

Step 2 uses only `lem-sfb-trait-semiabelian-hom-extension`. I read its entire statement and compared all hypotheses: its ring need not be complete or excellent; its groups are separated, smooth, commutative and of finite presentation; the semiabelian condition uses the very same definition; and its input is a group homomorphism, not a general rational map. Its conclusion gives BOTH existence and uniqueness, as the exact quoted sentence records. No extra hypothesis on the residue field, residue characteristic, or properness occurs. Setting the supplied extension equal to the desired one finishes the item. This non-elementary input is cited explicitly; nothing is inferred merely from the definition of semiabelian or from separatedness. In particular C1 and C4 do not conceal the hard extension theorem: it is precisely the existing node being reused.

I tested the comparison on rank-zero tori (abelian fibres), on `G=H` equal to the identity group, on split multiplicative groups with integral power maps, and on families whose toric rank jumps at the closed point. The notation change and the match of hypotheses remain the same in each case; there is no constant-toric-rank, properness or perfect-residue-field restriction added in the proof. Uniqueness includes the zero homomorphism. These are tests of the reduction, not independent proofs of the existing input.

The existing trait node's full statement/proof dependency closure was traversed: it does not reach this item, so adding this dependency creates no cycle. It belongs to the same chapter and unit; no off-route tool use is required. No proof step has 2000 characters, and the entire assembly proof is under 3000 characters. No new nodes have been introduced to restate clauses, package elementary observations, or duplicate a source tag (B1, B9, C5, D1-D2). No SGA source is used.

I ran LeanFinder twice with different semantic phrasings, LeanSearch, Loogle, and Mathlib grep only through the prescribed `msearch.py` command, then read every returned signature. The valuative-criterion hits concern lifting for a morphism already satisfying a criterion; they do not give the needed semiabelian extension theorem. The second phrasing returns group-object base change and scheme extensionality, which also do not assert this extension. Loogle and grep returned no hits. All services were available. The five recorded entries are the exact queries and result summaries in this item's `searches.jsonl`.

The main correction to the planned work was to stop attempting another mathematical split once the exact existing theorem was found. The theorem itself is not claimed finished; its original queue entry remains responsible for its proof. This obeys the reuse rule and avoids another duplicate branch.

## Unfinished work

No assigned delivery preparation remains apart from the dry run and push below. The mathematical proof of the already-existing cited theorem is its own stage-1 queue item, not a new node created in this delivery. No WANTED source was silently replaced by an uncited theorem.

## Validation

The required `deliver.py Q08 lem-sfb-semiabelian-trait-hom-extension --no-push` exited 0 and printed `OK (not pushed)` at `922b0e0bc48`: server preflight passed. The direct-delivery command is run after that dry run exited; its final commit identifier is reported by the command and in the worker final answer. No local DAG checker or review script was run.
