# Q12 stage-1 report: lem-pur-clopen-exceptional-scalar-descent

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-clopen-exceptional-scalar-descent.json`: statement; split using existing nodes only; no exact Mathlib match.
- `citations.json`: a verbatim statement excerpt for every citation in each of the ten proof steps.
- `searches.jsonl`: six actual Q12 searches, including a corrected Loogle namespace. Inherited item searches are retained separately in the node, without claiming to have rerun them.
- `zheng.txt`: sandbox text extraction of the existing source PDF; `write_split.py`: sandbox preparation script.

There are zero new nodes and zero new Mathlib leaves. The item statement, statement dependencies, source, created metadata, blueprint provenance and import fields are unchanged. Its proof was empty in both the repository and the initial sandbox; there was no earlier split or delivery to repeat. No Lean was written and no compiler, Lake or build tool was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for clopen/scalar/exceptional comparisons, including the SixFunctors subtree. The existing clopen idempotent file concerns finite-coefficient projectors, not this all-stage strict-system comparison. No project declaration stating the entire item was found. Sorry declarations would not count as attachments.

## WANTED

None. The source material used is already present.

## What was wrong and what changed

There is no statement dispute. The imported source is an unsplit task extracted from former parent steps 10–11. I read those full retained paragraphs in `coord/reports/Q121/lem-pur-finite-clopen-exceptional-restriction.md`. Their phrases “transposing these squares” and “pass through DU and Rlim” need actual map calculations, and common-stage descent needs the representative calculation. These are now expanded. No scalar square is inferred merely from agreement of finite evaluations.

I read the chapter and the item's actual unit, `sk-def-purity-conv`. This convention unit has no proof steps to rebind; its route uses the six-operation constructions. The current main-20261015 ancestor `def-pur-section-invariant.md` defines the dualizing section invariant and ends with the invertibility sentence. The present task supplies scalar coherence of the clopen identification used below that sentence, not a new smooth-purity route. The historical chapter/unit source path still names master; the current main snapshot was used for the ancestor text. No SGA source is used.

## Searches and reuse

Before considering any new node I searched the DAG and blueprint for clopen, scalar coherence, field descent, mates, finite-free tensor/limit transport, and cofinality. I read the actual statements of the existing coefficient projection, scalar-mate coherence, cofinal-mate, clopen support/counit/integral realization, completed scalar comparison, finite-free tower transport, scalar localization, and common-stage definition nodes. Those cover the non-elementary tools, so no new statement-only node is justified.

For the item I ran the prescribed msearch command with LeanFinder twice (different semantic phrasings), LeanSearch, Loogle, and Mathlib grep. All returned normally. The first Loogle query `CategoryTheory.Adjunction.mateEquiv` reported an unknown identifier; I recorded exactly that and corrected it to `CategoryTheory.mateEquiv`. I read the returned source: `Mathlib/CategoryTheory/Adjunction/Mates.lean:84` is the general square/mate bijection, with its counit equation at 123, vertical pasting at 170, and horizontal pasting at 209; `Adjunction/Unique.lean:102` and 127 give normalized uniqueness of right adjoints. The ModuleCat hits are ordinary extension/restriction adjunctions. The LeanFinder hits concern Galois lifts, locally constant functors, and ordinary inverse-system naturality. None states this theorem or specializes to it in one line. General mate machinery is already represented in the DAG and is reused, not re-created as a new leaf.

## Not duplicates

No new nodes. In particular I did not create nodes for the sectionwise balancing identity, for naturality after rationalization, or for common-stage cancellation: those are explicit elementary steps using the stated constructions. I did not reuse the similar compact-support refinement/cofinal results with separated-scheme or finite-Tor hypotheses, since this item allows nonseparated Y and arbitrary bounded constructible inputs. The selected generic finite-free total-limit node has neither restriction.

## Review by Q12

I read Zheng Construction 4.1, Construction 5.15, Lemma 5.16 and its following Brown adjunction, and Lemma 5.22 in the supplied PDF (sandbox text extraction). They give the strict-system and counit-normalized route, rather than claiming that the entire all-stage assertion is a verbatim theorem of Zheng. I also read Stacks `sites-modules.tex`, Tag 03DI (`lemma-extension-by-zero`) including its explicit sum presheaf, and 03DJ (`lemma-extension-by-zero-exact`). Rational and common-stage steps follow the actual project definitions and are marked as an agent proof. The proof_origin explicitly says this.

For step 1 I checked that the strict-support node supplies the actual compositor, the componentwise adjunction and its termwise counits. The local-field stage node supplies finite freeness, the shared basis reductions, and the ramified quotient identities. The written generator computation proves the scalar square for extension and insertion without making a new node for a few-line tensor calculation. Transition compatibility is checked on m tensor b, including the reduced coefficient.

For step 2 I checked the coefficient-projection statement, not its proof: it specifies q as the transpose of F of the scalar unit followed by the restriction identification. Both component compactifications have exactly the same proper part. Thus transposing the two proposed composites reduces to step 1 and naturality of that unit. The cited mate definition explicitly supplies a bijection, so equality of transposes is enough; it is not just a definition cited for a missing theorem.

For step 3 I checked the counit equation in the clopen-adjoint node and the explicit scalar-transpose equation in the scalar-mate node. The former comparison uses b inverse, and the insertion counit occurs in the composite adjunction, with source F_g_i r_i G_g. I checked the two pasting clauses and change-of-adjunction clause of the cited mate-pasting statement. They give exactly the two sides of the requested right square. Invertibility here is already asserted by the two comparison nodes: I do not claim arbitrary mates of isomorphisms are invertible.

For step 4 the actual coefficient-projection and scalar-mate statements give identity, tensor-associator, quotient and tower equations. The cofinal-mate node preserves counits and maps and identifies the O'/(varpi')^(en) construction with the O'/varpi^n construction. This is the required ramified indexing, not an identification of the two towers at equal unramified indices.

For step 5 the site/integral-realization node states the actual transported system map. The exceptional definition states the reduction and forgetful functors, with their action on arrows. The written balancing maps identify input reductions and their transitions; finite-free tensor is a single fixed finite direct sum, so the additive site functors commute with it. The comparison does not use faithfulness of evaluations.

For step 6 I checked the finite-free completed-scalar node on any scheme (including nonseparated Y), and the arbitrary small-ringed-site strict-tower transport theorem. Its statement explicitly supplies a canonical natural derived-limit comparison on entire towers, with no boundedness or exact-product hypothesis. The realization node identifies the particular realized rho. O-linearity follows from the asserted linear system rho and the linear forgetful and total-limit construction. No ambient unbounded pro-etale exceptional adjunction, separatedness over k, finite-Tor input, or orientation is added.

For step 7 I wrote the full elementary cofinal calculation rather than citing a restricted Roos lemma. The left adjoint repeats the retained object in the preceding block; exactness follows levelwise, and its Hom adjunction proves preservation of K-injectives. Extension of a compatible family by any later retained index is independent of that index. The actual total-limit theorem says it is computed on a K-injective tower, so the resulting comparison is the prescribed natural derived comparison. This is the same explicit calculation recorded in the exceptional definition, and it applies to maps and further restrictions.

For step 8 the semilinear localization theorem explicitly states that transformations, inverses, whiskering and equations extend. The two operation definitions specify exactly these rationalized functors; no comparison to a different coefficient category is assumed. For step 9 I checked the common-stage Hom equivalence relation in the algebraically closed definition and the common-stage operation map rules in both operation definitions. Conjugating by theta and using the scalar square reduces naturality to the finite-field naturality equation; equal representatives become equal images after one further extension. Inverse components compose to identity already at their field of definition. For step 10 I checked the exceptional unit formula and the clopen theorem's tensor-unit and empty-family clauses. Empty sheaf and system categories are zero by the empty covering axiom, so no nonzero exceptional arrow is being silently selected.

Every citation in every step has its literal statement quote in citations.json; I verified these against the current read clone. Existing dependency closures have no path back to the item. Proof dependencies are exactly the union of uses. The off-unit generic tools are declared with reasons in split_report.tool_uses, for maintainer review. No unit or chapter file was changed. Every step is below 2000 characters, and none conceals a standard comparison lemma: each non-elementary tool is an existing cited statement. I checked delivery-errors B–E in full, including both historical copies, against this delivery. Since there are no new nodes, B's statement-only and new-node duplicate/source/search obligations add no new files; the item retains its searches and provenance.

Small cases checked: one component equal to all X gives identity comparisons; two clopen copies with fold map give the diagonal right adjoint and the stated component square; an empty component gives only zero arrows; empty I forces empty X and has no component index. Identity coefficient extension and n=1 work. A ramified extension uses en, with e>=1, and consecutive extensions multiply the indices; the tensor formula sends ((m tensor b) tensor c) to m tensor bc. Nonseparated Y remains allowed by every chosen geometric coefficient-system statement. No changes to the statement were needed.

## Unfinished work

No missing ingredient remains in this stage-1 split. Existing unsplit dependencies remain tasks of their own. This delivery claims completion of the item's one-level split, not finished Lean proofs of those dependencies.
