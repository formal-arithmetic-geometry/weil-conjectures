# Stage 1 delivery: lem-pd-total-oplax-conjugation-constraints

## Files written

- dag/nodes/sec-poincare-duality/lem-pd-total-oplax-conjugation-constraints.json: statement, split into ten proof steps; not a Mathlib leaf. Statement and statement dependencies unchanged.
- citations.json: one verbatim statement quotation for each of the nineteen step/node citations.
- report.md and searches.jsonl: this report and the actual search record.
- write_split.py: sandbox-only preparation script, not delivery material. The reviewed JSON is the deliverable; it also includes subsequent corrections to this script's initial output.

No new DAG nodes and no Mathlib leaves.

## Attachments

None. Searches for the blueprint id and the total/oplax/conjugation notions in lean/WeilConjectures found no declaration stating the item. CategoryTheory.isMonoidal_conjugateEquiv_symm concerns adjunction conjugates of monoidal natural transformations, not this arbitrary natural isomorphism or these total summand formulas. The mapCochainComplexMonoidal implementation supplies the single-functor ingredient already represented by lem-sfb-termwise-strong-monoidal; it does not state the present functor-square result.

## WANTED

None. The source proof hints and the project source needed for comparison are present.

## Problems found and scope

The item was unsplit, with an empty proof, and the abstract functor-square extraction is not a verbatim assertion of Stacks 0FPQ. The proof is honestly marked agent-written, using that tag for the monoidal total constraints and its degree-zero unit hints, and existing DAG statements for the actual mathematical inputs. I did not infer monoidality of the arbitrary isomorphism a or identify its conjugated comparison with the separate Fs comparison.

The blueprint ancestor command returns None: this is below a seeded new target, not an imported blueprint statement. I preserved the inherited precise from.place and via chain, searched the entire imported blueprint for total tensor and conjugation, and checked the current latest blueprint (the sec-six-functors/sk-thm-sf-verdier-exchange unit). Its complement retains the tensor-Hom Verdier-exchange route. This abstract comparison is a subordinate tool and does not change that route or any unit/chapter record.

The first draft's shell/JavaScript string encoding damaged several TeX commands. I corrected the actual JSON, read all ten corrected proof steps, and checked for control characters. Step 8 now explicitly resets M to P^n, since the earlier associator step's M=P^p must not silently persist into the unitor calculation. The infinite-sum step explains how E0's natural tensorator identifies its inner tensored cocone with the tensor of its preserved double-total cocone.

## Unfinished work

None for this one-level split. Existing cited nodes remain independently queued according to their own states. No Lean was written or compiled.

## Not duplicates

No new nodes. In particular I reused lem-pd-total-oplax-conjugation-summands for the forward conjugation equation and lem-sfb-termwise-strong-monoidal for canonical single-functor totalization instead of creating inverse, associator-path, or unit-path clauses as separate nodes.

## Review by Q93

I read Stacks sites-cohomology.tex, lemma-symmetric-monoidal-cat-complexes (Tag 0FPQ), including its explicit degree-zero unit and omitted constraint verifications, and homology.tex, definition-associated-simple-complex (Tag 012Z) and remark-triple-complex. The latter gives the countable direct-sum total and the three differential coefficients 1, (-1)^p, (-1)^(p+q). I also read the single-functor implementation in WeilConjectures/Algebra/Homology/Monoidal/MapHomologicalComplex.lean (comparison summands, associativity, left/right unit proofs and mapCochainComplexMonoidal) and Mathlib/Algebra/Homology/Monoidal.lean (tensor inclusions, associator, and unit constructions). There are no new nodes needing separate source checks. The item statement is unchanged and has no statement dispute.

I opened the statements of every cited node. Step 1 uses lem-sfb-termwise-strong-monoidal for natural chain isomorphisms T and j and lem-pd-total-oplax-conjugation-summands for the actual forward A restriction and preservation by the equivalences. Their hypotheses match: abelian monoidal categories, additive tensors, small colimits preserved by tensor, and countable coproduct preservation by Fi and Fs. The equivalences satisfy the remaining preservation assumptions. I checked the epsilon orientation: j uses the inverse of the strong unit, exactly the item's oplax epsilon.

Step 2 takes only that forward formula and the existing chain isomorphism; multiplying on the indicated sides gives the inverse formula with the correct source and target. Its differential equation follows by cancellation in adjacent degrees, so no unproved flatness or quasi-isomorphism assertion enters. Step 3 uses the exact j component statement to compute J in degree zero. The zero-object argument is written explicitly using additivity; it proves uniqueness in every other degree.

Step 4 uses the two cited summand formulas, cancels Fs(T_E0^-1)Fs(T_E0), and computes g without treating a as monoidal. Its naturality is the composition of the tensorator naturalities in def-sfb-strong-monoidal-functor and the assumed naturality of a. Step 5 uses precisely the associator-induced-from-reindexing clause of lem-sfb-total-tensor-homotopy and the tensor-on-chain-maps formula in def-sfb-preserves-kflat-quasi-iso. The two nested inclusions have different parenthesized sources, and the ordinary associator is retained between them.

Steps 6 and 7 substitute the Step 4 equation twice, with naturality for the ordinary inner coproduct injection between the substitutions, and then the Step 5 associator equation. Each intermediate map is displayed. Their tensor-on-map input is exactly the cited definition, not a claim hidden in a definition's proof. The final restrictions both land through the right-nested target inclusion, with the ordinary associator in the correct position in the second path. Step 8 uses the cited induced unitors, the tensor-on-map rule, and the actual j formula. It tests (0,n) on the left and (n,0) on the right, including negative n. Tensor of a zero object vanishes by the explicit colimit-preservation hypothesis, including the empty colimit.

Step 9 checks the comparison maps in the transported diagrams: the inner a and a^-1 cancel and the outer a^-1 moves past the source constraint by naturality; the remaining E1 comparisons are exactly the coherence clauses of lem-sfb-termwise-strong-monoidal. Reintroducing E0 gives Fs(h^-1) and Fs(epsilon_E0^-1), so it recovers the specified A,J rather than merely some coherent structure. Step 10 uses the full universal-property statement of def-weil-pbc-category-colimit and the cocone-preservation assertion of the summand lemma. I checked preservation separately for the inner tensor-distributed cocone and the outer total cocone, and then apply Fs's assumed countable preservation. Thus the equality test is valid on infinite sums without an unjustified finite-support element argument.

Small cases checked: all zero complexes; complexes concentrated in degree zero, where every calculation reduces to its ordinary counterpart; a unit tensored with a complex concentrated in any negative degree; and Fi=Fs=E0=E1=identity with a an arbitrary invertible scalar natural transformation of vector spaces. For scalar a=c, g=c times identity and e=c^-1; the associator paths both acquire c^2 and the unit composite has coefficient c^-1 c=1. This explicitly tests the absence of a monoidality assumption. For an unbounded complex with all degree terms nonzero, the inverse and path equations still use coproduct universal properties and never sum a family of maps into a non-coproduct target by an infinite additive operation.

I checked delivery-errors B through E: all objects are introduced by the unchanged statement; no statement-only node contains a proof; no new elementary or duplicate node was created; no source tag is used as a substitute for a node citation; all nineteen quotations are verbatim portions of the actual cited statements. There is no new dependency cycle through the parent comparison. The sources are Stacks and project/Mathlib code, with no SGA. Every proof step is below 2000 characters. The non-elementary ingredients are existing cited lemmas; the remaining calculations explicitly use their statements, naturality, inverse cancellation, or the colimit universal property.

Real Mathlib searches were run with msearch.py using LeanFinder twice, LeanSearch, Loogle, and grep twice. Hits included coproduct comparison inverse formulas, graded tensor inclusions, HomologicalComplex associators and unitors, and CoreMonoidal.ofOplaxMonoidal_μIso. These give fragments already covered by the cited DAG tools, not the full conjugated path specification. The grep invocation given a single source file produced malformed file labels in the search wrapper's output; its unmodified logged result is retained, and I read the actual Mathlib file directly for interpretation. The directory grep and both semantic services worked. No unrun search is recorded.

The three generic tool uses from outside this unit are declared in split_report.tool_uses: the forward functor-square summand lemma, the single-functor totalization lemma, and the induced total constraints lemma. The current Verdier-exchange unit does not state these monoidal-complex tools; they serve its comparison infrastructure and do not replace its route.

## Validation

Required deliver.py --no-push completed successfully: OK (not pushed), commit 7fb8d526e07, preflight passed. This includes the server DAG and split checks. The final dry run is repeated after recording this result, then the same reviewed files are pushed.
