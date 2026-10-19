# Stage-1 delivery: lem-trf-tensor-kernel-factorization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tensor-kernel-factorization.json`: statement, split into five steps; statement and its two statement dependencies unchanged; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-universally-exact-fp-split.json`: statement-only, unsplit, Stacks Tag 058L; Mathlib searches find no match.
- `citations.json`: one verbatim statement quote for each node cited in each proof step.

The sandbox initially contained only brief markers, with no previous item, proof, report or searches. The shared repository's existing statement, provenance and inherited search records were retained. Current searches are recorded by msearch.py in this item's searches.jsonl. `prepare.py` is the item-local preparation script, not a project-file change.

## Attachments

None. I searched the exact blueprint id, domination, universally exact / universally injective module terminology and tensor-kernel terminology in the read-only slopmaster2 project source and the upstream names map. No project declaration states this factorization criterion or the new splitting criterion. The master checkout is reference material only; no master sorry declaration is counted as proved.

## WANTED

None. All sources used are in `literature/stacks-project/algebra.tex`.

## Findings and changes

The item is mathematically correct and its statement is unchanged. The imported statement combined Stacks 059C and 059D but supplied no proof. I expanded the quotient pushout rather than adding a new node which simply reasserts a clause of the item. The only new node is the independent generic splitting theorem, Tag 058L, which works for any universally exact sequence with finitely presented quotient and has no two maps with common source or domination hypothesis.

The original finite-test reduction can be performed on the pushout inclusion by the existing `lem-trf-universal-injective-finite-test`, avoiding another new node for Tag 059C. The tensor-of-pushout calculation is three lines from existing tensor right exactness and an explicit bilinear finite-sum isomorphism; it is written in steps 2–3, not hidden in an uncited pushout theorem. Step 2 is elementary; step 3 is non-elementary because it invokes right exactness.

I retained the historical blueprint ancestor and via chain. The parent `lem-trf-mittag-leffler-hom-systems`, step 5, uses this item exactly with a finitely presented transition cokernel. The current unit is sk-i-curve-zero; its key node, chapter and realized fields are untouched. The same-unit finite-test result and the Mathlib right-exactness leaf are generic supporting tools; no off-unit unsplit theorem is used and no new unit route is introduced. No SGA source is cited.

## Not duplicates

- `lem-trf-universally-exact-fp-split` vs `lem-trf-universal-injective-finite-test`: the existing node detects universal injectivity from finitely presented tests; it gives no retraction and has no finitely presented quotient hypothesis.
- `lem-trf-universally-exact-fp-split` vs `lem-trf-local-ui-flat-cokernel`: the existing node assumes a flat middle term and concludes a flat quotient; it does not split the sequence.
- `lem-trf-universally-exact-fp-split` vs `lem-weil-pbc-pushout-short-exact-sequence`: the existing node constructs a pushed-out extension in an abelian category; it asserts no splitting or tensor-purity criterion.
- `lem-trf-universally-exact-fp-split` vs `lem-trf-tensor-kernel-factorization`: the item concludes a factorization from two maps and finite tensor-kernel inclusions; the new node is the general pure-sequence splitting input, applied only after the explicit pushout and kernel calculation.

Whole-DAG searches for 058L, the source label lemma-universally-exact-split, and universal-exact splitting found no existing statement. Whole-blueprint searches for 058L, universally exact, and the full splitting concept found no match. The item was separately searched in the whole blueprint by tensor-kernel/factorization terminology; `same_as` remains empty. The new node inherits the nearest blueprint ancestor printed by blueprint_refs.py and prepends the item to via.

## Review by NJ

I read the chapter, unit, worker brief and stage-1 rules, the human's three blueprint levels, GOAL.md and dag-sync.md, and delivery-errors B–E. For the item I read Stacks algebra.tex, labels lemma-domination-fp (059C), lemma-domination-universally-injective (0AUM) and lemma-domination (059D), including their proofs. For the new node I read lemma-universally-exact-split (058L) and its proof, checking the tag against tags/tags. The 059D argument uses exactly this splitting result after forming the pushout. The new node states only its conclusion, in the retraction form; its proof is intentionally left for the next split.

Step 1 uses the statement of def-sc-finitely-presented-module only to identify the given quotient as finitely presented. Everything else is an explicit quotient computation: delta need not be injective; p is well defined because the second coordinate of delta is -f, and ker p = image a follows by writing v=f(u). This proves right exactness before any tensor operation.

Step 2 uses def-weil-pbc-module-tensor-product's actual bilinear universal property, pure-tensor generation and induced-map formula. I wrote both inverse maps for the two-summand tensor comparison and checked the identities on generators. This is a definition-level computation, not an invocation of general preservation of pushouts.

Step 3 uses lem-weil-pbc-tensor-right-exact's statement: exactness at the tensor of the middle module for the quotient sequence from step 1. Its required last-map surjectivity is the quotient map rho. It supplies a tensor z from U tensor Q, even though a tensor in a kernel need not be a pure tensor. The pair identity gives f_Q(z)=0 and t=g_Q(z), so the *given* kernel inclusion kills t. The kernel direction and minus sign were checked explicitly.

Step 4 uses the full statement of lem-trf-universal-injective-finite-test. That statement tensors on the other side, so I supplied the factor-swap isomorphisms and their naturality on pure tensors, and checked how Q=R recovers injectivity of a itself. The cited right-exactness statement, applied to the already exact W -> P -> C -> 0, gives exactness and surjectivity after every tensor. Together these are precisely the universal exactness hypothesis needed next. No flatness is inferred or assumed.

Step 5 uses the newly stated 058L retraction theorem. Here its A,B,C are W,P,V/f(U); all short-exactness clauses were proved in steps 1 and 4, and finite presentation is the original hypothesis. Its conclusion is exactly r a = id, which is the formula actually used. Then h=r b satisfies h f=r b f=r a g=g. Every cited node's statement was opened, read, and copied verbatim into citations.json; no citation uses a node's proof in place of its statement.

I tested zero ring / zero modules; f=0 (the Q=R test forces g=0); surjective f (C=0, so the criterion reduces to descent through its kernel); f=id; and f=2:Z->Z, g=id (the Q=Z/2 test fails, as it must). The new 058L statement holds for split A->A direct-sum C->C, including C=0; 0->Z --2--> Z->Z/2->0 fails the tensor-purity hypothesis for Q=Z/2, so there is no false splitting assertion. No finite generation of W or V entered the argument. All five steps are below 2000 characters, so no long-step claim conceals an extra lemma.

Mathlib searches used leanfinder, loogle, grep and leansearch, followed by a second semantic phrasing. I read the tempting local splitting and finite-presentation source declarations: Module.finitePresentation_of_split_exact at FinitePresentation.lean:251 assumes a splitting and concludes finite presentation of the left term, and the variant at :269 requires a projective quotient; LinearMap.split_surjective_of_localization_maximal requires local sections. The flat equational criterion (EquationalCriterion.lean:270) has a flat target and an unspecified finite free middle module. None specializes in one line to this item or 058L. The new node is unsplit, with no proof or proof dependencies. No statement dispute, hidden definition or target change was found.

## Unfinished work

None for this one-level split. The single new statement-only supporting node remains unsplit by design.
