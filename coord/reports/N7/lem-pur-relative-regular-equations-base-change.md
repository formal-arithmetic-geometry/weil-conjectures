# Stage-1 re-split: lem-pur-relative-regular-equations-base-change

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-relative-regular-equations-base-change.json`: statement and Lean record unchanged; the former step 5 is replaced by six shorter steps with citations for its hidden algebra inputs. Status is split. All five other original steps are preserved verbatim.
- `citations.json`: 17 verbatim statement quotations, one for each proof-step citation.
- `searches.jsonl`: the four searches actually run for this item; their records have been appended to the item's previous searches without replacing them.

No new nodes and no new Mathlib leaves. All required algebra inputs already have nodes. The auxiliary `repair.py` is sandbox-only preparation code, not a project script or a delivery file.

## Attachments

None. Searches of the slopmaster2 project for the item's blueprint tag, id, and relative-regular/base-change terminology found no declaration stating the item exactly. The regular-immersion module supplies flat base change, which does not allow the arbitrary change of base in this item. The existing side-project theorem recorded by NY is a stage-2 statement with `sorry`; its statement and metadata are retained. The algebraic fibre-Cartier declaration at Fiber.lean:981 is already attached to `lem-pc-algebra-fibre-cartier-local`; it is a reused input, not an attachment of the item.

## WANTED

None: all sources used are present locally.

## Reopened step repaired

I read `coord/repair-notes/lem-pur-relative-regular-equations-base-change.json`. The human's 2026-10-17 instruction requires keeping the existing statement and route, and exposing the hidden arguments in the 2303-character induction. I started from the current shared node; the sandbox had no previous node, report, or searches to preserve. I retained every pre-existing field outside the authorized proof, search and split-report changes, including the Lean record, historical review, blueprint ancestry and accepted tool metadata. This is a re-split, not a statement correction.

The hidden quotient/fibre identification now cites `lem-weil-pbc-tensor-quotient-base-change`; I wrote the two elementary balancing maps needed for its application over D rather than R. The ambient shrinking versus prefix-localization comparison cites `lem-weil-pbc-localization-quotient-commute`. Flatness of the earlier quotients cites `lem-pc-affine-flat-module-localization-preserves-flatness`. Finite presentation cites `lem-weil-pbc-localization-away-polynomial-quotient` and `lem-weil-pbc-finite-presentation-quotient-fg-ideal`. The fibre-Cartier criterion and exact-localization inputs were already cited, and remain so. Thus every non-elementary hidden input has its own existing node; creating nodes with these statements would duplicate the DAG. The parent retains the induction, its invariant, base, step and termination. It does not move the entire item or any conclusion clause into a new node.

The new induction steps have lengths 604, 763, 714, 573, 696 and 743 characters. No non-elementary step exceeds 2000 characters. The elementary generator calculation v=t f and the denominator calculation g=c/h^n remain written out. The longest remaining step, original step 6 (now 11), is 1665 characters and uses the existing flat-quotient tensor injection and prime-localization nodes. No unit or chapter route changes.

## Not duplicates

No new nodes. I searched the whole DAG by localization/flatness, quotient/tensor, finite-presentation/localization, and fibre-Cartier terminology, then read the matching statements. Whole-blueprint searches with `blueprint_refs.py search` for `flat localization`, `quotient finitely presented` and `relative regular` did not identify a blueprint statement replacing this item. The blueprint ancestor command confirms `lem-pur-divisor-class`, through `lem-pur-smooth-pair-local-coordinates`. The current main-20261015 divisor-class proof invokes the frame class in its opening sentence; its regular-equation prerequisite is exactly the recorded ancestry. The inherited unit metadata is preserved.

## Review by N7

I read the worker brief, stages/1-dag.md, SETUP.md (including the three authority levels), GOAL.md, dag-sync.md, the chapter and unit records, and delivery-errors B–E. For the item I read Stacks divisors.tex `lemma-relative-regular-immersion-flat-in-neighbourhood` (063U) and `remark-relative-regular-immersion-elements` (0FUD), and more-algebra.tex `lemma-relative-regular-immersion-algebra` (0CEP). These give the unchanged route through the Noetherian fibre, spreading the fibre sequence and repeated fibre-Cartier lifting. For the additional citations I read algebra.tex `proposition-localize-quotient` (00CT), `lemma-flat-localization` (00HT, including its localization proof), `lemma-compose-finite-type` (00F4), `lemma-principal-localization-NL` (08JZ, the displayed inverse presentation), and `lemma-tensor-product-exact` (00DF). There are no new node statements to source-check.

I opened the statement of every node cited, rather than using its title or its proof as an interface. The step checks are as follows.

1. The regular-to-graded node supplies exactly the canonical graded isomorphism from the specified regular sequence. The empty-sequence case is handled in the nonzero localization at q'.
2. The 0CEP node needs quotient flatness, which is a hypothesis here. The affine-Noetherian node applies to the finitely generated algebra over the residue field, not to the original base or algebra. The contraction q induces a prime in the localized fibre because its contraction in R is p.
3. Exact localization gives the graded quotient comparisons; powers identify by multiplication of fractions. The local quasi-regular-to-regular node applies because the fibre local ring is nonzero, Noetherian, local, and every equation belongs to its maximal ideal.
4. The principal-neighbourhood node assumes Noetherianity only of the fibre F. Its conclusion is regularity of the specified whole sequence on a principal open. Lifting gamma=a/r gives a outside q. The written inverse presentation and exact localization verify finite presentation and R-flatness of the initial D.
5. This is just the induction setup: all prefix flatness, finite-presentation and injection assertions are expressly in the invariant. The prime of D descends through each prefix quotient because every equation lies in q. Its contraction is p.
6. The tensor-quotient node states the algebra isomorphism B/IB = B tensor_D D/I, with no flatness hypothesis. Taking B=D tensor_R k and using the displayed inverse balancing maps gives precisely the prefix fibre. The next equation is injective by the fibre invariant, so at every prime the criterion's required open is obtained by g_P=1. This checks its global fibre hypothesis, rather than assuming a fact only at one point.
7. The existing fibre-Cartier node states both needed conclusions: a regular-principal ideal and a quotient flat over the original base. I checked its exact declaration at Fiber.lean:981, including flat finite presentation, field K, contraction equality and the all-primes condition. The explicit v=t f calculation proves injectivity for the specified equation, which cannot simply be inferred by changing generators without argument.
8. The quotient-localization node gives exactly D_i localized at the image of the lifted denominator. It therefore identifies the newly supplied flat quotient with D^+/(f_1,...,f_{e+1}). The equation g=c/h^n and c outside q justify the ambient principal shrinking A[1/(hc)].
9. The flat-module localization node applies with the R-flat D-module D_i, not with a supposed R-flat base-changing ring. Exact localization preserves earlier and fibre multiplication injections; quotient-localization identifies their domains with the requisite prefix quotients. The fibre localization maps are displayed explicitly and preserve the equations.
10. The inverse-presentation node supplies D[u]/(g u-1); adjoining u to the finite presentation of D gives the written finite presentation over R. The finite-presentation quotient node then applies to the finitely generated prefix ideals. Together with the previous steps this establishes the entire e+1 invariant and closes the finite induction.
11. The flat-quotient tensor-injection node applies with N=R' to each short exact sequence, since its last term D_i is R-flat. The displayed tensor flip preserves the multiplication map. The final weak-regular prime-localization node assumes injectivity of all prefix multiplication maps and membership of the equations in the prime; both are verified. The denominator h' avoids q' by contraction. The quotient is nonzero because it maps to the residue field at q', so this proves regularity in the project's sense, for arbitrary R'.

I declared the newly cited flat-module localization theorem as a generic off-unit tool in split_report.tool_uses, alongside the previously accepted principal-neighbourhood tool. The other additional inputs are existing Mathlib leaves. None replaces the unit's geometric route.

Small-case checks: b=0 gives the empty regular sequence in a nonzero prime localization; R'=0 gives no primes and a vacuous conclusion; A=R[x_1,...,x_b] with the variable sequence satisfies the claim under any change of base. In the induction e=0 the prefix ideal is zero and all comparison maps reduce to the identity; e=b ends the induction without another criterion application. Denominators avoid q, hence every prefix prime and its fibre point persist. A unit equation is excluded by q'-membership. No Noetherian assumption on R, A or R' is introduced. I checked the additional reused algebra statements also for the zero ideal and for localization by a unit; the comparison formulas become identities, as required.

For Mathlib I ran only the required msearch.py command, with the item's own id. LeanFinder and LeanSearch used different semantic phrasings; Loogle returned zero hits; grep returned regular-sequence preservation under flat base change. I read the hits and Regular/Flat.lean:34–94 and TensorProduct/Quotient.lean:51–82. The candidate regular-sequence lemmas require flatness (or faithful flatness) of the ambient scalar extension, which is not a hypothesis here. Prime-localization preservation is already a cited leaf, not a proof of the relative lifting theorem. All four services succeeded, so no failed service has been called evidence of absence. Previous search records are retained.

Against B–E: there is no new statement-only node to validate or duplicate, no new notion, no altered item hypothesis or weakened conclusion, no new source route, and no copied proof clause packaged as a lemma. Each proof citation has a verbatim statement quotation in citations.json. The newly used nodes are generic prerequisites and do not depend on the item; the server's DAG check will verify the complete closure. All writes are restricted to this sandbox. No Lean writing, compilation, Lake, git command in the shared repository, other agent, or SGA source was used.

## Source error retained from the earlier review

The unrestricted last sentence of Stacks 0FUD omits the condition that q' contain the equations. With R=k, A=k[t], f=t, R'=k and q'=(t-1), the equation becomes a unit locally and its final quotient is zero, so it is not regular under definition 00LF. The existing item already includes the necessary containing-prime hypothesis. I retain it verbatim and make no statement correction.

## Unfinished work

No mathematical work remains in this one-level split. The required remote dry run and direct delivery follow this report; they run no local DAG checker or compiler.
