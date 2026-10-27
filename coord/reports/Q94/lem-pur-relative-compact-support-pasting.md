# Worker report: lem-pur-relative-compact-support-pasting

## Files written

- dag/nodes/sec-six-functors/lem-pur-relative-compact-support-pasting.json: statement split into seven steps; no full Mathlib match.
- citations.json: 21 verbatim dependency-statement excerpts, one for each step citation.
- searches.jsonl: required logger's records; inherited node search records preserved and current actual searches appended.

There are 0 new nodes and 0 new Mathlib leaves. The whole-DAG, blueprint and project-source searches found the needed constituent lemmas already present. No Lean, repository or launcher file was written, and no compiler/build was invoked.

## Attachments

None. The project has AlgebraicGeometry.CompactSupportFormalism.pfBaseChange_paste_horiz and .shriekBaseChange_paste_horiz in WeilConjectures/SixFunctors/LowerShriek/Formalism/BaseChange.lean (lines 176 and 411). These are useful formal analogues but quantify over a supplied CompactSupportFormalism; they do not themselves supply the actual constant-B strict derived tower operations and evaluation normalization in the item. The exact blueprint tag was absent. These declarations are not claimed as an attachment.

## WANTED

None. The Stacks sources and blueprint used here are available locally.

## Statement repair — STATEMENT-DISPUTED

The imported finite-identification sentence was out of domain. It asserted that for every finite B and arbitrary base maps the maps are those of def-exchange-projection. Reading that definition shows B must there be A_{E,n}, with schemes and maps of the indicated separated finite-type S-setting and ell invertible on S. For example B=F_2 × F_3 is a finite commutative ring but cannot be A_{E,n}: the latter is a quotient of a valuation ring and is local, while B has a nontrivial idempotent. An arbitrary map a need not be finite type, either. Thus applying the named definition is not type-correct at the original generality.

The repaired statement retains formal pasting and tower/ordinary evaluation for arbitrary commutative B and arbitrary base maps. Only the identification with that particular named finite definition is now explicitly made when its finite hypotheses hold. No proper-base-change isomorphism is asserted or used. This does not restrict the separated finite-type coefficient domain needed by the parent mixed Frobenius-pasting argument.

## Proof and search findings

The source for the item is Stacks Tag 0E47, sites-cohomology.tex, remark-compose-base-change-horizontal, read in full at lines 4093–4123. It explicitly omits the verification. The proof supplies that verification using the actual mate law, and gives the open and compact-support parts. I also read Tag 0D6D, lemma-derived-pullback-composition, including its representative construction, and proetale.tex Tag 09AE, definition-extension-zero. No prohibited SGA route is used. This is an agent proof, not a claim that Stacks states the strict-tower extension. The blueprint main-20261015 prop-pur-weil-equivariance-compatibilities.proof.md constituent-compatibility paragraph and the live parent lem-pur-weil-basechange-semilinear-pasting Steps 1–2 were read; the proof supplies their relative pasting constituent without changing the unit route.

Mathlib was searched by the required msearch.py logger using two semantic phrasings, Loogle, grep and LeanSearch. Loogle and grep locate CategoryTheory.mateEquiv_vcomp, Mathlib/CategoryTheory/Adjunction/Mates.lean:170. I read its full signature and proof: it provides exactly the abstract two-square mate identity, already represented by lem-weil-pbc-mate-pasting. The semantic hits include SheafOfModules.pullbackComp, pushforwardComp and ordinary Scheme.Modules compositors; I read the sheaf pullback compositor/associativity source. They do not contain open-extension, unbounded strict-tower or finite-evaluation clauses. No service failure was recorded as absence. No new node was needed for any of those hits.

## Not duplicates

No new nodes. Existing lem-weil-pbc-mate-pasting supplies the generic adjunction theorem; lem-cbc-strict-tower-pullback-square-pasting supplies the canonical square identity, and lem-cbc-strict-tower-proper-open-calculus supplies the normalized open comparison. The abelian etale and completed-exchange blueprint nodes found by blueprint_refs.py search pasting have different coefficients or boundedness and do not replace the present item. Search compactification and strict tower found no blueprint node stating all its clauses. The inherited blueprint.from place was already specific and is retained, with same_as empty.

## Review by Q94

I checked delivery-errors B–E against the actual node files and sources, rather than treating their names as sufficient evidence. There is no new statement-only node to audit, no copied clause posing as a lemma, and no new notion requiring a definition. The item already introduces every scheme, category and map. All seven steps are below 2000 characters. Proof dependencies are the exact union of uses. Each quotation in citations.json was tested as an exact substring of the current cited statement; the files were opened and read before using them. I also checked transitively that the proof constituents do not depend on this item.

Step 1 uses def-pc-fibre-product for the unique projection-preserving comparison and pur713-def-base-changed-compactification for the actual open/proper pullbacks. Uniqueness makes the comparison and associativity argument elementary; no isomorphism of base maps is assumed. The cited base-change statement explicitly says the upper open square is Cartesian and that the new factorization is a compactification.

Step 2 uses the stated evaluation normalization of def-cbc-strict-constant-tower-operations and the stated termwise open evaluation of def-cbc-strict-tower-open-extension. The non-elementary K-injective assertion is cited as lem-weil-tower-evaluation-kinjective, whose statement has no boundedness or exact-product assumption. lem-weil-pbc-kinjective-hom-derived supplies the required Hom computation, and def-weil-pbc-proetale-operations specifies the ordinary unbounded operations and their adjunction. def-weil-proetale-inverse-image supplies the sectionwise direct image, so matching the square/compositor section maps has a concrete meaning. lem-weil-pbc-coefficient-exchange-mates is used only after verifying its hypotheses: evaluation's pull comparisons are invertible and termwise, its push comparisons are the prescribed mates, and its pull cube commutes termwise. The open comparison is obtained by the same adjunction transpose of the open unit. Equalities will be proved on towers, never inferred from faithfulness of evaluations. Constant towers then supply ordinary complexes, including for infinite B.

Step 3 instantiates lem-cbc-strict-tower-pullback-square-pasting with vertical p,p_a,p_ab and transverse a,b,bar-a,bar-b. Its statement allows arbitrary commuting squares, hence applies to the Cartesian squares here. I wrote the types of both left squares explicitly. Clause 1 of lem-weil-pbc-mate-pasting is exactly the required direction of composition; clause 3 handles conjugate changes of adjunction, whose normalization is given in the tower operations definition. None of these lemmas requires the mate to be invertible.

Step 4 uses the first, arbitrary-B, open-square part of lem-cbc-strict-tower-proper-open-calculus. Its statement explicitly gives both open-unit normalization and successive-base-change equality, as well as finite evaluation. The etale-origin and bounded-below hypotheses elsewhere in that node apply to gamma invertibility and are not used. The base-changed-compactification statement verifies cartesianness of the open squares. This is reuse of an existing stronger statement, not a new node for the beta clause.

Step 5 is the elementary calculation assembling H. I expanded all four factors at K, stated precisely the naturality morphism beta_a,K at which E_b is used, and combined the resulting adjacent factors. The calculation requires no additional categorical existence result and is an equality on the actual derived tower category.

Step 6 uses mate-pasting and the normalized tower and open definitions, the sectionwise direct-image definition, and lem-weil-pbc-conjugate-iso-unit-equation. The last lemma asserts uniqueness of the unit-preserving adjoint comparison, exactly what is used to pass from the same projection/section maps to coherent inverse images. Both threefold mates have the same left square; both open comparisons are the same threefold paste. Associativity of composition and Step 5 then give the H assertion. This is the short three-map case required by the statement, not an unproved coherence claim for arbitrary diagrams.

Step 7 compares the displayed definition of Ex_!^c in def-exchange-projection factor by factor, using the finite evaluation assertion of the strict open calculus. I checked its domain explicitly and corrected the original overbroad identification as described above. This does not invoke finite proper base change, etale origin, a lower bound, an equivariant compactification or invertibility of a.

I tested empty opens, j=id, identity base maps, B=0, infinite B=Z and nonconstant towers. Empty open extension makes H the unique map on zero objects; j=id removes beta; identity comparisons are the normalized units. The algebraic mate argument continues to work for noninvertible E and nonconstant towers. The proof uses neither a common bound on tower levels nor joint faithfulness of derived evaluation. The ring F_2 × F_3 tests the repaired finite-definition domain.

## Unfinished work

None in the requested one-level split. Existing unsplit constituent dependencies keep their own statements and are not edited. The report records generic off-unit tools in split_report.tool_uses for the maintainer's review.
