# Stage-1 repair: thm-trf-dualizing-complex-composition

## Files written

- `dag/nodes/sec-trace-formula/thm-trf-dualizing-complex-composition.json`: retained statement and Steps 1–3; replaced the long coherence step by Steps 4–8 citing existing categorical Mathlib leaves. No exact Mathlib match for the geometric theorem.
- `citations.json`: fifteen step/node pairs, checked against current statements.
- `report.md`: this report; `prior-Q115-report.md` and `prior-item.json` preserve the prior proof/report without claiming that the earlier reader reviewed these edits. `searches.jsonl` contains only searches actually run for Q18.

New nodes: 0. New Mathlib leaves: 0. The existing Mathlib leaves `lem-weil-pbc-mate-pasting` and `def-weil-pbc-adjunction-conjugate` are reused. No unit file is changed: this is a consequence of the package rather than its key definition.

## Attachments

None. I searched the whole read-only `WeilConjectures/` by the exact blueprint id and by dualizing/composition terminology. I read `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex`, TensorHom.lean:366–384, and `nonempty_iso_rightDerivedUpperShriek_comp`, Composition.lean:144–152, including its implementation note at 29–36. The former proves existence of an isomorphism on the ordinary etale category. Neither declaration gives the specified canonical, composition-compatible family on the constructible pro-etale categories of this item. I therefore do not attach a partially matching declaration. No upstream master sorry is treated as a proof.

## WANTED

None.

## Return repaired and retained work

The route note refers to an earlier Q115 packet, but that sandbox no longer exists on this machine. Its complete report and proof survive in the shared repository, and are preserved here. The current Q18 dedicated return, read in full, is more recent: it requires repair of the old non-elementary Step 4 (3600 characters), retaining its route, statement and other steps. I followed that concrete diagnostic rather than restarting the mathematics or treating historical provider failures as failed proofs.

The old step proved several different categorical assertions inline: a binary comparison, pasting compatibility for triple composition, normalization of the identity adjunction, and the two identity equations. The first already belongs to `lem-cat-right-adjoint-composition`. The generic pasting and conjugation assertions already belong to `lem-weil-pbc-mate-pasting` and `def-weil-pbc-adjunction-conjugate`, both Mathlib leaves. These are now cited explicitly in Steps 4–6, so no hidden generic lemma remains embedded in the geometric proof. The remaining two unit calculations are short substitutions and counit naturality, retained as elementary Steps 7–8. This repairs the one numbered return point without making a duplicate node for any of its arguments.

The longest current step is 1142 characters. No non-elementary step exceeds 2000 characters. The statement and Steps 1–3 are exactly the shared versions; all the old comparison formulas and identity normalizations are preserved, with the long triple-transpose calculation replaced by the existing statement of mate pasting. No Lean field, maintainer field, source snapshot field or import flag is changed intentionally.

## Source and route

I read both the master and main-20261015 blueprint statement/proof, the companion current `.proof.md`, the trace-formula chapter record, and the sk-d-six unit record and current section. The current statement is identical to the retained one. It fixes one finite coefficient ring, separated finite-type d and admissible structure morphisms, and requires a canonical dualizing comparison compatible with composition. The unit requires equality of component maps in ordinary categories. The construction still follows compact-support composition, passage to right adjoints, and evaluation at the constant coefficient object.

I read Stacks `categories.tex`, Tags 0037 (`definition-adjoint`, lines 3344 onward), 0B65 (`lemma-transformation-between-functors-and-adjoints`, lines 3542 onward), and 0DV0 (`lemma-compose-counits`, lines 3576 onward), with their tag mappings in `tags/tags`. I also read Mathlib Adjunction/Basic.lean:567–585, Unique.lean:102–136, and Mates.lean:170–228, 275–375 and 486–525. These provide the pasted adjunction/counit, conjugation, its composition and identity laws, horizontal pasting, and changes of adjunctions. In particular Mates.lean:209 is `mateEquiv_hcomp`, exactly the categorical clause previously hidden in Step 4. The proof remains agent-written because it expands an agent-written blueprint. No SGA source is used.

The existing tool use `prop-functor-package` is retained and declared in `split_report.tool_uses`. Only clause (3), with its composition, associativity and unit equations, is consumed; no other package clause is used. The two newly cited categorical nodes are existing Mathlib leaves, so they impose no off-unit geometric route. I do not set a new maintainer-owned `tool_uses` field.

## Search and reuse

I searched the full DAG for mate/conjugate/pasting/adjoint-composition terminology and inspected the statements of the resulting categorical candidates, including `lem-cat-right-adjoint-composition`, `lem-weil-pbc-mate-pasting`, `def-weil-pbc-adjunction-conjugate`, `lem-sc-left-adjoint-composition-iso-associativity`, and `lem-weil-pbc-three-step-adjunction-comparison`. The left-adjoint associativity node assumes strict equality on its right adjoints, so is not the right direct specialization. The mate-pasting leaf states the needed generality without that extra assumption. `tools/blueprint_refs.py search 'mate'`, search 'conjugate', search 'adjoint composition', and ancestor inspection cover the imported blueprint as well. No new node was made and no blueprint duplicate is claimed.

The retained item records previous geometric Mathlib searches and their results. New Q18 searches use only msearch.py and are appended to the item after their output is read. The Loogle query for `CategoryTheory.mateEquiv_hcomp` returns precisely that declaration; the geometric grep `dualizingComplex|rightDerivedUpperShriek` has zero hits. LeanSearch's alternate phrasing about coherent right adjoints of compact support returns general right-adjoint composition, ordinary module pushforward, coreflective composition and rigid-category mates, which do not state this geometric theorem. These confirm reuse of the categorical leaves, without pretending they alone implement the geometric operations.

## Not duplicates

No new nodes. `lem-weil-pbc-mate-pasting` and `def-weil-pbc-adjunction-conjugate` already state the two generic assertions extracted from the old long step. Their elementary specializations are written in the item. No clause of the geometric theorem is renamed as a node.

## Review by Q18

I read delivery-errors B–E in full and checked the current files and sources, not just the historical review. There are no new unsplit statements, so B1–B7 introduce no new obligation. Existing notion dependencies remain those of the original statement. TeX is serialized once. The theorem's statement introduces no extra hypothesis and is unchanged.

Step 1 uses the current `def-trf-admissibility` and clause (3) of `prop-functor-package`. I opened both statements: the former supplies specified adjunctions on D^b_ctf and explicitly states availability for every separated finite-type map in the setting, covering d as well as a_X and a_F. The latter states compact-support composition with the two coherence equations. All categories have the same finite A and the same finite-Tor constructible domains. The dualizing definition puts X and F in the required separated finite-type setting. No ambient pro-etale right adjoint is assumed.

Step 2 uses `lem-cat-right-adjoint-composition`, whose statement asserts the natural right-adjoint comparison and the pasted-counit normalization. The transport of Hom precomposes with alpha inverse; its source is L_aF R_d R_aX N, then L_aX L_d R_d R_aX N, then N. Thus chi has the stated direction and the claimed canonical normalization. I checked the Mathlib pasted counit and rightAdjointUniq counit equation as well as the Stacks formulation.

Step 3 uses the three current definitions for coefficient conventions, finite Tor amplitude, and the dualizing complex. A_s is constant free rank one, constructible on one stratum, and its degree-zero flat model tensors with M to M. This proves Tor interval [0,0] for n>1 just as for n=1, without inferring Tor finiteness from bounded constructibility. Evaluation and substitution omega_Y = R_aY A_s are elementary. All three cited statements say exactly these used notions.

Step 4 applies the same categorical composition statement as Step 2 and identifies its displayed normalized transpose with the component formula in `def-weil-pbc-adjunction-conjugate`. I opened the conjugation statement: it includes the bijection, explicit component formula, invertibility, and composition law. The argument is generic at M, with no new geometric preservation assumption. Its sole purpose is to identify theta with the normalized mate before using pasting.

Step 5 uses the full statement of `lem-weil-pbc-mate-pasting`: clause (2) identifies the mate of a pasting under composite adjunctions with the two whiskered mates, and clause (3) transports along the comparison with the specified composite adjunction. I checked these clauses against Mates.lean:209, 486 and 505. With the other square an identity, they give the whiskered binary conjugates in each of the two paths. Composition of conjugates is the explicit composition clause in `def-weil-pbc-adjunction-conjugate`. The package's associativity law then identifies the two inverse left-composition paths. Both start at L_aH and end at L_aX L_d L_e; their conjugates both start at R_e R_d R_aX and end at R_aH. Thus no arbitrary comparison or unproved coherence is substituted. This is where the old long step's generic hidden lemma has been replaced by its existing node statement.

Step 6 uses the compact-support unit from the package and the explicit conjugation formula with the second adjunction id adjoint id. Substitution gives u = epsilon_id composed with lambda inverse. Conjugation preserves isomorphisms by the cited statement, so u is an isomorphism. This construction does not assume that the specified identity adjunction has identity counit.

Step 7 uses the package's source-unit equation and the transpose fixed in Step 2. Substituting alpha_g,id = L_g lambda gives epsilon_g composed with L_g u; transposition gives u. Step 8 uses the target-unit equation, naturality of lambda, and counit naturality for f. Its displayed equality has source L_f R_f R_id M and target M; transposing gives R_f u. These two are elementary substitutions and naturality equalities, with all formulas displayed. The only theorem invoked externally is the unit equation actually asserted by the package. Evaluation of these and Step 5 at A_s gives precisely the item's functoriality.

I verified every used node statement and prepared all fifteen verbatim citation pairs, not just tags in prose. The proof dependency list is exactly the union of the eight steps' uses. Newly cited prerequisites are generic Mathlib leaves, without any dependency on the item. No new definition or generic geometric tool has been introduced, and no new clause merely restates the item. Every non-elementary step is short and cites the actual statement it consumes.

Small cases: for d=id or a_X=id the two unit formulas give the normalized identification. With the identity adjunction on vector spaces over F_3 having both unit and counit -id, u is -id and the proof still works; treating it as literally id would fail. For empty source all comparisons are the unique maps of zero objects. For zero N the natural comparison specializes consistently. For n=1 and n>1 the coefficient unit remains free of rank one even when A is not a field; n=0 is excluded in the conventions. No properness, smoothness, regularity, dimension, or extra finite-Tor hypothesis on the input A_s was smuggled in. The source is not disputed.

## Unfinished work

None for this one-level repair. Existing prerequisites retain their own recorded states. The direct-delivery brief authorizes Q18 to run preflight and push; historical handoff text in the prior report does not describe this delivery.

## Validation

The required validation is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q18 thm-trf-dualizing-complex-composition --no-push`, followed, only after explicit OK and process exit, by the same command without --no-push. No compiler, Lake, local check_dag/review_split/preflight, manual git command, agent spawn, or write to the shared repository or launcher is used.

The Q18 LeanFinder phrasing returned eight results about ordinary derived exact functors and homological-complex localization, with no dualizing or exceptional pullback theorem. All four Q18 searches succeeded, and their exact query texts, hit counts and returned names are retained in searches.jsonl and appended to mathlib_searches.
