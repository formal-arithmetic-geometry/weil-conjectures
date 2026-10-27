# Q73 stage-1 report: lem-sp-tower-coordinate-adjunction

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-tower-coordinate-adjunction.json`: statement retained verbatim, seven-step proof, status split; not a Mathlib match.
- No new nodes, no Mathlib leaves.
- `citations.json`: 24 entries, one per step/node citation, copied verbatim from the current node statements.
- `searches.jsonl`: actual search-command log; the item also retains all inherited search records and adds the seven searches run by Q73.

## Attachments

None. Searches of the project `lean/WeilConjectures/` for the exact blueprint tag, tower/coordinate adjunction, and relevant SixFunctors terminology found no declaration proving this strict varying-coefficient derived-tower assertion. The finite-coefficient smooth-duality files, including `SixFunctors/Etale/Derived/SmoothDuality/BaseChangeCharts.lean`, do not give it. No compiler or Lake command was run.

## WANTED

None. The current blueprint and the supporting Stacks texts are present locally.

## Audit findings and changes

The sandbox initially contained only dispatcher marker files, with no earlier proof, report or searches to recover. I copied the live unsplit item and retained its statement, statement dependencies, provenance, and inherited searches. The chapter/unit route is unchanged. This item is a local chart component, not the unit's key statement, so no unit realization field is edited.

The newest blueprint read was `literature/blueprint/latest/`, at the main-20261024 snapshot recorded in COMMITS.txt. Its Local pairs paragraph still follows projective line, open restriction, ordered affine coordinates, then etale summation. Its Levels paragraph is used only for the local chart constructions; this delivery does not take responsibility for the separate gluing argument.

One citation-scope issue was corrected during self-review: `lem-pur-finite-kummer-level` invokes the global finite-field conventions through `def-pur-conventions`, whereas this item allows any field of positive characteristic. I therefore do not invoke that theorem in the proof. The already existing `lem-amb-tate-root-projection-reduction` states the prescribed finite-twist/root identification on every scheme with ell invertible and supplies exactly the formula needed here, including its actual pullback comparison. The statement's mention of the finite Kummer identification and its exponent en is retained: the asserted identification is true by that general-scheme result. The arithmetic substitution is (en)/e=n. No mathematical statement is weakened or changed.

The initially considered direct use of the pro-etale roots inverse-image isomorphism lemma was also rejected: its isomorphism clause only covers scheme isomorphisms. Instead Step 3 uses `lem-amb-finite-root-site-comparison`, whose statement explicitly says that the root-tensor pullback for any scheme morphism is invertible. This is why the actual quoted statements matter.

The adjunction-composition formulas are already defined by `def-weil-pbc-composite-adjunction`. They require no new node. Mathlib's `CategoryTheory.Adjunction.comp`, `comp_unit_app`, `comp_counit_app` and `comp_homEquiv` were read in `Mathlib/CategoryTheory/Adjunction/Basic.lean`, lines 567, 575, 580 and 584; they formalize the same generic construction, not the geometric tower assertion. The first Loogle request reported overload and is recorded as unavailable, despite its wrapper saying OK with zero hits. A second Loogle query succeeded. Both semantic phrasings were read, and neither gave the geometric result.

## Not duplicates

No new node is created. Whole-DAG searches for the coordinate adjunction, root pullback, roots/twists, and `CategoryTheory.Adjunction.comp`/Stacks 0DV0, together with `tools/blueprint_refs.py search` for tower-coordinate adjunction, coordinate, Tate, root-tower and tower-gluing, supplied the existing tools reused here. The broader `det-sp-tower-gluing` is the blueprint ancestor and depends on this chart component; it cannot be used as a proof dependency. Finite affine-space adjunctions do not state an ordinary derived strict-tower result. `blueprint.same_as` remains the searched empty list.

## Review by Q73

I read the item, the sec-smooth-purity chapter, the sk-prop-sp-tower-geometric unit record and its current blueprint statement, and the entire current `sk-prop-sp-tower-geometric-gluing.proof.md`. The proof realizes its Local pairs paragraph rather than invoking purity or an ambient exceptional adjoint. I also read Stacks 03EL (`sites-modules.tex`, lemma-tensor-product-pullback), 0GLZ (`proetale.tex`, lemma-describe-pullback-from-etale), and 0DV0 (`categories.tex`, lemma-compose-counits), checking the tags against tags/tags. No SGA source is used. This is an agent-written expansion of the blueprint, and proof_origin says so.

For Step 1 I read the full statements of `lem-sp-tower-chart-admissibility` and `det-sp-tower-p1-adjunction`. The former supplies common bounds, bounded-below objects, separate etale-origin witnesses, and preservation by intermediate chart operations; the latter is an adjunction on that bounded-below etale-origin-level domain and restricts to the desired full subcategories in the stated field setting. The proof does not assume compatible witnesses or normalized towers.

For Step 2 I checked `lem-sp-coefficient-tower-shriek-calculus` clauses (1) and (2): they give the specific compact-support comparison, open extension and its derived adjunction, not just a definition of shriek. The projective-line node gives the actual unit, counit, finite evaluation, and Hom adjunction. The generic composite-adjunction definition specifies the two Hom bijections and both structure maps. Their order gives exactly the displayed affine-line bijections.

For Step 3 I read the complete statements of `lem-amb-tate-root-projection-reduction`, `lem-amb-finite-root-site-comparison`, and `lem-asd-finite-etale-twist-line`, in addition to chart admissibility. All scheme hypotheses hold because ell is invertible; the finite ring is A_n and the root exponent is ell^n, which kills A_n. The first comparison is defined on the prescribed finite twist, with an explicit projection formula and pullback square. The second explicitly proves invertibility for arbitrary scheme maps. The third gives etale local rank-one freeness and flatness; the site comparison carries the trivializing covers to pro-etale covers. I replaced the two insufficient citations described above before delivery.

For Step 4 I read both `lem-amb-root-tower-finite-tensor` and the root-projection reduction statement. Their inverse is defined using local compatible-root lifts and is independent of them, so the tensor calculation is legitimate. I checked the strict tower morphism equation in `sk-def-sp-coefficient-towers`, the positive tensor-power twist definition in `def-coefficient-twists-detailed`, the general ringed-topos derived-tensor pullback theorem, and the inverse-system ringed-topos and levelwise-kernel description in `det-sp-coefficient-towers-abelian`. The equality p_(n+1)(x)^ell=p_n(x) makes pullback and quotient commute before localization. Rank-one freeness gives exact termwise line tensor, and the reassociator commutes with the same transitions. No equality of arbitrary derived maps is inferred from their evaluations.

For Step 5 the induction starts at the identity functor, including identity unit and counit. The inductive Hom computation uses only the preceding affine-line construction, the stated compact-support composition isomorphism in the calculus node, and the explicitly defined composite adjunction. All intermediate domains were checked in Step 1. Ordinary inverse-image composition and reassociation have been described on sections/complexes, hence are actual tower maps; no independent derived identification is left unstated. The iteration retains the ordered coordinates rather than invoking a global smooth-purity result.

For Step 6 the calculus statement supplies the etale adjunction and says its counit is finite fibre summation. The composite-adjunction formula gives epsilon_p after F_p(epsilon_e), and the inverse of the specifically oriented alpha transports its source from F_h. I checked the arguments and the direction of alpha: alpha is F_p F_e to F_h, so the transported counit must precompose with alpha inverse. Units and counits come from identities under these Hom bijections, and thus satisfy the triangle identities already in the ordinary tower category.

For Step 7 I checked the exact evaluation assertion in `det-sp-coefficient-towers-abelian`, the actual operation/evaluation comparisons of `det-sp-tower-shriek-levels`, the finite evaluation clauses in the projective-line and shriek-calculus nodes, and the identity/composition formulas in the composite-adjunction definition. Applying evaluation to these already constructed maps gives precisely the finite transposes and structure maps. This does not assert that every finite object or arrow lifts, that evaluations are faithful, or that a bijection of tower Hom groups is an identification of finite Hom groups.

I tested d=0 (identity projection and etale summation), d=1 with e the identity (open restriction of the projective-line adjunction), d=2 (two ordered integrations with twist (2)[4]), empty U (zero Hom groups), zero complexes, n=1, and ramified E of index e>1 (uniformizer exponent en and root exponent n). No normalization hypothesis is used in any case. I checked delivery-errors B through E: no new statement-only objects, elementary or duplicate nodes are introduced; all non-elementary facts are stated by the cited nodes; all quotes are literal statement substrings; no proof dependency is the parent; and all seven steps are below 2000 characters. The root comparison is written explicitly rather than hidden behind “transport” or a levelwise-equality assertion.

The off-unit theorem citations declared in split_report.tool_uses are generic coefficient/root/tensor or exact evaluation tools. The unit already chooses the projective-line/open/etale route, and these tools supply its actual twist and evaluation infrastructure without replacing that route.

## Unfinished work

None for this one-level split. Existing cited nodes remain their owners' work. The required server dry run and push are performed after this report is written; their printed result is the delivery record.
