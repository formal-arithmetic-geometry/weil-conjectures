# Worker report: lem-sp-affine-line-scalar-mates

1. Files written: `dag/nodes/sec-smooth-purity/lem-sp-affine-line-scalar-mates.json` (statement, split; not a Mathlib leaf). Supporting audit file: `citations.json`. New nodes: 0. Mathlib leaves: 0.
2. Attachments: none. Searched all `lean/WeilConjectures/` for the exact blueprint tag and the affine/scalar/coefficient/mate notions. No declaration states the whole item. General pasting declarations do not construct these normalized geometric comparisons.
3. WANTED: none.
4. Errors: no statement error, no route departure. The input was a statement-only supporting node extracted from the previous affine-counit proof. Its statement, source, chapter, unit, origin and blueprint ancestry have been retained. The proof now supplies the omitted composition calculation. The definition of the specified coefficient map is reused rather than silently identifying another compactification's map.
5. Unfinished work: none in this one-level split. The cited nodes retain their own stage-1 obligations; their proof bodies are not used here.

## Sources and route

Read GOAL.md, the contract and worker brief, stages/1-dag.md, SETUP.md including its three levels, and both copies of delivery-errors.md B–E. Read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-lem-sp-reduction.json`, and the current blueprint `main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md` in full. This item realizes the Charts paragraph's open-extension and one-projective-line integration factors, below unit step 2. It is not the unit's key statement, so no realized fields were changed.

Also read Stacks `more-etale.tex`, Tag 0GL6, label remark-Rf-lower-shriek-change-of-rings (3739 onward), `categories.tex`, Tag 0DV0, label lemma-compose-counits (3576 onward), and `sites-cohomology.tex`, Tag 07A7, label remark-base-change (4033 onward). The proof is marked agent-written: the blueprint describes these ingredients but does not contain the displayed composition calculation. The cited coefficient node, rather than Tag 0GL6 alone, specifies the actual normalized coefficient maps. No SGA source is used.

## Searches and reuse

Read all inherited Mathlib search records and retained them. Ran and read additional logged searches using the required msearch.py command: LeanFinder with two distinct geometric phrasings, Loogle for CategoryTheory.mateEquiv_hcomp, grep for the affine coefficient-counit notion, grep for mateEquiv_counit and mateEquiv_hcomp in CategoryTheory/Adjunction, and LeanSearch for the geometric coefficient-counit comparison. These records are added exactly from searches.jsonl, with their actual query and results. Services returned successfully. Hits include ordinary ModuleCat scalar extension, unrelated coalgebra counits, projective-spectrum morphisms, and generic mate pasting; none states the geometric item. Read Mathlib/CategoryTheory/Adjunction/Mates.lean at lines 123–132 and 209 onward: these are categorical ingredients, not an exact or one-line specialization proving all of this item without the open and projective-line results.

DAG and blueprint searches included the exact item tag, scalar mates, composite adjunction, standard affine-line compactification, affine-line scalar, and projective-line counit scalar. Relevant existing inputs are reused. No supporting lemma was created for a few-line naturality computation. `blueprint.same_as` remains empty; the full geometric statement has no blueprint duplicate.

## Not duplicates

No new nodes. The existing open-counit and projective-line-counit nodes give the two separate identities; neither states their affine-line composite. The generic mate-pasting and finite-tower statements do not identify the actual open/proper geometric coefficient map for this compactification.

## Review by Q20

I checked the item against the current Charts source and read the full statements of every proof citation. There are no new nodes requiring a separate source review.

Step 1 uses lem-sp-etale-ctf-chart-domain for compact support, scalar extension, pullback, twists and shifts on the stated finite-Tor category. For j choose its compactification with identity proper factor, and for q choose identity open factor. Both middle schemes are in the standing class. This makes V_A K and H_A V_A K admissible inputs. It uses lem-sp-et-proet-coefficient-compatibility specifically for the definition of the chosen compactification's coefficient map as proper comparison followed by extension-by-zero comparison, and for invertibility on this class. This is declared as a generic tool use in split_report; the smooth-purity route itself is unchanged.

Step 2 uses precisely the displayed equation in lem-sp-etale-sum-counit-scalar with e=j and input V_A K. The standard open immersion is separated etale of finite type; the rings are finite, unital and killed by the common ell-power N. Its summandwise comparison is s, its pullback comparison is h, and its counit is the stipulated v. Thus this is the normalized actual open adjunction, not an abstract adjoint identified without a counit check.

Step 3 uses precisely the displayed equation in lem-sp-p1-counit-scalar with base T. Its functors, counit, proper coefficient comparison and right comparison are Q,V,w,b,a in the item. The same field characteristic, invertibility of ell, rings and common N satisfy all its hypotheses. The Tate twist and cochain shift retain the specified normalization, with no new orientation choice.

Step 4 reads the counit formula from def-weil-pbc-composite-adjunction and substitutes the two previously proved equations. I checked all domains in the two naturality squares: a_K goes from T_P V_A K to V_B T_T K, while v goes from J_A H_A V_A K to V_A K. The resulting b component is therefore b at V_A K, exactly the one in Step 3. The only additional facts are functoriality, associativity and naturality, written explicitly. This is elementary composition of the cited identities, not an uncited geometric lemma or an appeal to a proof of another node.

Step 5 uses the transpose characterization in def-weil-pbc-adjunction-mate with left adjoints L_A,L_B, right adjoints W_A,W_B and vertical functors T_U,T_T. The direction is the inverse of b^u: L_B T_U to T_T L_A. Its transpose equation is exactly the equation after cancellation, which fixes the mate without ambiguity. The comparisons are natural, so equality of all components gives equality of natural transformations.

I checked delivery-errors B1–B10: no new node, no artificial clause node, self-contained unchanged statement, normal TeX escaping, genuine logged searches, no unsupported Mathlib attachment and filled blueprint place/same_as. For C1–C8 I matched every citation to its statement, constructed verbatim citations.json, used no proof internals, and declared the one off-unit generic comparison tool. The steps cite previously established identities by step number without adding circular dependencies. For D1–D5 the argument remains in the item: the two counit identities are composed explicitly and no hidden comparison is moved to a restatement node. For E1–E7 I checked morphism directions, all standing hypotheses and the actual functor/counit choices; there is no statement correction or disputed inference.

Small cases checked: identity A=B reduces to the unchanged composite counit; empty base and zero input give the unique zero morphisms. N=1 forces the zero coefficient rings and also yields the unique maps. Nonflat Z/4 to Z/2 with ell=2 and characteristic 3 remains valid: only finite-Tor inputs are used, all tensor operations are derived, and no claim that scalar extension preserves arbitrary D+ objects enters the calculation. Every proof step is shorter than 2000 characters and none conceals a separately quantified lemma. I preserved all original statement and metadata fields and added no Lean files or compiler actions.
