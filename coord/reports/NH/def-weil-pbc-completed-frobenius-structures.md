# Stage-1 report

## Files written

- `dag/nodes/sec-proper-base-change/def-weil-pbc-completed-frobenius-structures.json`: definition, split; the statement is unchanged. Added six existing statement dependencies and retained the completed-base-change-map dependency. Mathlib has the generic operations on isomorphisms, but not this completed construction.
- `citations.json`: empty list, because a definition has no proof steps.

No new nodes or Mathlib leaves. No unit or chapter record changed. The item is not the unit's key statement.

## Attachments

None. Searched all project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the blueprint id and by completed Frobenius/Weil and transport notation. The available Frobenius material is not a declaration of these completed source and target structures together with the specified comparison maps and ordered composite. The upstream master search gave no exact declaration either; that checkout was reference material only, never attachment evidence.

## Wanted literature

None. The item's source and the supporting completion source are available locally.

## Corrections and scope

The imported definition named only the completed-base-change map. That node supplies neither the Frobenius functor nor the limit Weil structures. Added the existing Frobenius tower datum, finite-corner definitions, completed-pullback and adic-limit definitions, direct-image/limit theorem, and product-cone Frobenius theorem. No statement, hypothesis, coefficient category or formula was changed. In particular the maps retain type from Frobenius pullback to the object; they are not treated as endomorphisms.

Blueprint searches: `Theta_S`, `completed Frobenius`, `frobenius`, `pullback/tensor`, and `Theta_{Z,`. The only other `Theta_S` result is the downstream equivariance theorem, which does not define these structures and was not cited. The finite-corner structures have different objects; the product-cone theorem supplies the structures used as inputs here. No other blueprint node states the same definition, so `same_as` is empty. DAG searches by the limit objects, Weil structures, reconstruction and direct-image/limit terminology led to the reused nodes. No duplicate is introduced.

Mathlib searches ran through the prescribed msearch command, including a second semantic phrasing for generic endofunctor transport. The second phrasing returned `CategoryTheory.Functor.mapIso`; Loogle returned `mapIso_trans` and related natural-isomorphism operations. Read `Mathlib/CategoryTheory/Iso.lean`: `Iso.symm` at line 87, `Iso.trans` at line 131, `Functor.mapIso` at line 473, and `mapIso_trans` at line 484. These explain elementary transport, but none specifies S, T, s, t or the completed exchange map. LeanSearch returned HTTP Internal Server Error and is recorded as unavailable. Grep for the completed construction had no hits. The generic CategoryTheory grep returned ordinary isomorphism operations, not a match for the item.

## Unfinished work

None at this split level. Existing dependencies remain their own items. No Lean was written or compiled; no push is requested.

## Review by NH

I read the master blueprint definition at order 1339, its chapter and unit records, and the full statements of every added dependency. I also read the blueprint product-cone Frobenius lemma at order 1337 and Stacks `proetale.tex`, label `lemma-pushforward-Noetherian-case` (Tag 099N), and `theorem-proper-base-change` (Tag 09C9). Stacks supplies completion and direct-image comparisons, not a definition of these Frobenius structures. The source for the latter is the blueprint, and I do not attribute the extra Frobenius assertion to Stacks.

There are no numbered theorem proof steps: this is a definition. Its inputs are explicit existing objects and comparisons, not data selected from an undetermined existence theorem. `def-weil-pbc-frobenius-tower-datum` states that the Frobenius maps are automorphisms and defines the resulting equivalence Phi. `def-weil-pbc-level-map-corners` states A_n and D_n. `def-weil-pbc-adic-derived-inverse-limit` defines their limits. Most decisively, `lemma-weil-pbc-frobenius-product-cone-limit` explicitly states the isomorphisms Theta_(Z,infinity) and the common map W := V'H = H'V; I use its statement, not constructions hidden in its proof.

For s, `def-weil-pbc-completed-pullback` computes completed pullback as the derived limit of the levelwise reduction pullback; the formula for A_n identifies that limit with A_infinity. `prop-weil-pbc-direct-image-limits` supplies completeness of Rf_*K, so this application has the required complete input. For t, the same proposition states the canonical comparison Rf'_* Rlim E_n to Rlim Rf'_* E_n is an isomorphism. Its inverse has exactly the direction D_infinity to T. `def-weil-pbc-completed-base-change-map` fixes the first comparison to B_infinity and the final comparison to T; its sketch names that first comparison as H following the comparison to A_infinity. Thus substitution into the ordered composite yields t V' H s = t W s, and the equality of the two factorizations is supplied by the product-cone theorem. No separate node restating this clause is created.

I checked the transport types directly: Phi(S) maps by Phi(s) to Phi(A_infinity), then by Theta_A to A_infinity, then by s inverse to S. Its inverse is Phi(s inverse) Theta_A inverse s. Likewise Phi(T) maps by Phi(t inverse) to Phi(D_infinity), then by Theta_D to D_infinity, then by t to T; its inverse is Phi(t) Theta_D inverse t inverse. The inverse identities use only functoriality and cancellation. There is no hidden compatibility theorem in the word transport. Completed equivariance itself belongs to the downstream node and is not claimed proved here.

The hypotheses remain those of the proper Cartesian square, derived-complete coefficient datum and compatible Weil tower: the Noetherian coefficient ring, torsion quotient and perfect finite quotients are inherited from the existing construction. No change from pro-etale complexes to condensed coefficient objects is made. Identity comparisons give Theta_S = Theta_A and Theta_T = Theta_D; identity Frobenius gives ordinary conjugation. The zero complex also has correctly typed unique isomorphisms. For nonidentity Frobenius, Phi(s) and Phi(t inverse) are necessary and retained. These checks address the wrong-object and hidden-hypothesis failures in section E. Sections B–D introduce no new-node issues or relabelling: the actual formulas are retained, their missing inputs are cited, and no downstream equivariance dependency creates a cycle.

## Dry-run tool failure

The required `deliver.py NH def-weil-pbc-completed-frobenius-structures --no-push` completed with one preflight failure. The split review passed. The only failure printed the global check_dag summary with 32 cycles (178 nodes), rather than a new finding. In `tools/preflight_delivery.py`, lines 520–540 subtract base findings, but line 542 additionally rejects when `"0 cycles"` is absent from the summary. This makes any pre-existing global cycle count fatal even when the delivery introduces no findings. A read-only dependency traversal of all seven proposed dependencies found no path back to the item. I did not edit the tool, discard required dependencies to bypass it, or push. This requires a maintainer tool repair; the sandbox is prepared but has not received OK.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against the blueprint node at order 1339 and its source file; both displayed transport formulas, object definitions, and the ordered composite agree exactly, with no hypothesis or clause changed.
- Proof steps: none; this is a definition, so there are no proof dependencies or elementary steps to audit.
- `def-weil-pbc-completed-base-change-map`: checked its ordered composite and comparison directions; it supplies the completed exchange map used by the definition.
- `def-weil-pbc-frobenius-tower-datum`: checked the Frobenius automorphisms, pullback exchanges, and finite-level Weil data; it supplies the functors and tower datum used in the formulas.
- `def-weil-pbc-level-map-corners`: checked the four finite-level corners and the Cartesian pullback identification; it supplies the corner objects underlying the limits.
- `def-weil-pbc-completed-pullback`: checked its tower-level derived-limit definition and pullback type; it supplies the meaning of the completed source object.
- `def-weil-pbc-adic-derived-inverse-limit`: checked the cone model and functorial tower maps; it supplies the inverse-limit objects and comparison maps.
- `prop-weil-pbc-direct-image-limits`: checked the direct-image/limit isomorphism and completeness clauses; it supplies the target comparison and its direction.
- `lemma-weil-pbc-frobenius-product-cone-limit`: checked the limit Weil structures and equality `W=V'H=H'V`; it supplies the common equivariant map used by the composite.
- Small cases: zero complexes give the unique typed isomorphisms; identity Frobenius reduces the formulas to ordinary conjugation; identity comparisons give the expected finite-corner structures. The displayed maps remain correctly typed for nonidentity Frobenius.
- Changes: no node or statement changed. Added this second-reading record only; no new node or Mathlib leaf exists, and `citations.json` correctly remains empty.

## Second reading by NH

- Item statement: reread the blueprint node at order 1339 and the imported JSON hypothesis by hypothesis; the definitions of $S,T$, the comparison directions $s,t$, both transported Weil structures, and the ordered composite agree exactly.
- Definition dependencies: reread each of the seven cited node statements; each supplies the object, comparison, limit, Frobenius, or common-map datum used by the displayed definition, and no proof step is claimed for this definition.
- New nodes and Mathlib leaves: there are no new nodes and no Mathlib leaves; the existing dependency nodes were searched by identifier and terminology, and the recorded generic Mathlib transport searches do not match the completed construction.
- Edge cases and hypotheses: checked the zero complex, identity Frobenius, identity comparisons, and nonidentity Frobenius types; all displayed maps remain well typed and no hypothesis is added or dropped.
- Change made: filled the required item blueprint `from` record with the self ancestor, exact blueprint places, and empty `via`; this repairs the missing B9 stage-1 metadata while preserving the statement and dependencies.
