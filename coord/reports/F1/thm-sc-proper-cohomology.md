# Worker report: thm-sc-proper-cohomology

## Files written

- `dag/nodes/sec-curve-estimates/thm-sc-proper-cohomology.json`: split the imported proof into four steps; added the missing Brauer-vanishing citation, source places, three Mathlib searches, `blueprint.same_as`, and `split_report`.
- `dag/units/sk-thm-curveestimate.json`: the item is the unit's key theorem, so `realized.statement` now names it and `realized_by` records this item. The unit's statement, uses, and route were not changed.
- This report. No new node or Lean file was written.

## Attachments and source Lean

The read-only slopmaster2 checkout at `/home/ubuntu/weil-src-slopmaster2` was searched by node id, the source declaration names, and the curve-cohomology notion in `WeilConjectures/` and `Comparator/`. No single declaration states the full four-degree item.

- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_zero` belongs to the degree-zero clause of `thm-sc-proper-cohomology`, `WeilConjectures/AlgebraicGeometry/Curve/Estimate.lean:62`; sorry-free by the committed slopmaster2 sorry map.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one` belongs to the degree-one clause, the same file at line 77; has `sorry` at line 87.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_two` belongs to the degree-two clause, the same file at line 98; has `sorry` at line 106.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le` belongs to the higher-vanishing clause of `lem-sc-cohomological-dimension`, `WeilConjectures/AlgebraicGeometry/Curve/CohomologicalDimension.lean:411`; its proof text has no local `sorry` but the committed map records reachable `sorry`. These are partial clauses, not an attachment that closes the full item.

## WANTED

None. The Stacks source was read in the available local checkout `/tmp/stacks-project/etale-cohomology.tex`; it is not stored in this git worktree, and its established repository literature path is `literature/stacks-project/etale-cohomology.tex`.

## Source and blueprint comparison

Stacks Etale Cohomology Lemma Tag 03RQ, label `lemma-cohomology-smooth-projective-curve`, is at `etale-cohomology.tex:11135`. Its displayed result gives the three cohomology groups and vanishing above degree two. Its proof at lines 11165-11215 uses the Kummer sequence, Brauer vanishing, the degree sequence for the Picard group, and Jacobian torsion. Stacks states the lemma for smooth projective curves; the blueprint and item state it for smooth proper connected curves of dimension one. The four cited DAG statements themselves apply to smooth proper connected curves, so the same argument covers this scope without assuming projectivity. The nonempty dimension-one condition matters: `Spec k` has zero second cohomology. The primitive-root identification is noncanonical as a choice, matching Stacks' constant-sheaf clause.

The high-degree vanishing is Stacks Theorem Tag 03RT, label `theorem-vanishing-curves`, part (1), at `etale-cohomology.tex:15740`, for torsion sheaves on separated finite-type schemes of dimension at most one. Tag 03SC is the affine-curve theorem and was deliberately not cited for this clause.

`python3 tools/blueprint_refs.py search 'smooth proper connected curve'`, `search 'H^2(C'`, and a DAG-wide notion search found the item itself and related statements, but no other blueprint node stating the full proper-curve calculation; `same_as=[]`. The item is itself an imported blueprint node, so `blueprint.is` remains its id and `blueprint.from` remains null. The `split_report.blueprint` identifies the four clauses of its sole blueprint proof paragraph. No new node required an ancestor or `from.place`.

## Proof and route checks

Step 1 uses `lem-sc-primitive-root` for the choice and `def-sc-mu-trivialization` for the sheaf isomorphism; taking cohomology of that isomorphism is elementary. Step 2 uses the proper, connected, reduced specialization explicitly stated in `lem-sc-kummer-les` and cites `lem-sc-brauer-zero` for its required $H^2(C,\mathbf G_m)=0$ hypothesis. Its long exact sequence then gives $H^0$, the Picard $n$-torsion description of $H^1$, and the Picard cokernel description of $H^2$. Step 3 substitutes the two clauses of `lem-sc-pic-proper-ntorsion`; the substitution is elementary. Step 4 applies `lem-sc-cohomological-dimension` to the torsion constant sheaf on the smooth separated connected curve of `def-sc-curves`.

The first version cited `lem-sc-global-functions`, which `review_split.py` correctly rejected because it belongs to a unit outside this unit's route. I replaced it with the proper-curve unit-group clause already stated publicly by `lem-sc-kummer-les`. The remaining proof follows the unit's Kummer, Picard, and cohomological-dimension route. The unit has no numbered steps, so its `realized.steps` remains empty.

## Mathlib and B-E self-check

LeanSearch for the full smooth proper curve cohomology calculation returned only the general `CategoryTheory.Sheaf.H` definition. LeanFinder returned group cohomology and unrelated cotangent cohomology. A grep of the pinned Mathlib source for constant-sheaf cohomology and roots-of-unity names found no curve calculation. These three queries and their verdicts are recorded in the item; it is not a Mathlib leaf (B6, B8).

B1-B9: no new node was created, and all object and notion dependencies already named in the item's statement were retained. The item has single-backslash TeX in decoded JSON, its sources use the exact Stacks tags and `.tex` labels, its blueprint `same_as` is filled, and its `split_report` maps the blueprint proof. B10 is addressed by the clause-by-clause Lean search above: only degree zero is sorry-free, so the full item remains split.

C1-C8: each non-elementary input in the four steps is named by a public node, including Brauer vanishing, which the imported proof had omitted. The Kummer node states the specialization actually used; no step imports material from another node's proof. The only off-route citation found by the checker was removed, no tool use was written, and the DAG has no cycle.

D1-D5: the split does not create a child restating a degree of the theorem. It gives the route from the root-of-unity sheaf isomorphism and the Kummer exact sequence to the Picard group calculation, then derives higher vanishing separately. No source omission was hidden in a child.

E1-E7: $n$ invertible in $k$ permits the root-of-unity trivialization and Kummer exactness; algebraic closedness makes $k^\times$ $n$-divisible; smoothness gives reducedness; properness and connectedness supply the Kummer node's global-unit clause; Brauer vanishing is supplied explicitly. For $n=1$ all three displayed groups are trivial, as are the relevant torsion and cokernel groups. The dimension-one condition excludes the `Spec k` counterexample in degree two. No source error or changed statement is reported.

## Verification and unfinished work

- `python3 tools/review_split.py thm-sc-proper-cohomology`: PASS; zero new nodes; realizes `sk-thm-curveestimate`.
- `python3 tools/blueprint_refs.py check thm-sc-proper-cohomology`: zero field errors.
- `python3 tools/check_dag.py --cycles`: zero cycles and self-loops. It exits with seven pre-existing reachability warnings for unrelated proper-base-change nodes.
- No Lean file was edited or built. Lead review, delivery preflight, and push remain for F1.

## Review by F1

I read Stacks Etale Cohomology 03RQ (`lemma-cohomology-smooth-projective-curve`, `etale-cohomology.tex` lines 11135-11216) and 03RT (`theorem-vanishing-curves`, lines 15740 onward). The source writes projective whereas the blueprint item says smooth proper connected dimension-one; the public Picard, Kummer, Brauer, and cohomological-dimension nodes cited here each state the facts for that proper scope, so the argument applies with the item's exact hypotheses. The genus, invertibility of n, nonempty connected curve, three cohomology groups and higher vanishing were checked separately. No new node is introduced; the whole-blueprint search, `same_as=[]`, and partial slopmaster2 declarations were checked against B1-B10.

Step 1 uses the actual sheaf isomorphism in `def-sc-mu-trivialization` and the existence in `lem-sc-primitive-root`; cohomology transports along an isomorphism. Step 2 uses the proper connected reduced unit-group specialization explicitly in `lem-sc-kummer-les`, and `lem-sc-brauer-zero` supplies the H²(G_m)=0 hypothesis needed for the Picard cokernel formula. Step 3 substitutes both public conclusions of `lem-sc-pic-proper-ntorsion`. Step 4 applies `lem-sc-cohomological-dimension` to the torsion constant sheaf; `def-sc-curves` gives the finite-type separated dimension-one scope. These statements, rather than their hidden proofs, contain each non-elementary input (C1-C8, D1-D5).

I checked n=1, the need for invertibility in k, reducedness from smoothness, and why a zero-dimensional connected proper scheme cannot be used for the degree-two result. The source's chosen-root identification is noncanonical and the item retains that choice. The worker had an off-route global-functions citation; it was replaced with the Kummer node's public specialization, and `review_split.py` now passes. The unit record marks only this key statement realized. The DAG check has no cycle; its seven unrelated reachability warnings remain (E1-E7, A, F).
