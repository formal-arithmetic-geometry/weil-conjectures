# Stage 1 delivery: `lem-weil-pbc-quotient-by-power-torsion-no-torsion`

## Worker report

- Edited `dag/nodes/sec-proper-base-change/lem-weil-pbc-quotient-by-power-torsion-no-torsion.json`: four proof steps, status `split`, blueprint `same_as: []`, and split report. No new nodes.
- No Lean attachment and no WANTED source.

The statement is precisely part (1) of Stacks More on Algebra Lemma 05EB (`lemma-divide-by-torsion`, `more-algebra.tex` lines 24042-24063). Its proof says that for generators `f_j` of `I`, each `f_j x` is killed by an `I`-power, and then a common `I`-power kills `x`. Step 3 supplies the omitted monomial calculation: in total degree `N = 2 + sum n_j`, one exponent exceeds its corresponding `n_j`, so that monomial annihilates `x`. Step 2 handles the empty generating set `I=0`, for which the torsion submodule is all of `M`. The argument uses only the notions defined in the item's statement; no hidden lemma is needed.

Whole-blueprint searches for `05EB`, `I-torsion`, `power torsion quotient`, and `finite generated ideal torsion` found no blueprint node with the general finitely generated ideal statement. `lemma-nagata-power-torsion-quotient-torsionfree` states the principal-ideal special case, so it is not `same_as` and is not used in the proof. The item supplies torsion control in the formal-glueing path descended from step 7 of `thm-weil-pbc-finite-etale-lifting`.

`python3 tools/review_split.py lem-weil-pbc-quotient-by-power-torsion-no-torsion` passes with zero new nodes. `python3 tools/check_dag.py` reports zero cycles and eight unrelated reachability warnings. JSON parses. No build, commit, or push was run.

## Review by H1

I read More on Algebra 05EB(1) in `more-algebra.tex` and checked its finitely generated ideal hypothesis against the unchanged item statement. Step 1 identifies the quotient kernel, step 2 chooses annihilating powers for the finitely many generators, step 3 proves explicitly why one common power kills the class, and step 4 concludes. These steps use only the ideal and torsion definitions written in the item, so their empty `uses` lists are appropriate for this elementary calculation. For $I=0$, step 2 correctly makes the torsion submodule all of $M$; for one generator, the monomial bound specializes to the evident power calculation. There are no new nodes, and the Nagata blueprint result found in the search is only a principal-ideal specialization. I sent nothing back to the worker.

Source-first correction: exact sorry-free declarations carrying the blueprint marker `lemma:nagata-power-torsion-quotient-torsionfree` are `Submodule.powTorsion_quotient_eq_bot` at `WeilConjectures/Mathlib/Algebra/Module/Torsion.lean:158-161` and `Submodule.isSMulRegular_quotient_powTorsion` at `:163-167`. The local sorry map marks both and their dependencies closed. The node is therefore attached and closed on slopmaster2; the natural-language split is superseded.
