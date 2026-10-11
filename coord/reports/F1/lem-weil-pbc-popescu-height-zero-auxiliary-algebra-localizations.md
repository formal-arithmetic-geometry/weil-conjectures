## Worker report

Module: `Sheaf.RingTheory.PopescuAuxiliaryAlgebraLocalizations`; declaration:
`Algebra.popescu_auxiliaryAlgebra_localizations`. The only proof is `sorry`.
No definitions or dependency modules are added, and the node is unchanged outside `lean`.

Hypothesis and clause correspondence:

- Arbitrary commutative ring A: `(A : Type u) [CommRing A]`, with explicitly bound universe u.
- n,m ≥ 0 and r ≥ 1: `(n m r : ℕ) (hr : 1 ≤ r)`. Fin n, Fin m, Fin r
  index the same variables as the source's one-based indexing, by relabeling.
- P and f_1,...,f_m: `f : Fin m → MvPolynomial (Fin n) A`.
- C=P/(f_j) and classes of x_k: `J := Ideal.span (Set.range f)`, `C`,
  `p := Ideal.Quotient.mkₐ A J`, and `p (X k)`.
- S=A[x,y,z,t]: the sum index `Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))`
  distinguishes every variable; `sx`, `sy`, `sz`, `st` are its variables.
- The images of f_j in S: `fs j := aeval sx (f j)`.
- B and both relation families: `I := Ideal.span (Set.range (fun j =>
  fs j - ∑ i : Fin r, sy i * st (i,j)) ∪ Set.range (fun i => sz * sy i))`,
  `B := S ⧸ I`, `q := Ideal.Quotient.mkₐ A I`.
  `bx`, `bY`, `bz`, and `bt` are precisely the quotient classes.
- T=C[t,z], with rm+1 variables: `T := MvPolynomial ((Fin r × Fin m) ⊕ Unit) C`.
  `tt` and `tz` are those variables. `Tz := Localization.Away tz` and
  `Bz := Localization.Away bz`; `iota` and `lambda` are the localization maps.
- Clause (1), well-defined A-algebra map: the existential `phi : B →ₐ[A] Tz`
  supplies an actual homomorphism from the quotient, and the next four conjuncts
  prescribe x_k ↦ iota(C(p(X k))), y_i ↦ 0, z ↦ iota(tz), t_ij ↦ iota(tt ij).
- Clause (1), induced isomorphism: `e : Bz ≃ₐ[A] Tz` with
  `∀ b : B, e (lambda b) = phi b`. This compatibility states induction from phi,
  rather than merely an unrelated isomorphism between the same rings.
- Clause (2), for every l: `∀ l : Fin r`.
- Q_l: polynomial index `Fin n ⊕ (Fin r ⊕ ({i : Fin r // i ≠ l} × Fin m))`
  retains x and all y and exactly those t rows other than l. It has no z variable.
  `qx`, `qy`, `qt` denote its variables.
- The stated Q_l → B map: `alpha := aeval ...`, with each of the three sum-index
  cases sent to the matching quotient class. The subtype's `.val` restores the original row.
- Localization at y_l: `Qy := Localization.Away (qy l)`,
  `By := Localization.Away (bY l)` and localization maps `nu`, `mu`.
- The induced isomorphism: `e : Qy ≃ₐ[A] By`, with
  `∀ a : Q, e (nu a) = mu (alpha a)`.
- Its inverse sends z to zero: `e.symm (mu bz) = 0`.
- Its inverse sends t_lj to the stated expression: the last universally quantified equation
  uses `IsLocalization.Away.invSelf (S := Qy) (qy l)` times
  `nu (aeval qx (f j) - ∑ i : {i : Fin r // i ≠ l}, qy i.val * qt (i,j))`.

The let expressions are explicit ring constructions and generator notation inside the
proposition, not new library notions or additional assumptions. Stage 3 can introduce
these local values when entering the proposition. No data is postponed with sorry.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and `MvPolynomial.algHom_ext`
  in `Mathlib.Algebra.MvPolynomial.Basic`, and `MvPolynomial.aeval` in
  `Mathlib.Algebra.MvPolynomial.Eval` (the latter is imported explicitly).
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom`, `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ` in `Mathlib.RingTheory.Ideal.Quotient.Operations` and
  `Ideal.span` from Mathlib's ideal API. This dependency has a mathlib_match and needs no repair.
- `def-weil-ring-localization-away`: `Localization.Away`, read in
  `Mathlib.GroupTheory.MonoidLocalization.Away`, and `IsLocalization.Away` and
  `IsLocalization.Away.invSelf` in `Mathlib.RingTheory.Localization.Away.Basic`.
  `Mathlib.RingTheory.Localization.Algebra` supplies the induced A-algebra structures.

Edge cases checked before writing: n=0 leaves a coefficient-ring polynomial presentation;
m=0 makes the first relation family and all t variables empty; r=1 makes Q_l's t index
empty and the inverse's sum zero; zero base ring and a unit among the f_j give possibly
zero quotients/localizations, which are permitted without Nontrivial assumptions.
No field, Noetherian, smoothness, or characteristic assumption is used in these elementary
isomorphisms. The bound r≥1 is retained exactly, although the first clause also makes sense
for r=0. All rings stay in Type u, allowing arbitrary ring universes.

Source checked at https://stacks.math.columbia.edu/tag/07FA, proof of Lemma 16.9.4.
The local literature checkout does not contain smoothing.tex. The node already records
the source's misprint C[y,z,z⁻¹]: since zy_i=0, the y_i vanish after inverting z,
and the correct surviving variables are t_ij,z as the node states. No correction is needed.
The declaration docstring carries all seven proof steps from the node, including the
universal-property, relation, and composite checks.

Searches (2026-10-11):

- msearch.py leansearch, `localization quotient auxiliary algebra z y f sum y t elimination
  polynomial variables`: service unavailable, Internal Server Error.
- msearch.py leanfinder, `localizing quotient polynomial algebra by z*y and f minus sum y*t
  at z or y eliminates variables`: eight hits for general localization presentations,
  including `Algebra.Generators.compLocalizationAwayAlgHom_relation_eq_zero` and
  `IsLocalization.Away.mvPolynomialQuotientEquiv_apply`; none states this node.
- msearch.py loogle, `IsLocalization.Away, MvPolynomial`: twelve hits, including
  `IsLocalization.Away.mvPolynomialQuotientEquiv` for R[X]/(rX-1), not these eliminations.
- msearch.py grep, `delocalize|auxiliary.*algebra|invSelf`, RingTheory: only invSelf API
  and its applications; no auxiliary-algebra statement.
- rg of `delocalize|height.zero|auxiliary.*algebra|lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations`
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's `lean/Sheaf`:
  no matches. rg of this node id and `delocalize` in `dag/lean_names_upstream.json`:
  no matches. The new declaration name is absent from those searches.

Validation: scompile.py compiled the module cleanly in 1.9 seconds. The initial parser
error from using the reserved token `by` as a variable name was repaired by naming it `bY`.
No STATEMENT-DISPUTED issue and no statement correction.


## Second reading by F1

Node list and Lean correspondence: the commutative base ring is `(A : Type u) [CommRing A]`; the natural numbers and bound are `(n m r : ℕ) (hr : 1 ≤ r)`; the input polynomials are `f : Fin m → MvPolynomial (Fin n) A`. The `let` chain introduces `S`, variables `sx`, `sy`, `sz`, `st`, the relation ideal `I`, quotient `B` and classes `bx`, `bY`, `bz`, `bt`; `J`, quotient `C` and `p`; `T`, variables `tz`, `tt`, localizations `Tz`, `Bz`, and maps `iota`, `lambda`. Clause (1) is the existential `phi : B →ₐ[A] Tz` with the four prescribed generator images and an `e : Bz ≃ₐ[A] Tz` satisfying `e (lambda b) = phi b`. Clause (2) quantifies `l : Fin r`, defines `Q`, `qx`, `qy`, `qt`, `alpha`, `Qy`, `By`, `mu`, `nu`, then gives `e : Qy ≃ₐ[A] By`, compatibility on every `a : Q`, the equation `e.symm (mu bz) = 0`, and the formula for every `j : Fin m`. Every object, hypothesis, quantifier, and conclusion clause in the node is rendered by the theorem signature. Verdict: exact.

Edge cases checked: `n = 0` and `m = 0` give the expected coefficient-ring and empty-index polynomial cases; `r = 1` leaves the omitted-row sum empty; zero rings and unit relations are allowed; no field, Noetherian, finiteness, or characteristic assumptions are added. The shared universe `u` covers all rings and polynomial constructions, and `hr` preserves the source condition `r ≥ 1`.

Searches: LeanSearch was attempted through `msearch.py` (service returned Internal Server Error); LeanFinder and Loogle searches for polynomial quotient/localization elimination found only general presentation APIs; grep searches in Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no matching notion or theorem. The source checkout has no smoothing.tex; the node source is Stacks Tag 07FA, Lemma 16.9.4 proof.

Mismatches: none. The worker module already used the corrected Stacks reading in which the surviving variables after inverting `z` are `t_{ij},z` (the source's displayed `y_i` is a misprint), and it uses `bY` instead of the reserved token `by`. No statement correction, dependency module, or new node was needed. The module compiled cleanly with `scompile.py`; the node's `lean.statement` is the theorem signature verbatim.
