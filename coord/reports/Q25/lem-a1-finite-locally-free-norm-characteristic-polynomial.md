## Worker report

Module: `Sheaf.RingTheory.FiniteLocallyFreeNormCharacteristicPolynomial`.
Main declaration: `Algebra.finiteLocallyFree_norm_characteristicPolynomial`.
The only postponed proof is this theorem, with all ten DAG proof steps and their
prerequisites reproduced in its docstring. The node's statement and dependencies
are unchanged. No statement dispute, new node, or dependency repair is needed.

The module defines the local determinant characterization as a real Prop-valued
predicate, states unique existence of the two norms together with the polynomial
claims, and defines the canonical norm and its polynomial by choosing these
uniquely specified functions. This uses the allowed unique-object construction:
for each norm the theorem asserts uniqueness from the local determinant predicate
alone, independently of the polynomial conclusions. There is no choice from a
mere existence statement with undetermined data, no data `sorry`, and no global
basis is chosen. The predicate and the two canonical constructions belong to the
notion explicitly introduced by this node and are listed in `lean.declarations`.

Hypothesis and clause correspondence:

- Commutative rings A and B: `{A B : Type u} [CommRing A] [CommRing B]`.
  A common arbitrary universe contains every pair of rings, including by
  cumulativity rings originally in different universes.
- Unital ring homomorphism φ: `(φ : A →+* B)`. The helper predicate equips B with
  precisely `φ.toAlgebra`, inside the definition, so no additional algebra or
  scalar-action hypothesis is imposed.
- The affine morphism is exactly `Spec.map (CommRingCat.ofHom φ)` using the
  recorded `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- Finite locally free of degree r ≥ 0: `(r : ℕ)` and `h : (...).IsFiniteLocallyFreeOfDegree r`.
  The recorded upstream class extends finiteness, flatness and local finite
  presentation and asserts `fiberDegree_eq` at every point. Its signature and
  docstring were read in FiberDegree.lean, including through `scompile.py --source`.
- The coefficient extension φ[T] is `Polynomial.mapRingHom φ`. The theorem's
  first conjunct says its affine spectrum morphism is finite locally free of
  the same degree r.
- Nφ: the existential function `N : B → A`, its
  `IsLocallyFreeDeterminantNorm φ N`, and uniqueness against every other function
  with this characterization. `finiteLocallyFreeDeterminantNorm φ r h` selects
  precisely this uniquely determined function.
- The canonical determinant norm of φ[T]: the existential `Npoly`, the same
  predicate for `Polynomial.mapRingHom φ`, and its separate uniqueness assertion.
  The chosen norm for the polynomial extension therefore agrees with Npoly.
- Local determinant characterization: for every principal localization A_a,
  every finite rank n, every basis e of A_a tensor_A B, and every b, the
  image of N(b) equals the determinant of the matrix of the scalar-extended
  multiplication endomorphism. The map is `Algebra.lmul A B b`, then
  `.baseChange (Localization.Away a)`, then `LinearMap.toMatrix e e`, then `.det`.
  This is the matrix definition in `def-weil-endomorphism-determinant`, related
  to its recorded `LinearMap.det` by `LinearMap.det_toMatrix`. All bases on all
  principal free charts are quantified, so the characterization is independent
  of local bases. Principal opens form a basis, so this determines the norm on
  every local finite free chart, including arbitrary affine free charts.
- P_b(T): `Npoly (Polynomial.X - Polynomial.C b)`.
  `finiteLocallyFreeNormPolynomial φ r h b` constructs exactly this expression
  using the uniquely determined norm for the polynomial extension.
- Form T^r + sum_{j<r} a_j T^j: `∃ a : Fin r → A, ... = Polynomial.X ^ r +
  ∑ j : Fin r, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)`.
- Annihilation: `(Polynomial.map φ (Npoly (Polynomial.X - Polynomial.C b))).eval b = 0`.
  This is coefficient extension followed by evaluation in B, exactly as stated.
- Monicity and degree when A ≠ 0: `Nontrivial A → ... .Monic ∧ ... .natDegree = r`.
  The explicit expansion and annihilation have no such hypothesis.
- No global freeness, Noetherianity, faithfulness, or positivity of r is assumed.

Dependency declarations used in the statement:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` (and its parent class).
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, its constructors and coefficient map;
  evaluation is imported from `Mathlib.Algebra.Polynomial.Eval.Defs` and monicity
  from `Mathlib.Algebra.Polynomial.Monic`.
- `Mathlib.LinearAlgebra.Determinant`: the finite-basis determinant notion recorded
  as `LinearMap.det`; its matrix expression is the right-hand side of the predicate.

All available proof-dependency modules are imported without `public`. These include
`Sheaf.AlgebraicGeometry.PushforwardRankOnOpen`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
`WeilConjectures.Algebra.CharpolyLocallyFree`,
`WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange`,
`Sheaf.RingTheory.CoverModuleExact`, and the relevant Mathlib flat-rank, pullback,
properness, finite-presentation, localization/base-change, free characteristic
polynomial and Cayley-Hamilton modules (some through existing public imports).
The norm predicate uses Mathlib's tensor product, localization, multiplication
endomorphism and matrix determinant; it does not duplicate those definitions.

Edge cases checked mathematically before drafting:

- A is the zero ring: unitality forces B to be zero. Norm functions are unique;
  principal spectra are empty; the displayed polynomial form and annihilation
  remain valid. Monicity and degree are asserted only under `Nontrivial A`.
- r = 0 with A nonzero: the degree-zero finite locally free algebra is B = 0.
  The determinant of the empty matrix is 1; `Fin 0` gives an empty sum; P_b = 1
  evaluates to zero in B. No `Nontrivial B` hypothesis excludes this case.
- Empty principal opens, including localization at zero: basis quantification
  still makes sense in the zero ring and the determinant identity is automatic.
- Nonfree projective algebras: the predicate uses only local bases, with no
  `Module.Free A B` hypothesis and no global-basis fallback.
- Non-Noetherian rings and nonfaithful structural maps: no such assumptions
  appear in any binder. Characteristic is unrestricted.

Searches for an existing statement or norm construction:

- `msearch.py ... leanfinder "The determinant norm of T minus b in a finite locally
  free algebra is a monic characteristic polynomial annihilating b"`: eight hits,
  including `LinearMap.eval_charpoly`, `LinearMap.charpoly_monic`,
  `charpoly_leftMulMatrix` and `LinearMap.exists_monic_and_aeval_eq_zero`.
  These cover free modules or unprescribed annihilators, not this statement.
- `msearch.py ... loogle "Algebra.norm, LinearMap.charpoly, LinearMap.det"`: zero hits.
- `msearch.py ... leansearch "finite locally free algebra determinant norm
  characteristic polynomial"`: eight hits, including `Matrix.charpoly`,
  `LinearMap.charpoly`, `LinearMap.det_restrictScalars` and
  `LinearMap.det_eq_sign_charpoly_coeff`. None states this theorem for locally
  free algebras without global freeness.
- `msearch.py ... grep "def norm|norm_X_sub|charpoly" RingTheory/Norm`: six hits,
  identifying `Algebra.norm` in Norm/Defs.lean and free-module norm lemmas.
  Read Norm/Defs.lean and LinearAlgebra/Determinant.lean: `Algebra.norm` uses
  `LinearMap.det`, which returns 1 if there is no finite global basis. Hence it
  is not the norm required here for a nonfree finite locally free algebra.
- `rg` over the project and upstream RingTheory/Algebra/LinearAlgebra directories
  for `charpoly`, `Charpoly`, and determinant-norm names found the existing
  locally free characteristic-polynomial construction and the norm-chart
  existence theorem. Read `Sheaf.Algebra.LocallyFreeCharpoly`,
  `Sheaf.Algebra.CharpolyLocallyFree`, and
  `Sheaf.AlgebraicGeometry.FiniteLocallyFreeNormCharts`: the former takes a
  specified local cover, and the latter provides local section norms without
  this polynomial or degree/annihilation statement. No duplicate theorem found.
- `rg` over DAG nodes and `lean/Sheaf` for determinant-norm spellings found
  `lem-pd-finite-locally-free-norm-charts`, not a preexisting canonical ring-norm
  definition. The local characterization is an owning-node helper for the norm
  introduced explicitly in the item's own statement.
- Searched the exact item id throughout upstream WeilConjectures: no hit.
  Searched all four chosen declaration names in Mathlib, upstream, `lean/Sheaf`
  and `dag/lean_names_upstream.json`: no preexisting declarations.

Sources opened: local Stacks `exercises.tex`, Exercises `exercise-trace-det`
(02DU) and `exercise-trace-det-rings` (02DV), and `algebra.tex`,
`lemma-charpoly` (00DX), and the second proof paragraph of `groupoids.tex`,
`lemma-integral-over-invariants`. These explicitly construct determinants/norms for finite
locally free modules and give arbitrary-ring Cayley-Hamilton. The node's ten-step
proof gives the gluing route used by the theorem docstring. No source-based
correction is required.

Validation: the initial theorem and local-characterization definition compiled
cleanly through the prescribed `scompile.py`; the final file, including the two
canonical definitions, is also checked through that wrapper and by `deliver2.py`.

## Second reading by Q25

Independent maintainer second reading, 2026-10-18, of immutable delivery
67c97c2145194dec5cbefff9463ea3e45d503585. The reviewer did not write this delivery.
This section replaces the delivered placeholder; it records the maintainer's reading,
not a claimed earlier review by a Q25 worker.

Read the item, all four statement-dependency JSON records, the complete delivered
module and its four declaration docstrings, and the worker report. Read local Stacks
exercises.tex:1587–1627 (02DU, exercise-trace-det; 02DV,
exercise-trace-det-rings), algebra.tex:2810–2831 (00DX, lemma-charpoly), and
groupoids.tex:4326–4366 (lemma-integral-over-invariants). The exercise constructs
finite locally free determinants and algebra norms and gives scalar-extension
compatibility. The groupoid proof uses precisely the norm polynomial and its
Cayley–Hamilton annihilation. No field or Noetherian hypothesis is inherited here.

Clause-by-clause reading:

- Objects and scalars: `{A B : Type u} [CommRing A] [CommRing B]` and
  `φ : A →+* B` give arbitrary commutative rings and the specified unital map.
  The predicate installs exactly `φ.toAlgebra`, so there is no unrelated scalar
  action. The common arbitrary universe can contain any two ring types by
  cumulativity, using the maximum of their original universes. No size case is lost.
- Affine morphism and degree: the hypothesis uses the recorded `Spec.map` of
  `CommRingCat.ofHom φ`. Read Spec and Spec.map in Mathlib Scheme.lean:470–480.
  Read the actual FiberDegree definitions in both source checkouts: the class
  extends finite, flat and locally of finite presentation; its degree clause is
  the finrank of the global sections of the scheme-theoretic residue-field fibre.
  Thus it is the node's definition, without reducedness, etaleness or faithfulness.
  `r : ℕ` includes zero.
- Polynomial base change: the first conjunct applies the same degree predicate
  to `Polynomial.mapRingHom φ`. Read Eval/Defs.lean:534–542: this homomorphism's
  underlying function is exactly coefficientwise `Polynomial.map φ`.
- Canonical norms: the two function existentials have separate uniqueness
  assertions against every function satisfying the determinant predicate alone.
  This is stronger than merely selecting a polynomial with desired properties
  and exactly expresses the canonical local characterization in the node.
- Local matrices: the predicate quantifies over all `a : A`, all finite sizes,
  and all bases of `Localization.Away a ⊗[A] B`. Read `Algebra.lmul` in
  Algebra/Bilinear.lean:143, `LinearMap.baseChange` in TensorProduct/Tower.lean:661,
  and `LinearMap.toMatrix` in Matrix/ToLin.lean:584. These compute multiplication
  by b after the specified scalar extension, then its matrix determinant.
  Determinant.lean:212 (`LinearMap.det_toMatrix`) identifies this with the
  dependency's endomorphism determinant, and its basis invariance gives the
  required independence. Principal opens form a basis; equality there also
  characterizes the norm on any affine free chart. The quantification over all
  finite sizes handles the zero localization without assuming invariant rank there.
- Polynomial and expansion: `Npoly (X - C b)` is exactly the specified P_b.
  `∃ a : Fin r → A` and the displayed sum give all and only coefficients below r.
  Coefficients may depend on b, as required.
- Annihilation: `Polynomial.map φ ... |>.eval b = 0` first maps the coefficients
  and then evaluates in B. No injectivity of φ is assumed.
- Monicity and degree: only these conclusions require `Nontrivial A`; `Monic`
  and `natDegree = r` have their usual meanings (Degree/Defs.lean:48–61).
  The unconditional expansion already says all higher coefficients vanish.
- Actual constructions: `finiteLocallyFreeDeterminantNorm` chooses a uniquely
  characterized function from the theorem; `finiteLocallyFreeNormPolynomial`
  applies that canonical construction to the polynomial extension. Uniqueness
  identifies it with the theorem's Npoly. These are permitted unique-object
  constructions, with no data sorry or unconstrained map.

Edge cases: A zero forces B zero by unitality; both polynomial rings then have
one element, so the expansion and evaluation hold for every r. For nonzero A and
r=0, local rank-zero algebras force B=0; the empty determinant and polynomial are
1_A, evaluating to zero in B. `Fin 0` supplies the empty sum. Localization at zero
is harmless. Nonfree finite projective algebras, nilpotents, nonfaithful maps,
arbitrary characteristic and non-Noetherian rings are retained. No global
`Module.Free`, `Nontrivial B`, or positivity assumption appears.

The proof docstring preserves all ten node steps: zero base; rank-r sheaf charts;
finite principal refinement and section localizations; polynomial base change;
constant polynomial bases; locally free characteristic polynomials; signed
constant-coefficient norm and uniqueness; the XI-M multiplication matrix and
coefficient descent; Cayley–Hamilton evaluated at 1; module-cover injectivity.
The two elementary steps are the zero-ring argument and finite coefficient
common-denominator/basis calculation. The determinant sign calculation includes
r=0. Read the existing locally free characteristic-polynomial interface and
coverModuleExact injectivity; they supply the two gluing operations used here.
All proof dependencies remain in the record; no prerequisite was replaced by
an arbitrary map or a stronger hypothesis.

Independent duplicate searches: LeanSearch query “norm polynomial for a finite
projective commutative algebra satisfies Cayley Hamilton” returned eight hits,
including free LinearMap/Matrix characteristic polynomials and Algebra.norm.
Loogle `Algebra.norm` returned twelve hits including norm_eq_one_of_not_exists_basis.
Read Norm/Defs.lean:61–84 and Determinant.lean:179–183: the existing norm uses a
finite global basis, returning 1 otherwise, so it does not define this locally
free norm. Grep of Mathlib, upstream WeilConjectures and project lean/Sheaf for
the four declaration names and norm_X_sub found no prior declaration. Also read
Sheaf.Algebra.LocallyFreeCharpoly, Sheaf.Algebra.CharpolyLocallyFree and
Sheaf.AlgebraicGeometry.FiniteLocallyFreeNormCharts: these supply cover-dependent
characteristic polynomials or local section norms, not the present canonical
ring norm and its polynomial theorem. No duplicate or missing helper was found.

Mechanical and pilot checks: the sole theorem proof is `by sorry`; the three
definitions contain real expressions and no sorry. All four declarations and
the module have source-place and blueprint docstrings. No line exceeds 100
characters; all variables and universes are bound. The record lists all four
declarations, and its statement field equals the main signature verbatim.
The delivery changes only the item's lean record and adds its module and report.
There is no statement correction, new node, dependency repair or citer audit needed.
The route-pivot dropped-list intersection with statement/proof dependencies is
empty, and there is no item repair note at the inspected shared ref. No dropped
machinery or pro-etale substitute occurs.

Compilation reproduced against the immutable module with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q25
lem-a1-finite-locally-free-norm-characteristic-polynomial
snapshot/lean/Sheaf/RingTheory/FiniteLocallyFreeNormCharacteristicPolynomial.lean`.
Exit 0, no errors or warnings: sandbox 3.7 s, library module 2.8 s, each under
60 seconds. The installed wrapper currently runs the private overlay on the
server and confirms the library file there; this is the actual tool behavior,
not a claim of a separate local run. No global build, direct SSH command, live
Lean edit, delivery or Git mutation was performed by the reviewer.

Finding H11 (and the real-section requirement in H1): the original second-reading
section only said no reading had occurred. Replaced that placeholder with this
independent reading, preserving the Worker report verbatim. The mathematics,
Lean module and node record require no changes. Verdict: FIX, report only.
