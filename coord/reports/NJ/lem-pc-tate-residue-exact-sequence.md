## Worker report

The module `Sheaf.RingTheory.TateResidueExactSequence` states
`TateResidue.admissible_and_res_eq_add_of_exact`. Its proof is exactly `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The source is Tate, *Residues of differentials on curves*, §1 (T2), p. 150,
and §2 Theorem 1 and its projection formula, pp. 151–152. I read these pages
of the local PDF, the full DAG proof, and the upstream exact-sequence proof.

Hypothesis and clause correspondence:

- A field k: `{k : Type u} [Field k]`.
- A commutative k-algebra R: `{R : Type v} [CommRing R] [Algebra k R]`.
- The three R-modules: `V₁`, `V`, and `V₃`, each with `AddCommGroup` and
  `Module R`. Each also has `Module k` and `IsScalarTower k R`, expressing
  its restricted k-vector-space structure, as required by the recorded residue
  interface. This does not require any extra mathematical structure: every
  R-module has this compatible restricted action. The five carrier universes
  are explicitly bound and independent.
- The two R-linear arrows: `(i : V₁ →ₗ[R] V) (q : V →ₗ[R] V₃)`.
- Injectivity of i: `hi : Function.Injective i`.
- Surjectivity of q: `hq : Function.Surjective q`.
- Image equal to kernel: `hex : Function.Exact i q`. This says precisely
  `q v = 0 ↔ ∃ v₁, i v₁ = v`, including the composition-zero condition.
- The k-subspace A: `A : Submodule k V`.
- Its admissibility: `hA : TateResidue.Admissible R A`.
- Admissibility of the inverse image: first conjunct
  `Admissible R (A.comap (i.restrictScalars k))`.
- Admissibility of the image: second conjunct
  `Admissible R (A.map (q.restrictScalars k))`.
- Equality of the three maps on Ω¹(R/k): final conjunct
  `res R A = res R (A.comap (i.restrictScalars k)) +
  res R (A.map (q.restrictScalars k))`.
  Each term is the canonical `KaehlerDifferential k R →ₗ[k] k`, and addition
  is pointwise addition of linear maps, not just equality on selected differentials.

Dependency declarations used and inspected:

- Statement dependency `lem-pc-tate-abstract-residue-calculus` records
  `Sheaf.RingTheory.TateAbstractResidueCalculus`,
  `TateResidue.abstract_residue_calculus`. The module is publicly imported.
  Its actual constructions are `TateResidue.Admissible` and `TateResidue.res`
  in `WeilConjectures.RingTheory.TateResidue.Residue`; I read both definitions
  and their docstrings. Admissibility expands to every multiplication image
  being `Submodule.AlmostLE` A. In `TateIdeals`, this means inclusion in
  A plus a finitely generated k-subspace, equivalent over a field to the
  quotient (rA+A)/A being finite-dimensional. The residue is the existing
  canonical linear functional, with its commutator characterization.
- Proof dependency `lem-trf-vector-subspace-complement` is a Mathlib node:
  `Submodule.exists_isCompl` in `Mathlib.LinearAlgebra.Basis.VectorSpace`.
  Its full signature gives a complement to any subspace, with no dimension bound.
- Proof dependency `lem-pc-finite-potent-trace-calculus` records
  `Module.End.finitePotent_trace_calculus` in
  `Sheaf.RingTheory.TateResidue.FinitePotentTraceCalculus`. Its stable-subspace
  clause supplies finite potency of the induced operators and trace additivity.
  The module is a non-public proof import.
- Proof dependency `def-weil-pbc-kahler-differentials` records Mathlib's
  `KaehlerDifferential`, `KaehlerDifferential.D`, and
  `KaehlerDifferential.linearMapEquivDerivation` in
  `Mathlib.RingTheory.Kaehler.Basic`; their definitions and universal-property
  signatures were inspected. The proof imports that module as recorded.

The theorem docstring carries all five DAG proof steps: finite-dimensional
subquotients for admissibility, compatible projections from complements,
restriction and quotient of the commutator, stable-subspace trace additivity
and invariance of pairs, and extension from f dg to all differentials.

Edge cases checked mathematically before writing:

- A = 0 or A = V: inherited subspaces are respectively zero or full, all
  admissible, and all residues vanish. The module has no properness assumption.
- V₁ = 0, or V₃ = 0: exactness makes the other arrow an isomorphism; additivity
  reduces to invariance of the residue plus the zero-space residue.
- All three modules zero and the zero algebra are allowed by the signatures.
- Finite-dimensional modules or finite-codimension A give the expected zero
  residues; no finite-dimensionality assumption is imposed.
- No R-linear splitting is assumed. The proof uses k-linear complements only.
- Arbitrary characteristic is allowed, including characteristic two: the sum
  is addition in k, with no division by two or characteristic assumption.
- Different universes for the field, algebra, and each module are permitted.

Searches made, with results read:

- `msearch.py`, LeanFinder: "Abstract Tate residues are additive in a short exact
  sequence of modules and admissible subspaces pull back and map forward".
  Eight hits: `SnakeLemma.δ`, `Profinite.NobelingProof.succ_exact`,
  `SnakeLemma.δ_aux`, `SnakeLemma.δ'`, `SnakeLemma.δ_eq`, `SnakeLemma.δ'_eq`,
  `Algebra.H1Cotangent.exact_map_δ`, and
  `Algebra.Generators.H1Cotangent.exact_δ_map`. These concern connecting
  morphisms or cotangent exactness, not Tate residues or admissibility.
- `msearch.py`, LeanSearch: "Abstract Tate residue is additive in an exact
  sequence of modules with admissible subspaces". Eight hits concerned module
  length additivity (`Module.length_eq_add_of_exact`), cotangent addition,
  additive homology functors, Weierstrass remainder addition, localization,
  and Ext addition; none states this result.
- `msearch.py`, Loogle: `TateResidue.Admissible, TateResidue.res` returned
  zero hits and reported unknown identifier `TateResidue.Admissible` in its
  Mathlib search environment. This is not evidence against the upstream
  construction, which was found and read directly.
- `msearch.py`, Mathlib grep:
  `TateResidue|res_eq_add_of_exact|Admissible.*comap` returned zero hits.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `res_eq_add_of_exact|admissible.*exact|Admissible.*(comap|map)` found
  `TateResidue.res_eq_add_of_exact` in `ResidueProperties.lean:55`.
  I read its full signature and proof. It proves exactly the last conjunct,
  but the inherited admissibility assertions `hA₁` and `hA₃` are local proof
  facts, not declarations. Thus it cannot be attached as the whole node.
  Other hits concern unrelated admissibility notions.
- Direct `grep -rn 'lem-pc-tate-residue-exact-sequence' lean/WeilConjectures`
  returned no blueprint-tag match. `dag/lean_names_upstream.json` confirms
  the existing `Admissible`, `res`, and `res_eq_add_of_exact` names.
- Direct `rg` of the project and Mathlib for
  `residue_exact_sequence|admissible_and_res_eq_add_of_exact|residue_exact`
  found no collision for the new theorem name.

No node fault or disputed statement was found. The node is unchanged except
for `lean`. Validation uses only the prescribed server compile and delivery
wrappers; no local Lean build or direct repository mutation is performed.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
