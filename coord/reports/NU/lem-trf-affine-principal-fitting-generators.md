## Worker report

The module `Sheaf.RingTheory.AffinePrincipalFittingGenerators` states
`LinearMap.exists_fin_generators_quotient_fittingTorsion`, with `sorry` as the entire proof.
I read Stacks More on Algebra, Tag 080Z, `lemma-principal-fitting-ideal`, statement and
full proof, and the current five-step DAG proof. The natural statement is unchanged.
The shared repository already contains the reviewed stage-1 split; this delivery supplies
its stage-2 statement rather than resubmitting an unchanged stage-1 node.

Hypotheses and conclusion, clause by clause:

- A commutative local ring `(A, m)` is `{A : Type u} [CommRing A] [IsLocalRing A]`.
  Mathlib's local-ring predicate includes nontriviality and determines the unique maximal
  ideal, which is not otherwise used in the statement.
- An A-module M is `{M : Type v} [AddCommGroup M] [Module A M]`; `[Module.Finite A M]`
  is the recorded `def-weil-finitely-generated-module` declaration.
- The integer `k >= 0` is `(k : ℕ)` and the scalar is `(f : A)`.
- `Fit_k(M) = (f)` is the existential `hf`: a natural number n and A-linear
  `π : (Fin n → A) →ₗ[A] M`, with `Function.Surjective π` and
  `π.presentationFittingIdeal k = Ideal.span ({f} : Set A)`.
  This is exactly the presentation-independent ideal in the recorded dependency.
  Finite generation provides at least one such surjection; the first conjunct of
  `LinearMap.presentationFittingIdeal_independence_baseChange` says all surjective
  presentations have the same ideal. Thus existentially computing that ideal on one
  surjection is equivalent to the node's principal-ideal equality, and imposes no
  presentation, finite-presentation, or finitely generated kernel hypothesis on M.
  This is the same existential presentation convention already used by
  `Scheme.isFirstFittingIdealSheaf`.
- The submodule `{x | f x = 0}` is `LinearMap.ker (LinearMap.lsmul A M f)`:
  `LinearMap.lsmul_apply` identifies its map with `x ↦ f • x`, and membership in the
  kernel means that value is zero. This kills exactly f, not arbitrary powers of f.
- The conclusion is `∃ s : Fin k → (M ⧸ LinearMap.ker (LinearMap.lsmul A M f)),
  Submodule.span A (Set.range s) = ⊤`. This says the specified quotient is generated
  by k elements, with repetitions/zeros allowed. It imposes no independence condition.

Dependency declarations read and used:

- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` and its finite-span meaning.
- `Sheaf.RingTheory.PresentationFittingIdeal`: `LinearMap.presentationFittingIdeal`
  and `LinearMap.presentationFittingIdeal_independence_baseChange`. I read the full
  source, including all helper definitions, signatures, docstrings and the top-ideal
  branch for `n ≤ k`. The theorem requires finite generation, not finite presentation.
- Proof import `Mathlib.LinearAlgebra.Matrix.Adjugate`: `Matrix.adjugate_mul`,
  `Matrix.mul_adjugate`, `Matrix.adjugate_fin_succ_eq_det_submatrix`, the recorded
  declarations of `lem-weil-pbc-matrix-adjugate-identity`.
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, reexported by the presentation
  module: `Matrix.det`, `Matrix.det_apply`, the recorded determinant dependency.
- Signature notions additionally use `Mathlib.RingTheory.LocalRing.Defs`,
  `Mathlib.LinearAlgebra.BilinearMap` (`LinearMap.lsmul`), and
  `Mathlib.LinearAlgebra.Quotient.Defs` (the canonical submodule quotient).

The declaration docstring reproduces every step of the DAG proof: boundary cases;
selection of a minor generating `(f)` by the explicit local coefficient argument;
left multiplication of the relation-row matrix `(D E)` by `adj(D)`; identification
of its last block entries with replaced-column minors; and elimination of the first
`n-k` generators modulo the f-annihilator. This uses no cancellation by f.

Edge cases checked before finalizing:

- `f = 0`: its scalar endomorphism has kernel top, so the quotient is zero and any
  length k zero family spans, including the empty family when k is zero.
- `k = 0`: `Fin 0` is empty; its span is bottom, so the conclusion says exactly
  that the quotient is zero. This is the source's intended case.
- Zero M, n = 0 and n ≤ k: the presentation ideal uses its documented top branch;
  the generators of any presentation of length at most k can be padded with zeros.
- A field and free M of rank k, with f a unit: the kernel is zero and k generators
  are sufficient. The statement does not exclude positive characteristic.
- A = Z/4Z, M = A/(2), k = 0, f = 2: Fit_0(M) = (2), multiplication by 2 is
  zero on M, and its quotient is zero. A = Z/4Z, M = A ⊕ A/(2), k = 1, f = 2
  gives a nonzero quotient with one generator. No nonzerodivisor assumption is valid.
- Universes u and v are independent and explicitly declared. The ring is nonzero
  because the source assumes a local ring; no extra domain/Noetherian assumption.

Searches performed with msearch.py (actual machine results are in searches.jsonl):

- `leanfinder` query `presentation-independent Fitting ideal of a finitely generated module`: 8 hits; Ideal.exists_pow_inf_eq_pow_smul, Ideal.mem_iInf_smul_pow_eq_bot_iff, LieModule.mem_posFittingCompOf, Ideal.iInf_pow_smul_eq_bot_of_le_jacobson, Submodule.FG.jacobson_smul_lt.
- `loogle` query `LinearMap.presentationFittingIdeal, Module.Finite.exists_fin'`: 0 hits; loogle: unknown identifier 'LinearMap.presentationFittingIdeal'.
- `grep` query `presentationFittingIdeal|fittingIdeal|FittingIdeal`: 0 hits; no matches.
- `leansearch` query `presentation-independent Fitting ideal of a finitely generated module`: 8 hits; Module.Presentation.finite, FGModuleRepr.ofFinite, Module.FinitePresentation.recOn, Module.finitePresentation_of_finite, Module.FinitePresentation.out.
- `leanfinder` query `over a local ring, a finite module whose kth Fitting ideal is generated by f has k generators after quotienting by the elements killed by f`: 8 hits; Module.supportDim_le_supportDim_quotSMulTop_succ, Ideal.finrank_quotient_eq_sum, IsLocalRing.finrank_quotient_map, Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson, Module.exists_isPrincipal_quotient_of_finite.
- `loogle` query `LinearMap.ker, Submodule.span, IsLocalRing`: 0 hits; no matches.
- `grep` query `fitting|Fitting|principal.*generators`: 3 hits; Mathlib/RingTheory/Artinian/Module.lean, Mathlib/RingTheory/Artinian/Module.lean, Mathlib/RingTheory/Ideal/IsPrincipal.lean.
- `leansearch` query `principal Fitting ideal finite local module quotient annihilated by f generated by k elements`: 8 hits; Module.exists_isPrincipal_quotient_of_finite, FractionalIdeal.isPrincipal_iff, Module.Finite.quotient, Module.instQuotientIdealSpanSingletonSetSubmoduleHSMulTop, Module.exists_ker_toSpanSingleton_eq_annihilator.

The semantic hits concern principal quotients, support dimension, PID torsion and generic
finite-generation facts; none states this Fitting-ideal quotient generator bound.
The precise Loogle query with `LinearMap.ker, Submodule.span, IsLocalRing` had no hits.
Mathlib RingTheory grep found only Fitting decomposition for endomorphisms and an
unrelated principal-ideal declaration.

I also ran direct `rg` searches in the upstream `WeilConjectures` sources and the shared
`lean/Sheaf` sources, and searched `dag/lean_names_upstream.json`. The exact blueprint
id is absent upstream. Searches for `fittingIdeal|FittingIdeal|fitting.*torsion|principal.*fitting`
found the published presentation ideal and its sheaf applications only; the upstream name
index has no matching declaration. The new theorem's full name is absent from those
sources. No duplicate theorem or additional definition is introduced.

No statement correction, disputed statement, new node or dependency repair is needed.
Only the item's `lean` record is changed. The previous failed dry run's unchanged-item
problem is resolved by the new item module and Lean binding.

Validation: the prescribed scompile.py compiled both the sandbox copy and the intended
library module independently, with no errors or warnings (the sole theorem uses sorry).
The sandbox-only preliminary module-level Fitting definition was removed: the existing
presentation interface suffices, so no unused module or node is delivered.

## Second reading by NU

Independent maintainer second reading of the NU delivery, 2026-10-18. This section
records the present reviewer’s reading; it does not claim that a NU worker performed
an earlier reading. I read the immutable node, both statement-dependency nodes, the
complete delivered module and worker report, Stacks 080Z and 080R, and the exact
Mathlib/project declarations below. The Lean statement says exactly what the node says.

Clause checks:

- `{A : Type u} [CommRing A] [IsLocalRing A]` is a commutative local ring. Mathlib’s
  nontriviality agrees with Stacks’ definition requiring exactly one maximal ideal;
  the maximal ideal need not be an extra parameter because it does not enter the result.
- `{M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]` is precisely a
  finitely generated A-module. `Module.Finite.fg_top` is the recorded dependency;
  `Module.Finite.exists_fin` supplies a finite generating family.
- `(k : ℕ) (f : A)` covers every nonnegative integer and every scalar.
- `hf` requires a surjective finite-free map and equality of its
  `presentationFittingIdeal k` with `Ideal.span ({f} : Set A)`. I read the definition:
  it is top when `n ≤ k`, otherwise the span of determinants of `n-k` kernel rows
  restricted to distinct columns. The first conjunct of the recorded independence
  theorem makes this the presentation-independent Fitting ideal. Finite generation
  supplies a finite-free surjection, so the existential encoding adds no hypothesis.
  There is no finite-presentation or finite-generation-of-relations assumption.
- `LinearMap.lsmul A M f` evaluates to `f • x` by `LinearMap.lsmul_apply`;
  `LinearMap.mem_ker` identifies its kernel with exactly `{x | f • x = 0}`.
  The standard submodule quotient is therefore the specified quotient.
- `∃ s : Fin k → ..., Submodule.span A (Set.range s) = ⊤` says that quotient has
  k generators. Zero padding makes this equivalent to at most k generators;
  no independence or minimality is asserted.

Edge cases: `f = 0` gives kernel top and zero quotient; `k = 0` gives the empty
family and forces the quotient to be zero; zero M and `n = 0` are included.
For `n ≤ k` the dependency’s top-ideal branch and padding agree with the source.
A unit f has zero kernel. Nonzero zero divisors remain allowed: for example
A = Z/4Z, M = A/(2), k = 0, f = 2 gives zero quotient, while M = A ⊕ A/(2)
and k = 1 gives a cyclic quotient. No characteristic or Noetherian assumption
appears. The zero ring is excluded by the source’s local-ring convention.
The universes u and v are independently bound, with no imposed equality.

I read `PresentationFittingIdeal.lean` in the read-only group clone, including its
real helper constructions and independence/base-change theorem. I also read
Mathlib’s `Module.Finite`, `IsLocalRing`, `lsmul`, `ker`, submodule quotient and span;
`Matrix.adjugate_mul`, `Matrix.mul_adjugate`,
`Matrix.adjugate_fin_succ_eq_det_submatrix`, `Matrix.det` and `Matrix.det_apply`.
The proof docstring follows all five node steps, including the local unit-minor
argument, left adjugate multiplication, replaced-column minors and elimination.
There is no cancellation by f. Proof dependencies have the required imports.
The module introduces no definitions and its sole theorem has exactly `by sorry`.
Both docstrings have the source place and blueprint id. No line exceeds 100
characters. Programmatic comparison confirms `lean.statement` is verbatim equal
to the delivered signature. The immutable commit changes only the item’s `lean`
record, adds its module and adds this report; no statement correction is involved.

Independent `rg` searches in Mathlib, upstream WeilConjectures, the group’s
lean/Sheaf tree and upstream-name index used `fittingIdeal`, `FittingIdeal`,
`fitting.*[Tt]orsion`, `principal.*[Ff]itting`, the full theorem name, and
`generators.*annihilat`. Results contain the existing presentation ideal and sheaf
applications, unrelated Fitting decomposition and a regular-prime generator lemma;
none duplicates this theorem. The worker’s semantic/Loogle/grep searches are recorded
above. No new notion, dependency repair, or missing prerequisite is needed.
Neither the item nor its statement/proof dependencies is on the route-pivot dropped
list, and no route-pivot repair note exists for this item. No dropped machinery occurs.

Reproduced compilation using the prescribed command on the immutable module:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NU
lem-trf-affine-principal-fitting-generators
snapshot/lean/Sheaf/RingTheory/AffinePrincipalFittingGenerators.lean`
(arguments are on one command line). Exit status 0; no diagnostics. The wrapper
reported sandbox compilation in a private `/dev/shm/nt-tmp/.../.lbuild` overlay
(5.4 s) and library-module compilation (8.6 s), each with a 60 s limit. The currently
installed wrapper invokes its server compilation service; this review used that
prescribed wrapper, not a direct compiler or direct SSH command.

Finding and correction: the original second-reading section only said no reading
had occurred (H11). This complete replacement report preserves the Worker report
and replaces that placeholder with the actual independent reading above. No Lean,
node, hypothesis, conclusion or proof-plan change was needed. No global build,
live Lean write, project-clone edit, claim, delivery or merge was performed.
