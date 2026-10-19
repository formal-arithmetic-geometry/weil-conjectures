## Worker report

The module `Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus` states the
kernel-normalized determinant calculus of Stacks, More on Algebra, Tags 0FJI, 0FJK,
and 0FJL. Definitions have real data; all theorem proofs are `sorry`. The delivered
module compiles through scompile.py in both sandbox and library contexts without
errors or warnings (2.7 and 2.9 seconds on the final explicit compilation).

The node's hypotheses and clauses are rendered as follows:

* `{R : Type u} [CommRing R]` is the arbitrary commutative ring, including the zero ring.
* `TwoTermComplex R` has `neg`, `zero`, and `differential`, precisely a complex in
  degrees -1 and 0. Its terms are `ModuleCat.{v} R`; no relation between u and v is
  imposed. `TwoTermMap` has both component maps and the chain-map equation.
* The four term hypotheses `[Module.Finite R T] [Module.Projective R T]`, for the
  terms of P and Q, say that all terms are finite projective. These are the usual
  Mathlib notions, equivalent to being direct summands of finite free modules.
* `twoTermDeterminant P` is exactly `determinantModule R P.zero` tensor the R-dual
  of `determinantModule R P.neg`. The imported determinant module is the exterior
  socle, already identified with the locally glued top exterior power by
  `Module.determinantModule_topExterior`, `determinantModule_localization`, and
  `determinantModule_finite_projective`. Thus this reuses the existing determinant,
  including nonconstant rank, rather than creating a new determinant construction.
* `ha : a.DegreewiseSurjective` asserts surjectivity in both degrees. `hqa : a.QuasiIso`
  asserts bijectivity on differential kernels in degree -1, injectivity on degree-zero
  cokernels via the difference/range condition, and surjectivity on those cokernels
  via the representative/range condition. These are precisely the cohomology groups
  of a complex with no other terms; no restriction on a derived category is added.
* The first four conjuncts give finite generation and projectivity of the two
  component kernels. `Function.Bijective a.kernelDifferential` says the induced
  differential between these kernels is an isomorphism of R-modules.
* `IsKernelNormalizedDeterminantMap` requires `γneg` and `γzero` to satisfy the
  existing `Module.IsDeterminantExactSequenceMap` predicate. Consequently they are
  exactly the kernel-first wedge maps of the node, not arbitrary isomorphisms.
* The predicate states the contraction formula
  `T (γzero (nzero ⊗ qzero) ⊗ φ) = qzero ⊗ (φ ∘ γneg ∘ (nneg ⊗ -))`
  whenever `nzero.val = ExteriorAlgebra.map a.kernelDifferential nneg.val`.
  This is precisely the node's assembly by γzero and the inverse dual of γneg,
  with insertion of the fixed element δ_N = det(d_N). To check the equivalence,
  localize where the kernel determinant has basis n. Then δ_N = d_N(n) tensor n-dual;
  contracting the inverse dual of γneg gives the displayed functional on det(Q.neg).
  These local generators and pure tensors determine the whole map. No assembly map
  or trivialization is left unconstrained. Ordinary tensor symmetry introduces no sign.
  The formula avoids introducing extra arbitrary choices of Γ or δ, while specifying
  exactly the composite and normalization prescribed by the node.
* `existsUnique_kernelNormalizedDeterminantMap` states existence and uniqueness for
  this precise characterization. `kernelNormalizedDeterminantMap` chooses that
  uniquely determined object. Its data is therefore fixed despite the postponed proof.
* The next conjunct is `T_id = LinearEquiv.refl`, with identity surjectivity and
  quasi-isomorphism supplied by named, postponed helper theorems.
* The following conjunct quantifies over `a'`, its two required predicates, and
  `h : P.zero →ₗ[R] Q.neg`; its two premises are exactly
  `a'.zero - a.zero = Q.differential ∘ h` and
  `a'.neg - a.neg = h ∘ P.differential`. Its conclusion is `T_a = T_a'`.
* The final conjunct quantifies over S, the finite-projectivity hypotheses on both
  its terms, and a degreewise-surjective quasi-isomorphism `b : TwoTermMap Q S`.
  It asserts `T_(ba) = (T_a).trans (T_b)`, i.e. `T_b ∘ T_a` in the node's order.
  The homotopy assumptions apply only to homotopy invariance; the composition
  assumptions apply only to composition. Neither restricts the kernel conclusion.

Dependency declarations checked and used:

* `Module.Projective`, `Module.projective_lifting_property` from
  `Mathlib.Algebra.Module.Projective`.
* `ExteriorAlgebra`, `ExteriorAlgebra.ι`, `exteriorPower`, and `ExteriorAlgebra.map`
  from `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`.
* `Module.determinantModule` from `Sheaf.LinearAlgebra.ProjectiveDeterminantModule`,
  imported publicly through `Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence`;
  the latter supplies `Module.IsDeterminantExactSequenceMap`,
  `Module.existsUnique_determinantExactSequence`, and the determinant identifications.
* `Module.exists_standardFreeCover_of_finite_projective` from
  `WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover`, read with
  `scompile.py --source` because the older local upstream checkout lacks its file.
* `exists_common_summand_surjections` from
  `Sheaf.TraceFormula.LocalCommonSummandSurjections`.
* `Matrix.det_one_add_mul_comm` from `Mathlib.LinearAlgebra.Matrix.SchurComplement`.
  This is the recorded Mathlib match of the rectangular-determinant proof dependency.
* `DerivedCategory` and `HasDerivedCategory` from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, imported for the recorded
  cohomology/quasi-isomorphism proof dependency. No derived object is needed as a
  binder: its two-term kernel/cokernel content is expanded explicitly.
* `AlgebraicGeometry.Scheme` is the recorded Mathlib notion behind the determinant's
  description on rank loci; the determinant dependency already identifies its real
  exterior-socle construction with those local top wedges. No new scheme is defined.

Edge cases checked: zero ring, zero modules, empty wedges, identity with zero kernel,
zero quotient, rank-zero rectangular matrices, characteristic two, and nonconstant
rank. In the zero-kernel case the contraction formula specializes to the empty wedge
and evaluation, so it forces the identity rather than permitting an arbitrary scalar.
For an isomorphism between complexes concentrated in degree zero it forces the
usual determinant of that isomorphism. For an acyclic kernel of rank one it contracts
against its actual differential, so rescaling the differential rescales the prescribed
trivialization in the required direction. There are no field, local-ring, nonzero-rank,
Noetherian, or characteristic hypotheses on the calculus theorem.

Saved searches were retained and checked rather than restarting the investigation:

* `msearch.py ... grep "TwoTermComplex|surjective_two_term_determinant_calculus|kernelNormalizedDeterminantMap"`
  over the upstream source returned zero hits (saved in searches.jsonl).
* `msearch.py ... loogle "Module.determinantModule, Module.Dual, LinearMap.ker, Function.Bijective"`
  returned no hits and reported that the side-project determinant identifier is unknown
  to Loogle; its existing project definition was instead read directly.
* `msearch.py ... leanfinder "determinant map for degreewise surjective two-term quasi-isomorphism finite projective modules"`
  returned eight generic cohomology/projectivity/scalar-determinant results; none is
  the determinant-line construction. The saved node also records the LeanSearch query
  about determinants of short exact sequences and homotopic surjections: its eight
  results likewise concern ordinary exactness and endomorphism determinants.
* The saved direct rg search of `lean/Sheaf` found no existing two-term calculus.
  The existing determinant dependencies were opened and reused, not copied.

No new definition nodes, dependency repair, or natural-language statement correction
was needed. All auxiliary declarations belong to this node's construction and are
listed in `lean.declarations`. Every postponed theorem has a source and proof docstring.
`STATEMENT-DISPUTED:` none for the repaired statement.

## Second reading by Q123

The resumed self-check found a substantive defect despite the saved packet passing
mechanical checks: its normalization predicate existentially quantified an unconstrained
Γ and δ. Over a ring with multiple units, rescaling those witnesses allowed multiple
T's, so the claimed uniqueness did not hold. Its unused kernel-determinant abbreviation
also reversed the two degrees. I removed that abbreviation and replaced the predicate
with the explicit contraction formula above. This fixes the source's δ and the
assembly simultaneously; it does not change the DAG statement. In the identity case
the formula forces evaluation on empty kernel wedges and hence T = id.

I also moved the homotopy and composition hypotheses inside the corresponding
conjuncts, so the kernel conclusion is available under exactly the node's initial
hypotheses, and added the missing source/proof docstrings and determinant-switch
proof import. I reread the node, the full module, the exact-sequence determinant
interface, and the source construction and Tags 0FJK/0FJL. All hypotheses, both kernel
finiteness/projectivity assertions, kernel acyclicity, the canonical normalization,
identity, both homotopy equations, and composition now match as detailed above.
This is the worker's self-check; the maintainer's independent review remains separate.
