## Worker report

The module `Sheaf.RingTheory.GroupAlgebraCoactionGrading` states
`AddMonoidAlgebra.group_algebra_coaction_grading`, with its sole proof `sorry`.
It states the node unchanged; no new definitions, dependency repairs, or statement
corrections are needed. The module and theorem docstrings cite Stacks Tag 0EKK,
`lemma-complete-reducibility-Gm`, and the theorem docstring contains all six proof
steps. Read groupoids.tex lines 2340–2370: the source treats the Laurent basis;
the node explicitly generalizes its coefficient calculation to arbitrary R and M.

Hypothesis and clause correspondence:

- A commutative ring R is `(R : Type u) [CommRing R]`.
- An arbitrary additive abelian group M is `(M : Type v) [AddCommGroup M]`.
- The group algebra is `AddMonoidAlgebra R M`, from the recorded
  `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup` import. Its basis `e_m` is
  `AddMonoidAlgebra.single m (1 : R)`; its standard coproduct and counit are
  `Coalgebra.comul` and `Coalgebra.counit`. Their values on basis elements are
  the group-like formulas (read Coalgebra/MonoidAlgebra.lean lines 30–60 and
  Bialgebra/MonoidAlgebra.lean lines 44–46, including their to_additive declarations).
- A commutative R-algebra is `(A : Type w) [CommRing A] [Algebra R A]`.
- The algebra homomorphism rho is
  `ρ : A →ₐ[R] A ⊗[R] AddMonoidAlgebra R M`. This is the balanced tensor product
  with Mathlib's usual commutative algebra structure.
- Coassociativity is `hcoassoc`: apply rho to the first factor by
  `ρ.toLinearMap.rTensor`, then the canonical `TensorProduct.assoc`, and equate
  this to applying `Coalgebra.comul` to the second factor by `LinearMap.lTensor`.
- Counitality is `hcounit`: apply the counit to the second factor and the
  canonical `TensorProduct.rid R A`, giving the original element a.
- The conclusion quantifies `W : M → Submodule R A`. Its first conjunct fixes
  its carriers exactly by `a ∈ W m ↔ ρ a = a ⊗ₜ[R] single m 1`; thus these
  are precisely the node's A_m and each is an R-submodule.
- The second conjunct gives, for every a, a unique `f : M →₀ A`, all of whose
  entries belong to W m and whose `f.sum (fun _ b ↦ b)` equals a. This means
  exactly unique finite homogeneous expansion, with omitted coefficients zero;
  uniqueness is of the family, not of a finite set with optional zero entries.
- The third conjunct is `(1 : A) ∈ W 0`.
- The fourth conjunct is `∀ r : R, algebraMap R A r ∈ W 0`.
- The fifth conjunct gives `a * b ∈ W (m + n)` for arbitrary homogeneous a,b.
- The sixth conjunct states the coaction formula for every homogeneous finite
  expansion of a, `ρ a = f.sum (fun m b ↦ b ⊗ₜ[R] single m 1)`.
  Together with existence and uniqueness this is exactly the final node clause.
- No finite generation, nonzero, field, reducedness, or torsion-freeness instance
  occurs. The universes u, v, w are independent and autoImplicit is disabled.

Dependency declarations read and used:

- `def-sfb-ring-diagonalizable-group`: read the complete module
  `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`, including
  `AlgebraicGeometry.ringDiagonalizableGroup` and `ringDiagonalizableGroupMap`.
  The statement needs its coordinate Hopf algebra, not its spectrum. The
  recorded module imports `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra` and
  uses precisely `AddMonoidAlgebra R M` with its canonical Hopf structure;
  this theorem uses that same object, with no private replacement.
- `def-weil-pbc-algebra-hom-quotient`: the Mathlib match is `AlgHom`, from
  `Mathlib.Algebra.Algebra.Hom`; read its signature and docstring at lines 29–34.
  Only the algebra/homomorphism clause is needed here, not the ideal clauses.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` (Defs.lean lines 77–84),
  `TensorProduct.lift` (Basic.lean lines 118–139), and `LinearMap.rTensor` and
  `LinearMap.lTensor` (Map.lean lines 321–345), all under
  `Mathlib.LinearAlgebra.TensorProduct`; read their full signatures/docstrings.
  Also read the canonical `TensorProduct.assoc` and `TensorProduct.rid` in
  Associator.lean lines 70–85 and 142–161.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: Mathlib's
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `productMap`, `productMap_apply_tmul`, and `ext`; read their
  recorded source ranges Basic.lean 140–165, 305–330, 348–365, 468–492 and
  Maps.lean 800–837. The statement uses the canonical tensor ring/algebra
  instances, supplied by `Mathlib.RingTheory.TensorProduct.Basic`.

Edge cases checked mathematically against the signature: R=0 and A=0 give the
zero expansion without nonzero assumptions; M=0 gives only degree zero; a
trivial coaction has only degree-zero components. Infinite M is allowed because
each family is finitely supported, not because M is finite. Torsion M, including
p-torsion in characteristic p, still has a free group-like basis and coefficient
extraction works. R=Z/4 and other nonreduced bases are permitted. For a=0 the
unique expansion is the zero finitely supported function. An additive group is
necessarily inhabited, so there is no excluded empty-group case. No tensor
exactness or flatness assumption is used in either the statement or its proof plan.

Searches actually run through batch2/msearch.py:

- LeanFinder: "A coaction of an additive group algebra on a commutative algebra
  gives a unique finite homogeneous weight decomposition". Eight hits, chiefly
  `AddMonoidAlgebra.grade.decomposition`/`grade.isInternal` and polynomial weighted
  decompositions. These grade an already specified algebra and do not turn an
  arbitrary coaction on A into its weight decomposition.
- Loogle: "Coalgebra.comul, Coalgebra.counit, DirectSum.IsInternal". No hits;
  the service reported unknown identifier Coalgebra.comul. This lookup was
  inconclusive, rather than evidence that the declaration is absent; the
  Coalgebra source was read directly afterward.
- LeanSearch: "A group algebra coaction on an algebra induces an internal
  grading by homogeneous weight submodules". Eight hits including `GradedAlgebra`,
  `DirectSum.IsInternal.gradedAlgebra`, monoid-algebra gradings and homogeneous
  submodules. None constructs the weight decomposition from a coaction.
- grep: "coaction|Comodule|comodule", subdirectory RingTheory. Zero hits (run twice).
- Direct rg of lean/WeilConjectures and lean/Sheaf for
  "coaction|coaction_grading|coactionGrading|weightSubmodule", plus the required
  grep by node id in WeilConjectures: no theorem for the arbitrary-ring,
  arbitrary-character-group statement. Existing Hopf linearization, rational
  representation and torus-weight modules address other notions or special cases.
- Direct rg for the proposed theorem/module names in both project trees and
  dag/lean_names_upstream.json: no collision.

No node fault or STATEMENT-DISPUTED issue was found. scompile.py compiled both
its sandbox check and the actual library module cleanly (1.9s and 1.7s).

## Second reading by Q26

Performed as a separate in-thread reading, since the dispatcher explicitly
prohibits starting other agents. This is not claimed to be an independent agent
review; the maintainer supplies the independent delivery review.

Reopened the node and the final theorem signature. Checked the R, M and A binders
against the first sentence, the tensor algebra homomorphism and both coaction
identities against the hypothesis sentence, and all six conclusion conjuncts
against the remaining sentences. The first conjunct fixes the carriers, so the
existential W cannot choose a different grading. The finite family predicate
requires membership also at omitted indices (zero), which is automatic in a
submodule and changes no mathematical hypothesis. The final formula is stated
for any expansion, which is equivalent to its being true for the unique one.
Tensor associativity is in the correct direction: (A tensor H) tensor H to
A tensor (H tensor H); counitality uses the right unit, matching A tensor H.
Independent universes do not impose the common-universe spectrum restriction
of the dependency's scheme presentation. No mismatch was found and no signature
change was required after the successful compile.
