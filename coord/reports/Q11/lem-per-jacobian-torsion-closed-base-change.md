## Worker report

This repair states `Algebra.jacobianTorsion_closedBaseChange` in
`Sheaf.RingTheory.JacobianTorsionClosedBaseChange`, using the existing definition node
`def-per-completed-polynomial-conormal` and its canonical differential. The theorem is the
only postponed proof in this module; its docstring retains all seven proof steps. The
natural-language statement and proof are unchanged. The item gains the already landed
conormal definition in `stmt_deps`; its other change is its `lean` record. There are no new
nodes or dependency modules.

The Lean rendering of every hypothesis and clause is:

- A commutative Noetherian ring is `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
- The ideal and arbitrary finite variable count are `(I : Ideal A) (r : ℕ)`. The existing
  `AlgebraicGeometry.rigPolynomialCompletion I r` is exactly the completion of
  `MvPolynomial (Fin r) A` at `I.map (algebraMap A (MvPolynomial (Fin r) A))`.
- The presentation ideal is `(J : Ideal (rigPolynomialCompletion I r))`; E is literally
  `rigPolynomialCompletion I r ⧸ J`.
- I-adic completeness of E is `[IsAdicComplete I (rigPolynomialCompletion I r ⧸ J)]`.
- The specified continuous conormal differential is the existing
  `AlgebraicGeometry.rigJacobianDifferential r I J`. Its domain is `J.Cotangent = J/J²`;
  its target is `Fin r → (rigPolynomialCompletion I r ⧸ J)`. Its definition is the map
  induced from the unique continuous polynomial partial derivatives. There is no
  additional differential parameter or characterization assumption.
- The single nonnegative torsion exponent is `(c : ℕ)`. Universally binding any witness c
  is equivalent to the implication whose premise is existence of such a c.
- The kernel clause is `hker : I ^ c • (rigJacobianDifferential r I J).ker ≤ ⊥`.
  The ideal acts over A, exactly as in the parent algebraization theorem.
- The cokernel clause is `hcoker : I ^ c • (⊤ : Submodule A
  ((Fin r → (rigPolynomialCompletion I r ⧸ J)) ⧸
  (rigJacobianDifferential r I J).range)) ≤ ⊥`. The cokernel is the target modulo the
  range as an A-module, and its entire top submodule is annihilated by the same I^c.
- The arbitrary closed base ideal is `(H : Ideal A)` and A0 is literally `A ⧸ H`.
- `(K : Ideal (A ⧸ H))` is arbitrary subject to `hV`, which equates exactly the zero loci
  of `I.map (Ideal.Quotient.mk H)` and K in `PrimeSpectrum (A ⧸ H)`.
- `Algebra.CompletedPolynomialClosedQuotient I r J H` is the actual double quotient
  `(rigPolynomialCompletion I r ⧸ J) ⧸ H.map
  (algebraMap A (rigPolynomialCompletion I r ⧸ J))`, so it is exactly E/HE.
  Its A/H-algebra instance is Mathlib's existing
  `Ideal.Quotient.algebraQuotientMapQuotient`, without a replacement instance.
- K-adic completeness is the first conclusion
  `IsAdicComplete K (CompletedPolynomialClosedQuotient I r J H)`.
- The presentation binds `∃ (s : ℕ) (J0 : Ideal (rigPolynomialCompletion K s))` and an
  `A ⧸ H`-algebra isomorphism, recorded by
  `Nonempty ((rigPolynomialCompletion K s ⧸ J0) ≃ₐ[A ⧸ H]
  CompletedPolynomialClosedQuotient I r J H)`. The direction of this isomorphism is
  equivalent by inversion to E0 being isomorphic to the presented quotient.
- For this same s and J0 the conclusion binds `∃ d : ℕ`. The kernel clause is
  `K ^ d • (rigJacobianDifferential s K J0).ker ≤ ⊥`. The cokernel clause is
  `K ^ d • (⊤ : Submodule (A ⧸ H)
  ((Fin s → (rigPolynomialCompletion K s ⧸ J0)) ⧸
  (rigJacobianDifferential s K J0).range)) ≤ ⊥`. These use the canonical differential
  over A0 and the same exponent d. No flatness hypothesis is imposed.

Dependency declarations read and used:

- `def-per-completed-polynomial-conormal`: `AlgebraicGeometry.rigPolynomialCompletion`,
  `rigPartialDerivative`, and `rigJacobianDifferential` in
  `Sheaf.RingTheory.CompletedPolynomialConormal`. I read the full module, including
  the uniqueness and well-definedness theorems. The derivative is the unique A-linear
  filtration-preserving extension; the differential descends it through J/J².
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`, available through the conormal module.
- `def-weil-pbc-adic-completion`: `AdicCompletion` and `IsAdicComplete` in
  `Mathlib.RingTheory.AdicCompletion.Basic`, with the algebra structures supplied by
  `Mathlib.RingTheory.AdicCompletion.Algebra`, through the conormal module.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`; the underlying closed sets use
  `PrimeSpectrum.zeroLocus`.
- `Mathlib.RingTheory.Ideal.Over` supplies the canonical quotient algebra action;
  `Mathlib.RingTheory.Ideal.Quotient.Noetherian` supplies
  `Ideal.Quotient.isNoetherianRing`, needed by the canonical differential over A/H.
- The original proof-only imports are retained without `public`: finite-type
  Noetherian permanence, completion Noetherianity, completion modulo an ideal,
  finite-module tensor comparison, radical powers, and change of ideal completion.
  They are `Mathlib.RingTheory.FiniteType`,
  `WeilConjectures.RingTheory.AdicCompletionNoetherian`,
  `Mathlib.RingTheory.AdicCompletion.LocalRing`,
  `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`,
  `Mathlib.RingTheory.Finiteness.Ideal`, and
  `WeilConjectures.Algebra.ChangeIdealCompletion`.

Source: I reread restricted.tex remark-take-bar and equation-base-change-to-closed,
equation-NL, Tag 0AJU condition (3), and Tag 0GB2. These identify the actual closed
quotient and require annihilation of both homology modules of the continuous conormal
map. The existing conormal node states this exact map.

Edge cases checked: r=s=0 use `Fin 0`, hence the zero target, while the kernel still
records the full conormal module. c=d=0 mean the unit ideal annihilates both modules,
so both must vanish; no positivity assumption was inserted. I=0 and I=⊤, J=⊥ and
J=⊤, H=⊥ and H=⊤, and the zero coefficient ring are admitted. In particular H=⊤
gives the zero closed quotient, with Mathlib's canonical quotient action and
Noetherian instance. K is not assumed equal to IA0, only to have the same vanishing
locus. All coefficient rings remain in arbitrary universe u.

Searches (the original wrapper results are retained in searches.jsonl):

- LeanFinder, `Closed quotient base change preserves ideal power torsion in kernel and
  cokernel of continuous conormal differential of completed polynomial algebra`:
  eight cotangent/Jacobi--Zariski and smooth-lifting hits, no exact theorem.
- Loogle, `AdicCompletion.map, MvPolynomial.pderiv` and
  `AdicCompletion.evalₐ, MvPolynomial.pderiv`: zero hits for each.
- Mathlib grep, `AdicCompletion.*deriv|deriv.*AdicCompletion|completed.*[Cc]onormal`:
  zero hits; RingTheory grep,
  `completed.*[Cc]onormal|[Cc]onormal.*completion|AdicCompletion.*pderiv`: zero hits.
- LeanSearch for the continuous completed polynomial conormal differential returned
  eight component-construction hits, not the combined map.
- Original read-only project searches found formal-power-series presentations with
  different coefficient-field/maximal-ideal hypotheses and no exact theorem.
- The repair's source/DAG search and full module reading find the now-landed Q93
  `def-per-completed-polynomial-conormal`. It supersedes the earlier negative search:
  this delivery imports it and drops the duplicate construction. Reading
  `Sheaf.RingTheory.RigEtaleJacobianAlgebraization` confirms its input kernel and
  cokernel hypotheses use exactly our repaired canonical differential and ideal actions.
- Reading Mathlib `Ideal/Over.lean` finds the existing canonical quotient algebra
  instance, which replaces the removed duplicate instance.

## Repair of return L at bdf7484b9dfd

1. H12/H4: removed the new node
   `def-per-completed-polynomial-conormal-differential` and its module
   `CompletedPolynomialConormalDifferential.lean`. Replaced the dependency by the
   already reviewed `def-per-completed-polynomial-conormal`. Restated the item on
   `rigPolynomialCompletion` and `rigJacobianDifferential`, using precisely the
   parent's `I^c • ker ≤ ⊥` and `I^c • ⊤(coker) ≤ ⊥` form. The output uses K over
   `rigPolynomialCompletion K s`. Added the requested Noetherian quotient import.
2. Secondary H4: removed `completedPolynomialClosedQuotientAlgebra`; imported
   `Mathlib.RingTheory.Ideal.Over` and use its instance unchanged.

The initial saved-packet dry run completed as 08dbb9cfe1 and passed mechanically,
but still contained the returned duplicates; the repairs above were therefore made.
The repaired sole module then compiled through scompile.py at its actual library name
in 5.1 seconds, without errors or warnings. Every variable/universe is explicit and
`autoImplicit` is disabled. The node signature is copied verbatim from the file.
There is no statement correction or disputed statement.

## Second reading by Q11

Self-check after repair, with the natural node, the revised module, the Q93 conormal
module and the parent's statement open: the input ring, completion, quotient,
completeness, single torsion exponent, both homology annihilation hypotheses,
arbitrary H, vanishing-locus condition, output completeness, A/H-algebra presentation
and both output torsion clauses match as detailed above. The two mismatches in the
return were the duplicated conormal notion and quotient algebra instance; both were
removed. The parent now uses exactly the same canonical conormal map and submodule
annihilation hypotheses. No independent worker review is claimed; the maintainer
performs the independent review after delivery.
