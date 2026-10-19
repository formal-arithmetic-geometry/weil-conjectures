## Worker report

The module `Sheaf.RingTheory.JacobianTorsionEtaleShrink` states
`AlgebraicGeometry.jacobian_torsion_etale_shrink`, with proof `sorry`.
It formalizes Stacks restricted.tex, Tag 0ALQ (2), with the hypothesis expressed
by Tag 0AJU (3) and the canonical completed polynomial differential.
The reviewed natural statement and proof are unchanged. The sole additional
statement dependency is the already landed `def-per-completed-polynomial-conormal`.
No new nodes or dependency repair modules are delivered.

Hypothesis and clause correspondence:

- The commutative Noetherian ring A is `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`. The ideal is `(I : Ideal A)`.
- The commutative finite type A-algebra C is `(C : Type v) [CommRing C]
  [Algebra A C] [Algebra.FiniteType A C]`. The explicit algebra structure is the
  structure map in the node. `RingHom.FiniteType (algebraMap A C)` is equivalent
  by Mathlib's `RingHom.finiteType_algebraMap`; no extra finiteness is imposed.
- The integer r >= 0 is `(r : ℕ)`. The ring P is `rigPolynomialCompletion I r`:
  the `I.map (algebraMap A (MvPolynomial (Fin r) A))`-adic completion of
  `MvPolynomial (Fin r) A`. The ideal is `(J : Ideal (rigPolynomialCompletion I r))`.
- The presentation of the completion is `_e : (rigPolynomialCompletion I r ⧸ J)
  ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C`. Its orientation is immaterial
  because it is an algebra isomorphism; it specifies the original A-algebra structure.
- The exponent c >= 0 is `(c : ℕ)`. The common annihilation hypothesis is the pair
  `_hker` and `_hcoker`, each `I ^ c ≤ Module.annihilator A (...)`.
  `_hker` uses the kernel of `rigJacobianDifferential r I J`, whose domain is the
  actual `J.Cotangent = J/J²`. `_hcoker` uses the actual quotient of the target
  `Fin r → (P ⧸ J)` by the range. Thus it is its cokernel. For finite r, this
  product is the finite direct sum with its specified coordinate basis.
- The differential is the landed canonical `rigJacobianDifferential`, constructed
  using the unique filtration-preserving continuous extensions of polynomial
  partial derivatives, reduced modulo J and descended along J/J². There is no
  arbitrary differential or uncharacterized map in the hypotheses.
- The conclusion `∃ g : C, g - 1 ∈ I.map (algebraMap A C)` is exactly g ∈ 1 + IC.
- The final clause says that for every a ∈ I, `A → C[1/(g*a)]` is étale:
  `RingHom.Etale (algebraMap A (Localization.Away (g * algebraMap A C a)))`.
  In Spec(C_g), these are the inverse images of D(a) as a ranges over I.
  They cover precisely the inverse image of Spec(A) minus V(I), since a prime
  fails to contain I exactly when it omits some a ∈ I. Étaleness is local on
  the source. Thus the displayed condition is equivalent to the node's geometric
  conclusion, with the same g, by the affine-cover definition of an étale morphism.
  This equivalent ring-map formulation is also the convention in coord/STATE.md
  (ÉTALE RING MAPS). It permits independent universes u and v.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finite).
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` (finite monomial sums);
  its `aeval` and `algHom_ext` companions were read in Basic/Eval.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its compatible-sequence definition and canonical algebra structure.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, `Algebra.FiniteType`,
  and `RingHom.finiteType_algebraMap`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  the ring and algebra structure are from `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`; and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, defined affine locally by
  `RingHom.Etale`. The statement uses that same affine ring property.
- `Sheaf.RingTheory.CompletedPolynomialConormal`:
  `AlgebraicGeometry.rigPolynomialCompletion`, `rigPartialDerivative`,
  `rigJacobianRawDifferential`, and `rigJacobianDifferential`, including all
  docstrings and the full signatures of the unique-extension and descent obligations.
  The corresponding definition node was already landed and independently reviewed
  by Q93, so it is reused without copying or repairing it.

The non-public imports retain the already stated proof dependencies: finite
presentation of Noetherian submodules, exactness of completion, Nakayama,
localization exactness, principal-localization naive cotangent, polynomial Kähler
bases (including arbitrary variables), presentation homotopy equivalence, smooth
ring maps and the quotient conormal sequence. The affine étale criterion comes
from the public étale import. `lem-per-completed-jacobian-homology-comparison`
has no recorded module yet and therefore no import; its mathematical use is
explicitly named in the theorem's seven-step source proof docstring.

Edge cases checked against the exact source and expression:

- r = 0: the free target is the zero module; its kernel is the entire conormal
  module. No positive-r hypothesis is imposed.
- c = 0: I^0 = A, so both homology modules must actually vanish.
- I = 0: the complement is empty, the étale clause only inverts 0, giving the
  zero algebra, and g - 1 ∈ 0 forces g = 1. This is the source's vacuous conclusion.
- I = A: the completion is zero, but 1 + IC is all C and can include g = 0.
  This permits the empty source after shrinking, exactly as in the source.
- J = P and the zero algebra C are allowed. No `Nontrivial`, proper-ideal,
  injectivity of the structure map, or henselian/completeness assumption is added.
- A and C have independent universes. There is no unnecessary universe equality.

Searches made before writing:

- `msearch.py ... leanfinder`, query “If completed Jacobian kernel and cokernel
  are annihilated by an ideal power then a finite type algebra is etale away
  from the ideal after shrinking near the closed fibre”: eight hits, including
  `Algebra.exists_etale_of_isEtaleAt`, `Algebra.etaleLocus`, and localization
  permanence. None has the completed-Jacobian shrinking assertion.
- `msearch.py ... loogle "AdicCompletion.map, MvPolynomial.pderiv"`: zero hits.
- `msearch.py ... grep "rig.etale|completion.*[Ee]tale|[Ee]tale.*completion"
  RingTheory/Etale`: zero hits.
- `msearch.py ... leansearch`, query “Continuous partial derivatives and conormal
  Jacobian differential of the ideal adic completion of a polynomial ring”:
  hits include ordinary `MvPolynomial.pderiv` and `AdicCompletion.instCommRing`,
  not a new shrinking theorem.
- `msearch.py ... loogle "AdicCompletion.map, Ideal.Cotangent"`: zero hits.
- `rg` in the source `WeilConjectures` and `lean/Sheaf` for the item id,
  `completedJacobian`, `completed_jacobian`, `restrictedPderiv`, `adicPderiv`:
  no matching theorem. Completed Jacobian results in `TraceFormula` concern
  formal local presentations, not this general ideal-adic model.
- `tools/blueprint_refs.py search "completed polynomial"`: no blueprint-table
  match; a targeted DAG search of definition nodes for continuous derivatives
  found `def-per-completed-polynomial-conormal`. Reading its full landed module
  supplied exactly the missing canonical map. An initial broad search had not
  shown it; the module appeared in the subsequent targeted file inventory.
- Exact declaration-name `rg` for `jacobian_torsion_etale_shrink` and
  `jacobianTorsionEtaleShrink` found no pre-existing name in the source or Sheaf.

No STATEMENT-DISPUTED flag and no correction of the natural statement.
The previous attempt's stale-assignment report concerned the reviewed stage-1
split. This delivery does not split it: it adds the absent stage-2 Lean binding.

Validation: `scompile.py Q67 lem-per-jacobian-torsion-etale-shrink` compiled the
single delivered module cleanly, both sandbox check (3.5 s) and library module
check (4.6 s), under the prescribed per-file limit. No extra warnings were emitted.

## Second reading by Q67

Author's second reading (no separate agent was started, as the dispatcher brief
requires): reopened the node, source restricted.tex at equation (NL), 0AJU (3),
0GAF and 0ALQ (2), the landed completed-conormal interface, and the final Lean.
Checked every binder and conclusion as mapped above. In particular, checked that
using A-linear rather than P/J-linear kernel/range gives the same underlying
homology and the right I-annihilation; no change in modules is introduced.
Checked the affine cover conclusion on both empty-complement cases and verified
that no fixed completion isomorphism compatibility beyond A-linearity is needed.
The source allows an arbitrary completed presentation, as does the signature.
No mismatch found and no mathematical statement changed. The full seven-step
proof, including the common Nakayama annihilator and the arbitrary-variable
Kähler basis in step 6, is carried into the docstring for stage 3.
