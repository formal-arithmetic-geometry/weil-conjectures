## Worker report

Item: lem-sfb-prime-to-ell-linear-image-finite. The module
`Sheaf.RepresentationTheory.PrimeToEllLinearImageFinite` states
`Padic.primeToEll_linear_image_finite`, with its sole proof `sorry`. No definition,
helper node, dependency repair or statement correction is needed.

Read the full item statement and five proof steps; its sole statement dependency,
including its recorded declaration and the coefficient construction it imports;
the three further proof dependencies and their recorded source declarations;
Stanford Weil II seminar lecture 19, Proposition 1.1.9, pp. 2–3. That proposition
supplies the stable lattice, and the node explicitly labels the congruence
argument as an agent corollary. The proof docstring includes all five steps.

Hypotheses and clauses, in order:

- Prime ell: `(l : ℕ) [Fact l.Prime]`, including l = 2.
- Finite extension E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. This uses the exact underlying coefficient
  extension objects of `def-weil-l-adic-coefficient-extension`.
- Norm topology on E: `[tE : TopologicalSpace E]` and `_hE` identify it with
  `(spectralNorm.nontriviallyNormedField ℚ_[l] E).toUniformSpace.toTopologicalSpace`.
  This is the topology of the spectral absolute value
  `Padic.coefficientExtensionAbsoluteValue`, not an arbitrary field topology.
- Profinite group H: `(H : ProfiniteGrp.{v})`, whose bundled structure includes
  compactness, total disconnectedness and the topological group structure.
- Every finite continuous quotient has order prime to l: `_hH` quantifies over
  `N : OpenNormalSubgroup H` and asserts
  `Nat.Coprime (Nat.card (H ⧸ N.toSubgroup)) l`.
  Every such quotient is finite by compactness and discreteness. Conversely,
  the kernel of any continuous surjective homomorphism to a finite discrete
  group is open normal, and the first isomorphism theorem identifies that group
  with the corresponding quotient. Thus the quantifier is equivalent to the
  node's condition, with no restriction on quotient universes.
- Finite-dimensional E-vector space M: `(M : Type w) [AddCommGroup M]
  [Module E M] [FiniteDimensional E M]`. Universes u, v, w are independent.
- Norm topology on M: `[TopologicalSpace M] [IsModuleTopology E M]`.
  Over this complete nontrivially normed field the finite-dimensional module
  topology is the product topology in any basis, equivalently the topology of
  any compatible vector-space norm. This specifies precisely the usual topology
  and imposes no completeness, nonzero-dimension, or extra norm-choice hypothesis.
- Representation into GL_E(M): `(ρ : H →* (M ≃ₗ[E] M))`, using the group of
  E-linear automorphisms and its composition multiplication.
- Joint continuity: `_hρ : Continuous (fun p : H × M ↦ ρ p.1 p.2)`.
- Finite image: `Finite ρ.range`, using Mathlib's actual range subgroup.
- Its order prime to l: `Nat.Coprime (Nat.card ρ.range) l`. Finiteness is a
  separate conjunct, so the natural cardinal cannot hide an infinite image.
- Zero-dimensional case: no `Nontrivial M`, positivity or nonempty basis
  assumption occurs. If M = 0 its automorphism group and the image have order 1.

Dependency interfaces used and imported:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, is the recorded module for the sole
  statement dependency. Its public import
  `Sheaf.NumberTheory.Padics.CoefficientExtension` supplies the coefficient
  absolute value, integers, maximal ideal, uniformizer and finite-level rings.
  The statement uses the same field/algebra/finite-dimensional binders and
  spectral topology. No private coefficient construction is introduced.
- `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic`, `ProfiniteGrp`;
  `Mathlib.Topology.Algebra.OpenSubgroup`, `OpenNormalSubgroup` and its
  inherited `toSubgroup`; these implement the group and quotient hypothesis.
- `Mathlib.Topology.Algebra.Module.FiniteDimension` and its imported
  `Mathlib.Topology.Algebra.Module.ModuleTopology`, `IsModuleTopology`.
- Proof import `Sheaf.RepresentationTheory.ProfiniteStableLattice`,
  `Padic.exists_stable_lattice`, with the full signature/docstring read.
- Proof import `Mathlib.Topology.Algebra.Valued.LocallyCompact`,
  `Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField`,
  the `mathlib_match` for lem-weil-valued-dvr-finite-quotients.
- Proof import `Mathlib.GroupTheory.OrderOfElement`,
  `Nat.Coprime.pow_left_bijective`, the `mathlib_match` for
  lem-sfb-finite-matrix-group-coprime-power.

Edge cases checked before writing: zero-dimensional M; trivial H and trivial
representation (image order 1); quotient by all of H (order 1); ell = 2;
ramified coefficient extensions (the congruence proof uses l in the maximal
ideal rather than l being a uniformizer); and independent group, coefficient,
and vector-space universes. Groups are nonempty by their group structure;
there is no hidden exclusion of a legitimate empty vector-space basis.
No counterexample or disputed clause was found.

Searches made on 2026-10-21 with the prescribed msearch.py wrapper:

- LeanFinder: `A jointly continuous representation of a profinite group with
  finite quotients of order prime to ell on a finite dimensional ell adic
  vector space has finite image of order prime to ell`. Eight hits, including
  `ProfiniteGrp.toFiniteQuotientFunctor`,
  `CategoryTheory.PreGaloisCategory.has_decomp_quotients`,
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite`, and Galois/profinite
  constructors. None states the linear-image assertion.
- Loogle: `"Profinite", "GeneralLinearGroup"`: zero hits.
- Mathlib grep:
  `(congruence|profinite).*(GeneralLinear|finite.image)|(GeneralLinear|finite.image).*(congruence|profinite)`:
  zero hits.
- LeanSearch: `A continuous representation of a profinite group all of whose
  finite quotients have order coprime to ell on a finite dimensional vector
  space over a finite extension of the ell adic numbers has finite image`:
  eight hits, all profinite-group constructors or their canonical inverse-limit
  maps (`ProfiniteGrp.toLimit_fun_continuous`, `ProfiniteGrp.isIso_toLimit`, etc.);
  none asserts finite linear image.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `prime.to.*(image|finite)|linear_image_finite|primeToEll` and
  `lem-sfb-prime-to-ell-linear-image-finite|prime.to.*(monodromy|linear)|linear_image_finite`:
  related Sylow, tame-boundary and prime-to-ell geometry text only, no theorem
  with this assertion. Searching the exact item id in WeilConjectures gives no
  declaration. Exact proposed-name search in those two trees and
  `dag/lean_names_upstream.json` gives no clash.

Validation: prescribed scompile.py compiled both its private sandbox module and
`Sheaf.RepresentationTheory.PrimeToEllLinearImageFinite` successfully (2.7 s and
2.4 s). `set_option autoImplicit false` enforces explicit variable binding.
Every source line is at most 100 characters. The only postponed proof is the
named theorem, whose source and full proof plan are in its docstring.

## Second reading by NL

The dispatcher instructed this worker to deliver itself and not start other
agents; this is a second pass by the same worker, with independent review left
to the maintainer as specified in the brief. Reopened the node and completed
module and compared the binders and conclusion clause by clause as mapped
above. In particular, checked that `_hE` fixes the field topology rather than
requiring an unnecessary normed-algebra instance, that `IsModuleTopology`
fixes the vector-space topology, that `_hH` uses all open normal subgroups,
and that the conclusion concerns the actual range, with both finiteness and
coprimality explicitly present. No dimension positivity, faithfulness,
nontriviality or extra field restriction is present. The module imports each
recorded proof interface, and its docstring contains the induction `K_1 = K_n`
and the separatedness argument. No mismatch or change was found on this pass.
