## Worker report

The module `Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation` states
`LieAlgebra.exists_chevalley_admissible_representation`. Its sole proof is `sorry`.
No new definitions or nodes, dependency repairs, or statement corrections are needed.
The original node fields are unchanged except for `lean`.

Hypotheses, matched with the node:

- The finite-dimensional rational vector space is `V : Type u` with `AddCommGroup`,
  `Module ℚ`, and `FiniteDimensional ℚ` instances. No nonzero-dimensional hypothesis occurs.
- The finite reduced crystallographic root system is given by `R : Set V`, rational
  functionals `c : R → Module.Dual ℚ V`, and its explicit axioms. `hfinite` says finite;
  `hne` excludes zero; `hspan` says the roots span; `htwo` normalizes each coroot to 2;
  `hint` makes root-coroot evaluations integers; `hreflect` says each indicated reflection
  permutes the root set; `hreduced` says precisely that its intersection with a rational
  root line is the root and its negative. These are the root-system conventions in the
  conclusion of `RootDatumLattice.lattice_embedding`, and the same arbitrary-space
  hypotheses used by `LieAlgebra.rationalSerrePresentation`.
- `P : Submodule ℤ V` and `hP` specify the weight lattice exactly by integral evaluation
  under every given coroot. This is a parameter characterized by the existing node's
  defining formula, not a new definition or an extra restriction. The recorded
  `RootDatumLattice.weightLattice` applies to the particular tensor rationalization of an
  integral datum; the current statement, like the node, starts with an arbitrary rational
  root system. No choice of an integral datum is imposed. The module imports that
  dependency and uses its explicit conventions rather than replacing the input by a
  lattice-embedding special case.

Conclusions, clause by clause:

- The existential `g : Type u`, Lie structures, and finite-dimensional instance are the
  rational finite-dimensional Lie algebra. `HasTrivialRadical ℚ g` is exactly the
  semisimplicity definition recorded by `def-wf-semisimple-lie-algebra`, not a different
  direct-sum predicate.
- `H : LieSubalgebra ℚ g`, `IsLieAbelian H`, and the quantified maximality clause say
  maximal abelian subalgebra. Its simultaneous diagonalizability follows explicitly from
  the nonzero eigenvectors `e a`, their bracket formula with every `h : H`, the abelian
  zero-weight summand H, and `DirectSum.IsInternal` of H and the root lines. Thus this
  is the splitting Cartan required by the node.
- `θ : H ≃ₗ[ℚ] Module.Dual ℚ V` is the stated identification `H ≃ Vᵛ`. Finite-dimensional
  evaluation and its dual give exactly `Hᵛ ≃ V`. A weight `v : V` evaluates on H as
  `fun h : H ↦ θ h v`; the coroot element is `θ.symm (c a)`.
- `e : R → g`, its nonvanishing clause, and the internal sum of the rational root lines
  give `g = H ⊕ ⨁ a, ℚ e_a`. The existential simple-root basis `b`, `hb`, and integral
  sign-coherent coordinate clauses give exactly the simple base in the node. The basis
  `B : Module.Basis (Fin r ⊕ R) ℚ g` has simple coroots and the chosen root vectors as
  its entries.
- The opposite-root bracket is quantified over `a b : R` with `b = -a`, and equals
  the coroot element. This avoids introducing an arbitrary negation map or any new
  root-system construction.
- The root-sum bracket is quantified over `a b k : R` with `a + b = k`. It supplies a
  natural number `p` for which `b - p • a ∈ R` and every such natural number is at most
  `p`. This is precisely the maximum in the node, with no additional interval assertion.
  An integer `ε = 1 ∨ ε = -1` gives the coefficient `ε * (p + 1)`. The next clause
  separately gives zero bracket when the sum is nonzero and not a root.
- The existential W and `LieRingModule g W` / `LieModule ℚ g W` are the representation;
  its actual representing Lie homomorphism is `LieModule.toEnd ℚ g W`.
  `FiniteDimensional ℚ W` and `LieModule.IsFaithful ℚ g W` give finite dimension and
  injectivity of this homomorphism.
- `Λ : Submodule ℤ W`, `Submodule.IsLattice ℚ Λ`, and `Module.Free ℤ Λ` give a full
  finite-rank free abelian subgroup. `IsLattice` means finitely generated and rationally
  spanning; for a subgroup of a rational vector space, this is equivalent to the
  canonical scalar-extension map `ℚ ⊗[ℤ] Λ → W` being an isomorphism. Injectivity is
  the localization of a subgroup inclusion; surjectivity is rational spanning. This
  also gives the tensor order used in the node by symmetry.
- `Ω : Finset V` gives finiteness; `∀ μ ∈ Ω, μ ∈ P ∧ weightSpace ... ≠ ⊥` gives precisely
  integral weights with nonzero spaces. The spaces are Mathlib's ordinary simultaneous
  eigenspaces, whose membership is `∀ h, ⁅h,w⁆ = θ h μ • w`. Their internal direct sum
  is all W. `Submodule.span ℤ (Ω : Set V) = P` is the full-weight requirement.
- The second internal direct sum is inside Λ, of each ordinary weight space restricted
  to ℤ and pulled back by `Λ.subtype`. Its summands are exactly `Λ ∩ W_μ`; hence it
  asserts the integral decomposition, rather than only a rational decomposition.
- `IsNilpotent (LieModule.toEnd ℚ g W (e a))` says each root operator is nilpotent.
  The membership condition for every `a`, `m : ℕ`, and `w ∈ Λ` says precisely that
  `(m!)⁻¹ • ρ(e_a)^m` preserves Λ, including m = 0.
- When `R = ∅`, the final implication supplies `Subsingleton g` and a rational linear
  equivalence `ψ : W ≃ₗ[ℚ] ℚ` carrying Λ to the integer image in ℚ, and `Ω = {0}`.
  These identify the witnesses with the stated zero algebra, rational module, and
  integer lattice; H is then zero as a subalgebra of a subsingleton algebra.

Dependency declarations read and used:

- `Sheaf.LinearAlgebra.RootDatumLatticeEmbedding`:
  `RootDatumLattice.lattice_embedding`, `rootSpan`, `coroot`, `weightLattice` and their
  docstrings were read in full. Its explicit rational root-system and weight conditions
  are used as above, without requiring its stronger integral-datum input.
- Mathlib `Algebra.Lie.Basic`, `OfAssociative`, `Subalgebra`, and `Semisimple.Basic`:
  `LieRing`, `LieAlgebra`, `LieSubalgebra`, `LieRingModule`, `LieModule`,
  `LieModule.toEnd`, `LieModule.IsFaithful`, `LieAlgebra.HasTrivialRadical`, and
  `hasTrivialRadical_iff_no_solvable_ideals` provide the two Lie definition nodes.
- Mathlib `Algebra.Lie.Weights.Basic`: `LieModule.weightSpace` and its
  `mem_weightSpace` characterization were read; these are ordinary eigenspaces.
- Mathlib `Algebra.DirectSum.Module`: `DirectSum.IsInternal` and its internal-sum
  consequences; `Algebra.Module.Lattice`: `Submodule.IsLattice` (finite generation and
  rational span) and its freeness theorem. No private lattice notion is introduced.
- Proof imports are the four recorded supporting modules:
  `Sheaf.Algebra.Lie.RationalSerrePresentation` (`LieAlgebra.rationalSerrePresentation`),
  `Sheaf.Algebra.Lie.ChevalleyRootNormalization`
  (`LieAlgebra.exists_chevalley_basis_of_pinning`),
  `Sheaf.Algebra.Lie.RationalHighestWeightModules`
  (`LieAlgebra.exists_rational_highestWeight_module`), and
  `Sheaf.Algebra.Lie.KostantIntegralPBW`
  (`LieAlgebra.exists_kostant_integral_pbw_basis`). Their full statements and proof
  docstrings were read. The PID proof leaf is `Submodule.basisOfPid` in
  `Mathlib.LinearAlgebra.FreeModule.PID`.

Edge cases checked: empty roots force V = 0 by hspan and retain the node's particular
one-dimensional representation and singleton zero weight. No `Nonempty R`, positive rank,
or `Nontrivial g` is assumed. The full weight lattice is then zero but is generated by the
singleton zero weight. Zero can also be a weight in nonzero rank. For opposite roots the
sum bracket is separated from the nonzero-sum formulas. For a root sum the defining string
set is nonempty at p = 0 and finite, because the nonzero root has distinct natural multiples
and R is finite. The m = 0 divided power is the identity and preserves every subgroup.
For type A1, requiring full weight generation retains the fundamental weight rather than
allowing only the adjoint representation's even weights. The statement includes disconnected
root systems and every universe u; both finite-dimensional witnesses can be realized in u.

Sources checked: the local Milne PDF, printed pp.503--511, in particular the rational-field
extension on p.508, Chevalley basis paragraph and Theorem 23.71, admissibility and equation
(152) on p.510, and the fundamental-weight choice in Corollary 23.73 on p.511.

Searches (all msearch calls used Q47 and this item):

- `leanfinder`: "A rational semisimple Lie algebra with Chevalley basis admits a faithful
  representation with full weight lattice and integral lattice preserved by divided root
  powers". Eight hits: Geck construction, its Cartan and trivial radical, and linear-weight
  results. None constructs the requested full-weight faithful module with admissible lattice.
- `loogle`: `"Chevalley"`. Twelve hits, all for unrelated constructible-image complexity.
- `leansearch`: "Chevalley basis faithful representation admissible integral lattice divided
  powers". Eight hits, on divided-power structures in commutative rings and a Z-lattice basis.
  None is this simultaneous existence statement.
- `grep` through msearch: `Chevalley.basis|admissible.lattice|divided.power.*lattice`.
  One hit in `Mathlib/Algebra/Lie/Basis/Basic.lean`; read its definition and TODO, which
  explicitly says Chevalley bases remain to be defined. Its existing `LieAlgebra.Basis`
  is weaker and is not this statement.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for Chevalley, chevalley,
  AdmissibleRepresentation, and RationalRootSystem found the separate normalization,
  PBW, and straightening inputs and unrelated Chevalley theorems. No combined theorem.
- Exact node-id search in `lean/WeilConjectures` found no declaration. Exact proposed-name
  search in `dag/lean_names_upstream.json`, `WeilConjectures`, and `Sheaf` found none.
- Targeted Mathlib search for `IsLattice`, `IsFullLattice`, and `weightLattice` located
  the existing `Submodule.IsLattice` API used here.

No STATEMENT-DISPUTED issue was found. Compilation uses scompile.py only; the first pass
required classical decidable equality for internal direct sums, supplied with
`open Classical in` without adding any mathematical hypothesis.

## Second reading by Q47

A separate final rereading in this dispatcher worker compared the unchanged node and the
module clause by clause. No additional agent was started, as required by the assignment.
The explicit finite-spanning rational root axioms match the dependency's conventions.
The Cartan identification is in the dual direction stated in the node's next sentence,
and finite-dimensional duality gives the preceding direction. Simple coroots, not arbitrary
Cartan vectors, are the B entries. The maximum p is a natural maximum, not a root-pairing
chain coefficient assumed without identifying the pairing. W uses an actual Lie module,
so its representing map is linear and preserves brackets, and faithfulness means injectivity.
The rational and integral direct sums are separate, with the latter correctly inside Λ.
The lattice is finitely generated, free, and full. All weights are integral and nonzero
as spaces, with their integer span exactly P. Nilpotence, all divided powers, and the
specified empty-root witnesses are retained. The only elaboration repair was classical
decidable equality; it changes no hypothesis or conclusion.
