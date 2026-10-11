## Worker report

The module `Sheaf.NumberTheory.Padics.LatticeStabilizerOpen` states
`Padic.lattice_stabilizer_isOpen`, with proof `sorry`. It introduces no new definitions
and changes only the item's `lean` record. Its docstring carries all three DAG proof
steps, including the DVR-freeness dependency and the explicit matrix neighborhoods.

Hypothesis and conclusion correspondence:

- A prime ℓ: `(l : ℕ) [Fact l.Prime]`.
- A finite field extension E/ℚ_ℓ: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`.
- Its ℓ-adic topology: the local instance
  `letI : NormedField E := spectralNorm.normedField ℚ_[l] E` uses the spectral
  absolute value extending the p-adic absolute value. This is the same absolute value
  used by the dependency's valuation-ring definition.
- A finite-dimensional E-vector space V: `∀ (V : Type v) [AddCommGroup V]
  [Module E V] [FiniteDimensional E V] [TopologicalSpace V]`.
- The product topology in an E-basis: the hypothesis
  `∃ b : Module.Basis (Fin (Module.finrank E V)) E V,
  Continuous b.equivFun ∧ Continuous b.equivFun.symm` says the basis coordinate
  equivalence is a homeomorphism to the finite product of copies of E. Existence in
  one basis is equivalent to the node's description in any basis: a change of basis
  and its inverse are finite matrices, hence continuous for the product topology.
  This introduces no auxiliary norm on V and excludes no topology described in the node.
- An O_E-submodule Λ₀ contained in V: `Λ : Submodule
  (Padic.coefficientExtensionIntegers l E) V`. The scalar action is the canonical
  restriction of the E-action to this subring, not an independent module structure.
- Finite generation: `Λ.FG`.
- Spanning over E: `Submodule.span E (Λ : Set V) = ⊤`.
- GL_E(V): `V ≃L[E] V`. Under the basis-coordinate topology hypothesis every E-linear
  map is continuous (its finite matrix acts continuously on the finite product), as
  is the inverse of each automorphism. Thus this bundled type is exactly the full
  group of linear automorphisms, not a restricted subgroup.
- The stated compact-open topology: the local topology instance on `V ≃L[E] V` is
  `TopologicalSpace.induced (fun g : V ≃L[E] V ↦ (g : C(V, V))) inferInstance`.
  `ContinuousMap.compactOpen` from `Mathlib.Topology.CompactOpen` is the instance on
  `C(V,V)`. Inducing directly from continuous maps is the same as inducing via the
  subspace of continuous linear maps, by composition of induced topologies. In
  particular this does not inadvertently substitute Mathlib's bounded-convergence
  topology on continuous linear maps for the topology explicitly specified by the node.
- Exact stabilization u(Λ₀)=Λ₀: `g '' (Λ : Set V) = (Λ : Set V)`; equality, not merely
  containment, is required. This subset is the stabilizer subgroup under composition.
- Openness of that subgroup: `IsOpen {g : V ≃L[E] V | g '' (Λ : Set V) = (Λ : Set V)}`.

Dependency used: `Sheaf.NumberTheory.Padics.CoefficientExtension`, declaration
`Padic.coefficientExtensionIntegers`; read its full signature and docstring. The
module also uses Mathlib's `spectralNorm.normedField`, `Module.Basis.equivFun`,
`ContinuousLinearEquiv`, `Submodule.FG`, `Submodule.span`, `TopologicalSpace.induced`,
and `ContinuousMap.compactOpen`. No dependency module is needed.

Edge cases checked: V=0 has a basis indexed by `Fin 0`, the unique lattice is finitely
generated and spans, and its stabilizer is the whole one-element GL, which is open.
The zero submodule in nonzero V fails the spanning hypothesis, exactly as required.
No nonzero-dimension, nonempty-index, freeness, chosen basis of the lattice, fixed
extension degree, or restriction on the prime was added. The universes u and v are
explicit and independent. Arbitrarily scaled lattices satisfy the same hypotheses;
no standard-coordinate lattice was substituted for Λ. Scalar actions are canonical.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder "The stabilizer of a finitely generated spanning lattice
  over the integers of a finite extension of a p-adic field is open in the general
  linear group"`: eight hits, including `stabilizer_isOpen` for actions on discrete
  spaces and Krull-topology fixing-subgroup results; none states this theorem.
- `msearch.py ... loogle "IsOpen, Submodule, ContinuousLinearEquiv"`: no hits.
- `msearch.py ... grep "stabilizer.*[Oo]pen|[Oo]pen.*stabilizer" Topology`: five hits,
  all for continuous actions on discrete spaces in `Topology/Algebra/MulAction.lean`.
  These require an action on a discrete lattice space that is not supplied here.
- `msearch.py ... leansearch "stabilizer lattice open p-adic general linear group"`:
  unavailable (Internal Server Error); no match verdict inferred from unavailability.
- `rg -n "lem-pod-lattice-stabilizer-open|lattice.*stabilizer|stabilizer.*lattice"`
  on `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository `lean/Sheaf`:
  no existing declaration. Search for the intended full name in Mathlib, the source
  repository, `dag/lean_names_upstream.json`, and `lean/Sheaf`: no collision.
- Read `Mathlib.Topology.CompactOpen`: `ContinuousMap.compactOpen` is explicitly
  generated by compact-domain/open-codomain mapping conditions. Read
  `Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap`: its default topology
  is bounded convergence; avoided using it as the compact-open topology.

Source checked online because the local lecture PDF is absent:
[Stanford Lecture 19](https://math.stanford.edu/~conrad/Weil2seminar/Notes/L19.pdf),
Proposition 1.1.9, second bullet, states that GL(Λ₀)≅GL_n(O_E) is open in GL_n(E).
This passage is on printed page 3 (PDF page index 2); the node's source record says
p. 2. This pagination discrepancy does not affect its statement or proof.

Validation: server `scompile.py C1 lem-pod-lattice-stabilizer-open` compiled the
module cleanly, with no warnings. `deliver2.py C1 lem-pod-lattice-stabilizer-open
--no-push` printed OK: compiles and passes preflight except the second reading,
which the independent reader supplies. Nothing was pushed.

## Second reading by C1

I independently opened the sandbox node and module, the sole statement-dependency
node `def-weil-l-adic-coefficient-extension`, its recorded module
`Sheaf.NumberTheory.Padics.CoefficientExtension`, and the defining witness theorem
`Padic.extension_integers_dvr` in `ExtensionIntegersDvr.lean`.

Object, hypothesis and conclusion checklist, in the node's order:

- Prime ell: `l : ℕ` and `[Fact l.Prime]`. Exact; includes every prime, including 2.
- Finite extension E/Q_ell: `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]`. Exact; no Galois, ramification or degree restriction.
- The ring O_E: `coefficientExtensionIntegers l E`, used as the scalar ring of
  `Λ : Submodule ... V`. Exact dependency notion, not a private ring or an
  independently chosen action. Its defining witness states
  `∀ x : E, x ∈ O ↔ abv x ≤ 1`; the absolute value supplied is the spectral
  absolute value extending the p-adic one. Its data is a subring chosen from a
  named theorem, not data defined by `sorry`.
- The topology on E: `letI : NormedField E := spectralNorm.normedField ℚ_[l] E`.
  Exact. I read the Mathlib definition: its norm is `spectralNorm ℚ_[l] E`,
  the same function used in the dependency's `spectralMulAlgNorm` absolute value.
- Finite-dimensional E-vector space V: `V : Type v`, `[AddCommGroup V]`,
  `[Module E V]`, `[FiniteDimensional E V]`. Exact; the two universes are independent.
- Its product topology in any E-basis: `[TopologicalSpace V]` together with
  `∃ b : Module.Basis (Fin (Module.finrank E V)) E V,
  Continuous b.equivFun ∧ Continuous b.equivFun.symm`. Exact: both directions
  specify the topology, rather than merely continuity of coordinates. Every
  finite-dimensional space has such an indexed basis. A change between bases
  acts by finite sums of scalar multiples on E^n, and its inverse does too;
  hence this condition in one basis is equivalent to the node's condition in any.
- Lattice contained in V: `Λ : Submodule (coefficientExtensionIntegers l E) V`.
  Exact; the subring scalar action is the restriction of the given E-action.
- Finite generation: `Λ.FG`. Exact; not a chosen basis or a free-module hypothesis.
- Spanning V over E: `Submodule.span E (Λ : Set V) = ⊤`. Exact; the span is over
  E, not over the integer ring.
- GL_E(V): `V ≃L[E] V`. Exact under the preceding coordinate-topology condition:
  every E-linear map has a finite matrix, whose coordinate functions are
  continuous. Both an automorphism and its inverse are therefore continuous.
  I opened Mathlib's `ContinuousLinearEquiv` structure; it adds exactly these
  two continuity proofs to a linear equivalence, without further instances.
- Stabilizer: `{g : V ≃L[E] V | g '' (Λ : Set V) = (Λ : Set V)}`.
  Exact image equality, which already defines the subgroup (identity,
  composition and inversion preserve the equality); no weaker inclusion.
- Its openness for the specified topology: the local automorphism topology is
  `TopologicalSpace.induced (fun g : V ≃L[E] V ↦ (g : C(V, V))) inferInstance`,
  followed by `IsOpen` of that stabilizer. Exact. I opened
  `Mathlib.Topology.CompactOpen`: the instance on `C(V,V)` is generated by
  compact-set/open-set mapping conditions. Restricting first to continuous
  linear maps and then to equivalences gives the same induced topology by
  composition. No operator-norm topology is assumed.

The binders quantify over every such E, V and Λ before asserting openness.
There is no hidden topology compatibility, Noetherian, normed-space, positive
dimension or characteristic hypothesis. All universes and variables are bound.

Source reading: independently opened
[Stanford Lecture 19](https://math.stanford.edu/~conrad/Weil2seminar/Notes/L19.pdf),
Proposition 1.1.9, second bullet, on printed page 3. The matrix-lattice assertion
there applies to any lattice in a finite extension of Q_ell. The geometrically
connected scheme and its fundamental group belong to the surrounding sheaf
equivalence, not to this standalone matrix assertion, so they are correctly
absent here. The node says p. 2, whereas the passage is on printed p. 3; this
is a source-location discrepancy only. The source field and lattice agree with
the node. The item's statement has no `statement_change` and needs no correction.

Edge cases: V=0 gives `Fin 0`, the empty coordinate product and the unique
automorphism; its lattice stabilizer is the entire group. The zero lattice in
a nonzero V is excluded exactly by the spanning condition. The basis condition
excludes no dimension-zero or empty-index case. E remains a field of
characteristic zero through its Q_ell algebra; no prime is excluded. Empty
schemes and coefficient-quotient n=0 do not occur in this statement. No chosen
standard lattice or fixed extension degree is substituted for the arbitrary
lattice and extension.

Independent searches (2026-10-11), using other terms than the first reader:

- `msearch.py C1 lem-pod-lattice-stabilizer-open leanfinder
  "integer lattice automorphism group open subgroup local field"`: eight hits,
  consisting of arithmetic-subgroup discreteness, number-field integer/unit
  lattices, and Galois fixing-subgroup openness. None is this assertion.
- `msearch.py C1 lem-pod-lattice-stabilizer-open loogle "IsOpen, LinearEquiv"`:
  zero hits.
- `msearch.py C1 lem-pod-lattice-stabilizer-open leansearch
  "open subgroup preserving an integral lattice in a finite dimensional p-adic vector space"`:
  service unavailable (Internal Server Error), recorded without a no-match inference.
- `rg -n -i 'lattice.*(stabili|open)|stabili.*lattice|generalLinearGroup.*isOpen|isOpen.*generalLinearGroup|lattice_stabilizer_isOpen'`
  over Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, repository
  `lean/Sheaf` and `dag/lean_names_upstream.json`: only unrelated topological
  lattices of open sets and the real Weierstrass lattice complement appeared;
  no existing assertion or declaration-name collision.

No H3-H6 or H8-H9 mismatch found. The module has one named theorem with a
`sorry` proof and no definitions or additional assertions. Its docstring
follows all three node proof steps: DVR finite freeness, the matrix criterion
and A+M_n(m_E) neighborhood, then continuity of entries and openness of m_E.
The dependency import supplies O_E; the other imports supply equivalences,
compact-open topology and basis coordinates. No new definition node or
dependency module is needed. I left the correct Lean and node unchanged;
the second reading adds only this independent review.
