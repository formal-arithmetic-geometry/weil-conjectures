## Worker report

The module `Sheaf.RingTheory.TotallyRamifiedUniformizerPresentation` states
`IsDiscreteValuationRing.exists_uniformizer_polynomial_presentation`, with its proof
postponed by `sorry`. There are no definitions, auxiliary theorems, new nodes, dependency
repairs, or changes to the informal statement. The node copy changes only `lean`.

Source read: Stacks Project, `literature/stacks-project/more-algebra.tex`, Tag 09ER,
`lemma-weakly-unramified-goes-up-along-totally-ramified`, especially the first proof
paragraph (lines 34502 onward). This gives generation by the chosen uniformizer, the monic
polynomial with the indicated divisibility conditions, and degree equal to the extension
degree. I also read the current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`:
its current paragraph (3) does not assert this auxiliary algebra lemma, consistently with
the node's historical-support provenance. The statement being formalized is the reviewed
DAG node's statement, not an alteration of the unit.

Hypothesis correspondence:

- The complete DVR `R` is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [IsAdicComplete (maximalIdeal R) R]`. Completeness uses
  precisely the maximal-ideal-adic, Hausdorff notion, rather than an unrelated topology.
- Its fraction field is `(F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]`.
- The finite separable extension is `(E : Type w) [Field E] [Algebra F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]`. The induced `R`-algebra structure is
  `[Algebra R E] [IsScalarTower R F E]`; this specifies compatibility with `R -> F -> E`.
- Degree `n >= 1` is `(n : ℕ) (hn : 1 ≤ n) (hdegree : Module.finrank F E = n)`.
  `FiniteDimensional` means finite vector-space dimension, not finite cardinality.
- The given subring `S` of `E` containing `R` is `(S : Subalgebra R E)`, with
  `(hS : S = integralClosure R E)` identifying it with the actual integral closure.
  This is an equality of subalgebras inside the given field, not an arbitrary choice of
  a normalization map or an abstract ring with an unspecified embedding.
- `S` is a DVR by `[IsDiscreteValuationRing S]`; its domain structure is inherited from
  its inclusion in the field `E`, so no redundant domain binder is supplied.
- Locality is `[IsLocalHom (algebraMap R S)]`. For local rings, reflection of units is
  equivalent to the maximal-ideal inverse-image condition spelled out in the node.
- The induced residue map is an isomorphism by
  `hresidue : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R S))`.
  This is the canonical residue homomorphism of the specified inclusion, not an
  unrelated isomorphism of the two residue fields.
- Total ramification's ideal equality is
  `hramification : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ n`.
  `Ideal.map` gives the extended ideal `m_R S`.
- The universal choices of uniformizers are `(pi : R)` and `(t : S)`, with
  `hpi : maximalIdeal R = Ideal.span {pi}` and
  `ht : maximalIdeal S = Ideal.span {t}`. Neither uniformizer is chosen by the theorem.

Conclusion correspondence:

- `∃ P : R[X], P.Monic ∧ P.natDegree = n` says exactly that
  `P = X^n + sum_{i<n} C(a_i)*X^i`, taking `a_i = P.coeff i`. Conversely every displayed
  polynomial of the node is monic of natural degree `n`; no additional condition on
  its coefficients is introduced.
- `∀ i : ℕ, i < n → P.coeff i ∈ Ideal.span {pi}` gives all coefficient conditions
  `a_i ∈ pi R`. In particular it includes `a_0 ∈ pi R`, since `hn` implies `0 < n`.
- `P.coeff 0 ∉ Ideal.span {pi ^ 2}` gives the remaining `a_0 ∉ pi^2 R` condition.
- The first existential gives an `R`-algebra equivalence
  `(R[X] ⧸ Ideal.span {P}) ≃ₐ[R] S`. Its equation for every `Q : R[X]` says that
  composing with the quotient map is exactly `aeval t`. Thus it is precisely the
  isomorphism induced by evaluation required by the node.
- The second gives an `F`-algebra equivalence
  `(F[X] ⧸ Ideal.span {P.map (algebraMap R F)}) ≃ₐ[F] E`. Its equation for every
  `Q : F[X]` similarly specifies evaluation at the image `(t : E)` of the same `t`.
  Mapping the coefficients of `P` to `F` makes the node's second quotient well-typed.
  Algebra equivalences express the base-preserving quotient presentations in the source.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`, in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`. The maximal-ideal-generator form is
  used literally in the signature.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete` in
  `Mathlib.RingTheory.AdicCompletion.Basic`; its docstring and class signature were read.
- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`, reexported by
  the statement's polynomial/field imports. The extension maps are `algebraMap`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` in
  `Mathlib.FieldTheory.Separable`; its class signature quantifies over every element,
  and `IsSeparable.isIntegral` verifies that algebraicity is included.
- `def-weil-pbc-integral-closure`: `integralClosure` in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`; its carrier is exactly integral
  elements, as required by `hS`.
- `def-weil-polynomial-ring`: `Polynomial` in `Mathlib.Algebra.Polynomial.Basic`,
  reexported by `Mathlib.Algebra.Polynomial.AlgebraMap`.
- Additional standard interfaces are `IsFractionRing` in
  `Mathlib.RingTheory.Localization.FractionRing`, `FiniteDimensional` in
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, the canonical residue-field map in
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`, and quotient algebras in
  `Mathlib.RingTheory.Ideal.Quotient.Operations`.

The proof dependencies are Mathlib leaves. Their modules are included as plain proof
imports when not already public statement imports:
`Mathlib.RingTheory.PrincipalIdealDomain` (Noetherian/PID),
`Mathlib.RingTheory.DedekindDomain.IntegralClosure` (`IsIntegralClosure.finite`),
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` (normality),
`Mathlib.RingTheory.Localization.Integral`
(`integralClosure.isFractionRing_of_finite_extension`), and
`Mathlib.RingTheory.LocalRing.Module` (`IsLocalRing.map_mkQ_eq_top`). Uniformizer
factorization `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` is already available
from the public DVR import. The theorem docstring records all eight proof steps and the
DAG inputs, including the least-order argument, the two applications of monic division,
and the fraction-field denominator argument.

Edge cases checked before drafting and again against the signature:

- `n = 1`: the extension and integral closure identify with the base; for any chosen
  uniformizer the relation has the form `X - t`. Its constant coefficient is divisible
  by `pi` but not `pi^2`, even if the chosen uniformizers differ by a unit.
- `n = 0` is excluded by exactly the stated `n >= 1`; no accidental positive-degree
  assumption is needed beyond it.
- A zero uniformizer cannot satisfy the maximal-ideal equality in a DVR. Fields and the
  zero ring cannot satisfy the DVR/domain assumptions.
- Every uniformizer of `S`, including any unit multiple, is quantified universally;
  there is no preferred generator or existence-only weakening.
- Equal characteristic, mixed characteristic and wild ramification are all covered.
  No perfect-residue-field, characteristic-zero or tame-degree hypothesis is added.
- `u`, `v`, `w` are independent explicit universes for the two fields and base ring;
  `S` is the subalgebra inside `E` and imposes no equality of these universes.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py ... leanfinder "A uniformizer of the integral closure of a complete DVR in
  a totally ramified finite separable field extension generates the ring and has
  Eisenstein minimal polynomial"`: eight hits. The closest are
  `mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt` and its power version;
  reading their signatures shows they assume a power basis and Eisenstein minimal
  polynomial, rather than prove the required presentation. Uniformizer-generator hits
  characterize the maximal ideal only.
- `msearch.py ... loogle "IsDiscreteValuationRing, Polynomial.IsEisensteinAt"`: zero hits.
- `msearch.py ... grep "IsEisensteinAt|totallyRamified|uniformizer" RingTheory`: 25 hits
  in Eisenstein and valuation files, none with the required conclusion.
- `msearch.py ... leansearch "A totally ramified finite separable extension of complete
  discrete valuation fields has integral closure generated by any uniformizer with an
  Eisenstein polynomial"`: eight hits concerning integral closure or the same
  Eisenstein assumptions; no exact match.
- `rg -n` in `lean/WeilConjectures` and `lean/Sheaf` for `totally.ramified`,
  `uniformizer.*presentation`, `uniformizer.*[Ee]isenstein`, and the proposed declaration
  name: no matching general presentation theorem. The upstream Laurent-series file
  concerns special Artin--Schreier polynomials, not this statement.
- The item id has no occurrence in `lean/WeilConjectures`; the proposed declaration name
  also has no occurrence in `dag/lean_names_upstream.json` or the library.

No statement fault or mathematical dispute was found. Compilation with the prescribed
`scompile.py Q132 lem-sfb-totally-ramified-uniformizer-presentation <file>` passed in
both sandbox and actual module mode (2.9 s and 2.6 s), with no errors or unexpected warnings.

## Second reading by Q132

I reread the complete node, source paragraph and final Lean signature after compilation.
This is a second pass by the assigned worker, not a claim of a separate reviewer; the
brief prohibits starting another agent, and the maintainer supplies independent review.
The checks matched completeness to the maximal ideal, the finite separable extension to
`FiniteDimensional` plus `Algebra.IsSeparable`, and the degree to the specified `n`. The
inclusion of `S` really is the integral closure in the same `E` by `hS`; the algebra tower
makes its map from `R` the given one. The local-map and residue-isomorphism assumptions
refer to that inclusion. The ramification equality has the correct direction and exponent.
Both uniformizers are arbitrary maximal-ideal generators. Monicity and natural degree
reproduce the displayed polynomial, with constant-term membership supplied by the
all-coefficients condition at zero and `hn`. Both equivalences are explicitly evaluation
maps, including the coefficient base change in the second quotient. No mismatch was
found and no correction or extra node was needed. All variables and universes are bound
explicitly, `autoImplicit` is disabled, and the only postponed declaration is the named
main theorem with the node's eight-step proof plan.
