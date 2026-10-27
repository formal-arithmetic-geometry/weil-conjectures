## Worker report

The module `Sheaf.RingTheory.ArtinCompletedPolynomialTestRing` states
`AlgebraicGeometry.ArtinDeformation.completedPolynomial_testRing` with `sorry`.
The two helper declarations merely abbreviate the literal Mathlib completion and
name its canonical R-algebra inclusion. They belong to this node's construction;
they introduce no independent mathematical notion and contain no postponed data.
The node changes only in `lean`; its natural-language statement is unchanged.

Sources read: Stacks `formal-defos.tex`, Tag 06SM, `lemma-exists-smooth`, especially
its choice of a polynomial algebra surjecting onto k, its completion paragraph,
and its final smoothness argument; Tag 0316 and the recorded completion dependency.
The latest blueprint's `det-thm-sf-ctf-stability-direct-images.proof.md`, clause (3),
was read for the inherited route. The node is the supporting polynomial-completion
lemma, not that blueprint unit's own statement.

Hypothesis and clause correspondence:

- Commutative Noetherian R: `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- Field of finite type over R: `(k : Type u) [Field k] [Algebra R k]
  [Algebra.FiniteType R k]`. This is finite type as an algebra, precisely the
  node's hypothesis, rather than finite generation merely as a field extension.
- Both finite variable blocks, including zero: `(s d : ℕ)` and
  `MvPolynomial (Fin s ⊕ Fin d) R`. The left summand is Y; the right is X.
- R-algebra surjection to k: `e : ... →ₐ[R] k` and `he : Function.Surjective e`.
- Vanishing of every distinguished X: `hX : ∀ i : Fin d,
  e (MvPolynomial.X (Sum.inr i)) = 0`.
- q is `RingHom.ker e.toRingHom`; S is `PolynomialTestCompletion e`, definitionally
  `AdicCompletion q P`, the compatible inverse-limit sequence ring. The inclusion
  `polynomialTestInclusion e` is `IsScalarTower.toAlgHom R P S`; it is the actual
  canonical completion map, with the inherited R-algebra structures.
- Locality is the existential `∃ (_ : IsLocalRing S), ...`. Within its scope the
  same local-ring structure is used in every maximal ideal and residue field.
- Noetherianity and completeness: `IsNoetherianRing S` and
  `IsAdicComplete (IsLocalRing.maximalIdeal S) S`.
- The stated maximal ideal: equality of `IsLocalRing.maximalIdeal S` with
  `q.map (polynomialTestInclusion e).toRingHom`.
- Canonical residue field: an R-algebra equivalence `ResidueField S ≃ₐ[R] k`
  whose composite with `IsLocalRing.residue S` equals `AdicCompletion.kerProj he`
  on every element. The latter is Mathlib's canonical projection, formed by
  evaluation at level one followed by the first isomorphism theorem for e;
  it restricts to e on P. Thus the marking is fixed, not an arbitrary isomorphism.
- Every positive quotient: `∀ n : ℕ, 1 ≤ n → ...`, with augmentation ρ on
  `S ⧸ maximalIdeal S ^ n` satisfying `IsTestAlgebra R k ρ`, and with composite
  along the quotient map equal to the same canonical `kerProj he`.
- Every intervening ideal: `∀ L`, existence of positive n with `m^n ≤ L`, and
  `L ≤ m`, imply exactly the analogous `IsTestAlgebra` assertion for `S ⧸ L`.
  `IsTestAlgebra` states local and Artinian, surjectivity of ρ, and that its kernel
  is the maximal ideal. These are precisely local Artinianity with the specified
  residue field k. The additional equation fixes the induced canonical marking.
- Restriction bijection for each `A : TestCategory R k`: `Set.BijOn` of
  `fun h ↦ h.comp (polynomialTestInclusion e)`, from the set defined by
  `IsLocalHom h ∧ (residue A).comp h = kerProj he` onto the set defined by
  `(residue A).comp f = e`. No extension map is added as hypothesis.
- Lifting through every test surjection: quantified `π : B ⟶ A` and
  `Function.Surjective (map π)`, followed by every local marked h, give a local
  marked g with `(map π).comp g = h`. There is no small-extension restriction.
- Every local R-map to a test, even one not preserving the marking: the final
  quantifier assumes only `IsLocalHom h`. It gives `@Continuous` with both
  topological structures explicitly the maximal ideals' `adicTopology`, and a
  positive n and actual quotient R-algebra map g whose composite is h.

Dependency declarations reused (their signatures and docstrings were read):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal finite
  generation characterization, for `def-weil-pbc-noetherian-ring`.
- `Mathlib.Algebra.Field.Defs`: `Field`, the Mathlib match of `def-weil-field`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, its definition through
  `Algebra.FiniteType`, and `finiteType_algebraMap`, for
  `def-weil-pbc-finite-type-algebra`. The theorem has an explicit algebra, so
  `Algebra.FiniteType R k` is precisely the algebra-map specialization.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval`, for
  `def-weil-pbc-mv-polynomial-ring` (evaluation is used in the proof plan).
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, the completion algebra structure, `AdicCompletion.kerProj`,
  and its restriction formula `kerProj_of`.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`:
  `AlgebraicGeometry.ArtinDeformation.IsTestAlgebra`, `TestCategory`, `ring`,
  `testLocal`, `testArtinian`, `residue`, and `map`. The local Artinian quotient
  augmentations use this existing predicate rather than a duplicate definition.
- Proof plan: `Algebra.FiniteType.isNoetherianRing` (Mathlib finite type);
  `AdicCompletion.isNoetherianRing` in
  `WeilConjectures.RingTheory.AdicCompletionNoetherian`;
  `AdicCompletion.isAdicComplete`, `pow_smul_top_eq_ker_eval` in Mathlib's
  completion completeness module and `eval_surjective` in its basic module;
  `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing` in
  `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`; the Artinian-to-Noetherian
  instance and `isArtinianRing_iff_isNilpotent_maximalIdeal` in
  `Mathlib.RingTheory.HopkinsLevitzki`. All their modules are imported directly
  or through the public test-category dependency, with completion completeness,
  the quotient Artinian criterion and completion Noetherianity plain imports.

Edge cases checked before writing and again against the signature:

- s=d=0 is allowed (including R=k and q=0); neither block requires nonemptiness.
- s=0 or d=0 separately are allowed. The vanishing condition is vacuous for d=0.
- Exponent one is retained, giving the marked residue field itself; exponent zero
  is excluded exactly where the node excludes it, since S/m^0 is the zero ring.
- L=m is allowed. If m=0, L=0 is allowed and the quotient is the field S.
- A=k and identity test surjections are included. Any surjection is allowed,
  regardless of whether its kernel is small.
- The final continuity and factorization clauses assume no residue identity.
- No characteristic or separability restriction occurs. The base need not be
  local and the polynomial ring is not assumed local or localized first.
- R, k, the completion and all test rings use the common universe of the recorded
  test-category interface; tests do not range over a smaller independent universe.

Searches (machine-readable results are also in the sandbox searches.jsonl):

- msearch leanfinder: "Completion of a polynomial algebra at the kernel of a
  surjection to a field is complete Noetherian local and local maps to Artinian
  rings lift across surjections". Eight constituent results: kerProj and its
  surjectivity, formally smooth lift lemmas, completion evaluation surjectivity,
  henselian completeness. No theorem gives the complete assertion.
- msearch loogle: `AdicCompletion, IsLocalRing`. Twelve results, all completion
  locality/residue results for an already local source ring. P here need not be
  local, and these do not give the marked Artinian-map bijection and lifting.
- msearch grep, Mathlib RingTheory: `completedPolynomial|completed_polynomial|
  AdicCompletion.*IsLocalRing|IsLocalRing.*AdicCompletion`. Five explanatory
  matches in `AdicCompletion/LocalRing.lean`; none is this statement.
- msearch leansearch: "Local residue preserving algebra maps from the completion
  of a polynomial ring to Artinian local algebras form a formally smooth functor".
  Eight results on formal smoothness, including multivariable polynomials; none
  states the completion theorem and all its clauses.
- rg in the project Sheaf and WeilConjectures sources for completed polynomial,
  polynomial-test names, the node id, and Tag 06SM. Found
  `Algebra.completedPolynomial_lift_calculus`, which instead starts over a field,
  localizes at a maximal ideal, treats complete Noetherian targets, and restricts
  lifting to square-zero kernels; it is not the present assertion. The downstream
  StackVersal module mentions this node only in proof documentation.
- rg in both project roots and `dag/lean_names_upstream.json` found no collision
  for `PolynomialTestCompletion`, `polynomialTestInclusion`, or
  `completedPolynomial_testRing`.

No statement dispute, no new nodes, and no dependency modules. The full seven-step
natural-language proof of the node is retained in the theorem docstring. The only
postponed theorem is this node's theorem. Server scompile passed both sandbox and
library compilation with no warnings or errors after making the bundled quotient
algebra explicit in the `IsTestAlgebra` applications.

## Second reading by Q110

No second reading by another worker: this task is dispatched directly and prohibits
starting other agents. The maintainer supplies the independent review. A final
self-check compared every hypothesis and clause above against the unchanged node
and the compiled signature.
