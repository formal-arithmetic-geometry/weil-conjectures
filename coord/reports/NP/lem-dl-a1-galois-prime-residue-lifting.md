## Worker report

The module `Sheaf.FieldTheory.GaloisPrimeResidueLifting` states
`Ideal.galois_prime_transitivity_and_residue_lifting`, with one `sorry` and no
new definitions. The node statement, dependencies, and proof remain unchanged.
The source is Stacks Project, More on Algebra, Tag 0BRK,
`lemma-one-orbit-geometric-galois`, read in `literature/stacks-project/more-algebra.tex`
at lines 32777–32865. The node requests part (1) and the surjectivity clause of
part (2), without the additional algebraic-normal conclusion of the source.
The theorem docstring carries all six steps of the node's profinite/localization proof.

Hypotheses and objects, clause by clause:

- The normal domain R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R]`. This uses exactly the normal-domain specialization
  recorded by `def-weil-pbc-normal-ring`.
- F is its fraction field through `(F : Type v) [Field F] [Algebra R F]
  [IsFractionRing R F]`. A chosen model of the fraction field is allowed; no
  particular presentation is required.
- The extension E/F is `(E : Type w) [Field E] [Algebra F E] [IsGalois F E]`.
  `IsGalois` consists of `Algebra.IsSeparable` and `Normal`. The former implies
  algebraicity and the latter says each minimal polynomial splits. Neither
  finite degree nor finite Galois group is assumed.
- `[Algebra R E] [IsScalarTower R F E]` specifies the composite R-algebra
  structure, rather than a second independent embedding. These are compatible
  structure data always supplied by composition, not an added mathematical restriction.
- S is literally Mathlib's `integralClosure R E`. G is `E ≃ₐ[F] E`.
  Its Mathlib action on the integral closure restricts its action on E:
  `integralClosure.coe_smul` identifies the underlying element. Scalar
  commutation along R → F → E is provided by Mathlib's
  `AlgEquiv.apply_smulCommClass`. No arbitrary action is an assumption.
- Clause (1) quantifies over `s s' : Ideal (integralClosure R E)` with both
  prime instances. The antecedent `s.under R = s'.under R` is exactly equal
  contraction to R. The conclusion `∃ g : E ≃ₐ[F] E, g • s = s'` uses the
  standard pointwise ideal action, the ideal image under the restricted g.
- Clause (2) quantifies over every prime s and every ring equivalence
  `α : s.ResidueField ≃+* s.ResidueField`. The base prime is `s.under R`.
  `Ideal.ResidueField.map (s.under R) s (algebraMap R (integralClosure R E)) rfl`
  is the canonical embedding of its residue field. The contraction equality
  required by this map is definitional; `rfl` supplies it.
- The equality `α.toRingHom.comp (Ideal.ResidueField.map ...) =
  Ideal.ResidueField.map ...` says α fixes that entire embedded base field.
  A ring automorphism with this equality is precisely a base-field algebra
  automorphism; the statement does not assume α preserves S/s or is induced
  by an automorphism of S.
- The conclusion supplies g with `g • s = s` and, for every b in S,
  `α (algebraMap S s.ResidueField b) = algebraMap S s.ResidueField (g • b)`.
  This is exactly the induced residue-field action. Mathlib's
  `IsFractionRing (S ⧸ s) s.ResidueField` instance identifies this field with
  Frac(S/s). Every element is a fraction of images of elements of S, so
  equality on these images implies equality everywhere, by preservation of
  division. This is a generator formula for the whole field action, not a
  quotient-ring-only lifting statement. The stabilizer equality ensures the
  restriction induces a quotient automorphism, hence a fraction-field automorphism.

Dependency declarations used and read with their docstrings/signatures:

- `def-weil-pbc-normal-ring`: `IsIntegrallyClosed` in
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, together with `IsDomain`.
- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` in
  `Mathlib.FieldTheory.Separable`, through `IsGalois` in
  `Mathlib.FieldTheory.Galois.Basic`. Read `Normal` in
  `Mathlib.FieldTheory.Normal.Defs` and its splitting field.
- `def-weil-pbc-integral-closure`: `integralClosure` and its restricted action in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
- `Ideal.ResidueField`, `Ideal.ResidueField.map`, its formula on algebra maps,
  and the fraction-ring instance are the existing Mathlib constructions in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`.

All available proof dependencies are imported without `public`: the Krull
inverse limit (`InfiniteGalois.continuousMulEquivToLimit`,
`Mathlib.FieldTheory.Galois.Profinite`), finite group limits
(`ProfiniteGrp.limit`, `ProfiniteGrp.ofFiniteGrp`,
`Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic`), fixed fields
(`InfiniteGalois.fixedField_fixingSubgroup`,
`Mathlib.FieldTheory.Galois.Infinite`), profinite invariant rings
(`Algebra.IsInvariant.isIntegral_of_profinite`,
`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`,
`Ideal.Quotient.stabilizerHom_surjective_of_profinite`,
`Mathlib.RingTheory.Invariant.Profinite`), and localization/quotient comparison
(`IsLocalization.isPrime_iff_isPrime_disjoint`, `IsLocalization.map_under`,
the quotient localization instance, `Mathlib.RingTheory.Localization.Ideal`;
`IsLocalization.algEquiv`, `Mathlib.RingTheory.Localization.Basic`).
The two normal-ring/integral-closure proof dependencies are already public
statement imports. No proof-dependency import was omitted for a cycle.

Edge cases checked: E = F (trivial Galois group), R a field, the zero prime,
nonmaximal primes (the residue object is the fraction field, not just S/s),
identity α, infinite Galois degree, and arbitrary characteristic. There is no
residue separability assumption. The zero ring is correctly excluded by
`IsDomain R`. The three universe variables u, v, w are independent and explicitly
bound. All other variables are explicit; `autoImplicit` is false.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`: “For a possibly infinite Galois extension of the
  fraction field of a normal domain the Galois group is transitive on primes of
  the integral closure and lifts all residue field automorphisms” returned eight
  hits, including `Ideal.exists_comap_galRestrict_eq`, finite-group pretransitivity,
  and `Algebra.isInvariant_of_isGalois'`. These use finite group/extension
  hypotheses or only supply ingredients.
- `msearch.py ... loogle`: `IsFractionRing.stabilizerHom_surjective, galRestrict`
  returned zero hits. `Ideal.Quotient.stabilizerHom` returned seven hits,
  including the finite and profinite quotient-automorphism lifting theorems.
- `msearch.py ... leansearch`: “For an infinite Galois extension of the fraction
  field of an integrally closed domain the stabilizer of a prime of the integral
  closure surjects onto the residue field automorphism group” returned eight
  hits. The profinite hit concerns automorphisms of B/Q, and the generic
  fraction-field lifting theorem in `Invariant.Basic` assumes a finite group.
- `msearch.py ... grep`: `stabilizerHom|exists_smul_of_under_eq` in
  `RingTheory/Invariant` returned eleven relevant hits. Read the finite and
  profinite signatures, not merely the search descriptions.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node id, the new theorem name, and prime/residue/lifting combinations
  found downstream proof references but no existing theorem with these two
  infinite-extension clauses. Read
  `WeilConjectures/Mathlib/RingTheory/Invariant/Profinite.lean`: the continuous
  action and fixed-ring results exist there, and
  `Ideal.Quotient.stabilizerHom_surjective_integralClosure` lifts quotient-ring
  automorphisms. It does not itself lift arbitrary automorphisms of Frac(S/s);
  localization is still needed. Hence no duplicate theorem is introduced.

The prescribed `scompile.py` server compile passed for this file, both sandbox
and library modes, without errors or warnings. No statement dispute, source fault,
new node, or dependency-interface repair was needed. The example CompactObject
Sheaf module is withdrawn; its recorded upstream module was read as well.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
