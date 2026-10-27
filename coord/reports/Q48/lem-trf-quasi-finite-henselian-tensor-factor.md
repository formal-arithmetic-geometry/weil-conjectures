## Worker report

The new module `Sheaf.RingTheory.QuasiFiniteHenselianTensorFactor` states
`Algebra.quasiFinite_henselian_tensor_factor`. Its only proof is `by sorry`.
The existing node is unchanged except for its `lean` record. No new notion,
dependency repair, or statement correction is needed.

Source read: Stacks Project `algebra.tex`, Tag 05WP
(`lemma-quasi-finite-henselization`), especially the first two sentences of its
proof, and Tag 04GH (`lemma-finite-over-henselian`), clauses (2), (3), and
its proof. The given general henselian base R is justified by 04GH(3): the
special henselization appearing in 05WP is not needed for this step.

Hypothesis-by-hypothesis rendering:

- Commutative rings A, B, R are the explicit `Type u`, `Type v`, `Type w`
  parameters with their three `CommRing` instances. Universes are independent.
- The finite-type ring map A → B is `[Algebra A B] [Algebra.FiniteType A B]`.
- The two prime ideals are `(p : PrimeSpectrum A)` and
  `(q : PrimeSpectrum B)`. Primality is part of these bundles.
- q lies over p is
  `hqp : q.asIdeal.comap (algebraMap A B) = p.asIdeal`.
- Quasi-finiteness at q is `hq : IsQuasiFiniteAtPrime A B q`, using the
  dependency's isolated-point definition, not a copied or altered predicate.
- R is a henselian local ring by `[HenselianLocalRing R]`; this class extends
  `IsLocalRing R`, whose maximal ideal is `IsLocalRing.maximalIdeal R`.
- The map A_p → R is `[Algebra (Localization.AtPrime p.asIdeal) R]`.
  `[Algebra A R]` and `[IsScalarTower A (Localization.AtPrime p.asIdeal) R]`
  specify its restriction along A → A_p. They do not assert an extra
  mathematical property: every given A_p → R has exactly this restriction.
- This map is local by `hlocal`, precisely the equality of the inverse image
  of R's maximal ideal and A_p's maximal ideal written in the node.
- C is literally `R ⊗[A] B` throughout, with the standard commutative tensor
  algebra structure. There is no separate arbitrary ring or arbitrary map.
- Every prime n of C is covered by `(n : PrimeSpectrum (R ⊗[A] B))`.
- Contraction of n to R is the equality `hnR`, using `algebraMap R C`,
  which is r ↦ r ⊗ 1.
- Contraction of n to B is `hnB`, using
  `(Algebra.TensorProduct.includeRight : B →ₐ[A] R ⊗[A] B).toRingHom`,
  which is b ↦ 1 ⊗ b. No B-algebra instance on C is installed.

Clause-by-clause conclusion:

- `IsQuasiFiniteAtPrime R (R ⊗[A] B) n` is quasi-finiteness of R → C at n.
  The finite-type instance required to type this predicate is Mathlib's
  `Algebra.FiniteType.baseChange`, obtained from A → B. It is not an added
  hypothesis or an extra conclusion.
- `Module.Finite R (Localization.AtPrime n.asIdeal)` states exactly the
  required finite generation as an R-module, not mere finite type as algebra.
- Equality of the comap of the maximal ideal of
  `Localization.AtPrime n.asIdeal` along `algebraMap R` with the maximal
  ideal of R states locality of the canonical composite R → C → C_n.
  The localization's R-algebra instance is the canonical scalar tower
  through C, so finiteness concerns this same map.
- `HenselianLocalRing (Localization.AtPrime n.asIdeal)` gives the final
  henselianity clause; locality of that ring is already furnished by prime
  localization. No ind-etaleness, residue-field equality, or Noetherian
  instance is assumed anywhere.

Statement dependencies used, with their signatures and docstrings inspected:

- `WeilConjectures.RingTheory.QuasiFiniteAtPrime`:
  `Algebra.IsQuasiFiniteAtPrime` (the open singleton in the canonical fibre
  spectrum; source Tags 00PL and 00PK).
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  its public Mathlib `HenselianLocalRing` (extends `IsLocalRing`) and
  `HenselianRing`. Strict henselianity is not imposed; the recorded
  `IsStrictlyHenselianLocalRing` is not the clause of that dependency used here.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`:
  `Localization.AtPrime`; its local-ring instance supplies maximal ideals.
  The dependency's other clauses `Ideal.ResidueField` and `Ideal.Fiber`
  were also read; the existing quasi-finite predicate already uses the latter.
- `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`:
  `Algebra.TensorProduct.instCommRing`, `instAlgebra`, `includeLeft`,
  `includeRight`, `tmul_mul_tmul`, `productMap`, `productMap_apply_tmul`,
  and `ext`. These are the dependency's existing pushout construction.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`:
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`, `lift.tmul`,
  `ext'`, `LinearMap.rTensor`, and `rTensor_tmul`. The tensor type used
  here is this same module tensor product, with its algebra multiplication.
- `Mathlib.RingTheory.FiniteStability`: `Algebra.FiniteType.baseChange`,
  providing the derived finite-type instance required in the first conclusion.

Proof dependencies are imported without `public`:
`WeilConjectures.RingTheory.QuasiFiniteFourRings`
(`Algebra.finiteType_and_isQuasiFiniteAtPrime_of_four_rings`),
`Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition`
(`HenselianLocalRing.finiteType_exists_algEquiv_pi_prod`),
`WeilConjectures.RingTheory.FiniteLocalHenselian`
(`HenselianLocalRing.finite_local_henselian`), and
`Mathlib.LinearAlgebra.FiniteDimensional.Basic`
(`fieldOfFiniteDimensional` and `FiniteDimensional.exists_mul_eq_one`).
The docstring records all four proof steps, including exclusion of the
remainder factor, the finite-dimensional domain argument, the explicit
localization isomorphism, and the maximal-ideal contraction argument.

Edge cases checked before writing:

- If B or C is the zero ring, there is no q or n respectively, so the
  assertion is correctly vacuous. Henselian local R itself is nonzero by
  the standard local-ring convention.
- If R is a field and C is a finite algebra such as k[e]/(e²), the selected
  localization can be nonreduced and still is finite and henselian. No
  reducedness, separability, or residue-field isomorphism was introduced.
- An empty collection of finite factors cannot supply n above the closed
  point with the required quasi-finiteness, as the remainder argument shows.
- A henselian non-Noetherian R is permitted: no Noetherian instance is in
  the signature, and 04GH(3) does not assume one.
- A finite type algebra may contain a non-quasi-finite remainder; the theorem
  does not assert that C itself is finite or that all its primes qualify.
- Arbitrary independent ring universes and arbitrary primes p, q, n are
  allowed; there is no specialization to a henselization or a closed q.

Searches for an existing statement:

- `msearch.py` LeanFinder: “A quasi finite point over the closed point of a
  henselian local ring has a finite henselian localization after tensor
  base change”. Eight hits, including `Algebra.QuasiFiniteAt.baseChange`,
  residue-field finiteness, and `HenselianLocalRing.TFAE`; none states this
  finite henselian localization assertion.
- `msearch.py` LeanSearch: “Localization of a finite type algebra at a quasi
  finite point over the closed point of a henselian local base is finite
  and henselian”. Eight hits, concerning localization stability and the
  maximal-ideal henselian pair; no exact statement.
- `msearch.py` Loogle: `HenselianLocalRing, Algebra.QuasiFiniteAt`, zero hits.
  The initial query using the project-specific `Algebra.IsQuasiFiniteAtPrime`
  was unknown to the remote Mathlib index; the Mathlib-only query above
  was then used instead.
- `msearch.py` grep in `RingTheory`:
  `henselian.*(quasiFinite|quasi.finite)|(quasiFinite|quasi.finite).*henselian`,
  zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for quasi-finite/
  henselian/tensor combinations found only component results, especially
  the existing finite-local and finite-type product decomposition modules.
  None states the item's tensor-base-change localization theorem.
- `grep -rn` for the exact blueprint id in `lean/WeilConjectures` found no
  declaration. The final full declaration name was also checked against
  both project roots and Mathlib, with no existing declaration found.

Validation: the delivered file compiled cleanly with `scompile.py` in both
its sandbox and final module context. Every variable and universe is bound
explicitly. No diagnostic commands, new definitions, or proved theorems
are in the module. No disputed statement or node fault was found.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
