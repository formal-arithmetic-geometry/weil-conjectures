## Worker report

The module `Sheaf.RingTheory.EtaleSupportedCotangent` states
`Algebra.finite_and_ideal_pow_annihilates_polynomialConormal` with `sorry`.
The accompanying helper `Algebra.polynomialConormalDifferential` has real data:
it composes Mathlib's canonical `Extension.cotangentComplex` with the coordinate
isomorphism of the base-changed polynomial Kahler basis. It introduces no second
conormal module, quotient action, Kahler differential, or presentation notion.
No statement correction or new node is needed.

Hypothesis and clause correspondence:

- Commutative rings A and C and the structure A → C: `{A C : Type u}`,
  `[CommRing A] [CommRing C] [Algebra A C]`. Both spectra use the common scheme
  universe; all universe variables and object variables are explicitly bound.
- A Noetherian: `[IsNoetherianRing A]`.
- An arbitrary ideal H of A: `(H : Ideal A)`.
- C a finite type A-algebra: `hC : (algebraMap A C).FiniteType`, the recorded
  `RingHom.FiniteType` definition, equivalent to `Algebra.FiniteType A C` by
  `RingHom.finiteType_algebraMap`.
- Etale over Spec(A) minus V(H): `het : AlgebraicGeometry.Etale` of the
  restriction `Spec.map (CommRingCat.ofHom (algebraMap A C)) ∣_ U`, where
  `U` has carrier `(PrimeSpectrum.zeroLocus (H : Set A))ᶜ`. This restricts the
  source to the full inverse image of U, exactly the stated condition. The
  open-set proof is Mathlib's `isClosed_zeroLocus ... |>.isOpen_compl`.
- Arbitrary finite s ≥ 0 and arbitrary surjection α: `(s : ℕ)`,
  `(α : MvPolynomial (Fin s) A →ₐ[A] C)`, `(hα : Function.Surjective α)`.
- K is the kernel of α: `(Extension.ofSurjective α hα).ker` is definitionally
  `RingHom.ker α.toRingHom`. Its `Cotangent` is a type synonym of `K.Cotangent`,
  i.e. K/K². Mathlib supplies its C-action by lifting scalars through α;
  `Cotangent.val_smul'` verifies compatibility with the polynomial action.
  Thus the choice of a set-theoretic section in `ofSurjective` changes no
  action or mathematical object: any two lifts differ by K, which kills K/K².
- The specified differential dα is `polynomialConormalDifferential α hα`.
  `Extension.cotangentComplex_mk` sends `[f]` to `1 ⊗ df`. The definition then
  applies `((KaehlerDifferential.mvPolynomialBasis A (Fin s)).baseChange C).equivFun`.
  `Module.Basis.baseChange_repr_tmul` and
  `KaehlerDifferential.mvPolynomialBasis_repr_apply` identify coordinate j
  with `α (MvPolynomial.pderiv j f)`. In the helper, the explicit temporary
  algebra instance is `α.toAlgebra`, so this is α, not another map on polynomials.
- M1 is the actual `LinearMap.ker` of that map. M0 is the actual quotient
  `(Fin s → C) ⧸ LinearMap.range` of that map. The finite product here is the
  same finite free module C^{⊕s} as in the node, including s = 0.
- The two finite-generation conclusions are the first two conjuncts,
  `Module.Finite C M1` and `Module.Finite C M0`.
- A single nonnegative integer b is `∃ b : ℕ`. The last conjunction says
  `∀ a ∈ H ^ b, ∀ m : M1, algebraMap A C a • m = 0`, and the same for M0.
  These are exactly H^b M1 = H^b M0 = 0, with both actions through A → C.
  No positivity restriction on b and no elementwise varying exponent is added.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`; its equivalence with
  `Algebra.FiniteType` is `RingHom.finiteType_algebraMap`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`,
  `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`; the signature uses the actual
  polynomial algebra, not an abstract presentation carrier.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.MvPolynomial.PDeriv`: `MvPolynomial.pderiv` (the coordinate
  description of the differential).

The already-stated proof dependencies are imported: the Noetherian finite-type
and submodule results in `Mathlib.RingTheory.FiniteType` and
`Mathlib.RingTheory.Noetherian.Basic`; affine section/open results via
`Mathlib.AlgebraicGeometry.ResidueField` and `.OpenImmersion`; etale restriction
and composition in `.Morphisms.Etale`; the polynomial Kahler basis via
`Mathlib.RingTheory.Extension.Cotangent.Basic`; exact localization in
`Mathlib.Algebra.Module.LocalizedModule.Exact`; and the three upstream modules
`WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent`,
`WeilConjectures.RingTheory.EtaleRingMapConormalCriterion`, and
`WeilConjectures.RingTheory.ExistsAnnihilatorOfSubsingletonLocalizedModule`.
Their recorded theorems are respectively
`Algebra.Generators.principal_localization_naive_cotangent`,
`Algebra.etale_ring_map_conormal_criterion`, and
`Module.exists_annihilator_of_subsingleton_localizedModule`.
Statement imports are public; proof-only imports are plain imports.

Edge cases checked mathematically:

- H = 0: the complement is empty and etaleness there is vacuous; b = 1
  annihilates both modules. No global etaleness is inferred.
- H = A: the complement is all of Spec A; etaleness makes both modules zero,
  and b = 0 is allowed.
- s = 0: C^0 is zero, so the cokernel is zero but the kernel need not be.
  For Z → F_p with H = (p), the kernel module is (p)/(p²) and b = 1 works.
  This checks that the kernel was not incorrectly discarded.
- C is the zero ring: all C-modules here are zero, its spectrum is empty,
  and all hypotheses and conclusions still make sense. No nontriviality or
  domain assumption occurs.
- Redundant presentation: A = C with α : A[y] → A, y ↦ 0 gives the identity
  differential on the conormal generator, so both cohomology modules vanish.
  The statement quantifies all surjections rather than one selected presentation.

Searches (2026-10-24):

- `msearch.py ... leanfinder` query: "For a finite type algebra over a noetherian
  ring etale off V(H), the kernel and cokernel of any polynomial conormal
  differential are finite and killed by a power of H". Eight hits include
  `Algebra.Extension.Cotangent.finite`, finite H1 results, Kahler finiteness,
  and smooth locus results. None states the simultaneous ideal-power result.
- `msearch.py ... leansearch` query: "The kernel and cokernel of a finite
  polynomial conormal map are finite and annihilated by an ideal power if
  the algebra is etale outside its zero locus". Eight hits include
  `Algebra.Extension.Cotangent.finite`, `Cotangent.ker_mk`, and finite
  presentation kernel finiteness. No exact theorem.
- `msearch.py ... loogle` query:
  `Algebra.etaleLocus_eq_compl_support, Algebra.Extension.cotangentComplex`.
  Zero hits for the combined query.
- `msearch.py ... grep` query:
  `etaleLocus_eq_compl_support|annihilator.*cotangent|cotangent.*annihilator`
  in `RingTheory`: three hits in `Mathlib/RingTheory/Etale/Locus.lean`,
  describing the etale locus, not simultaneous finiteness and ideal torsion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for conormal differential,
  cotangent complex, and supported cotangent terms located the existing
  Mathlib-based conormal interfaces and the recorded proof dependencies;
  no exact theorem. The required `grep -rn` of the item id in
  `lean/WeilConjectures` had no hits. The final declaration names also have
  no hits in Mathlib, either project source tree, or `dag/lean_names_upstream.json`.

Source inspected: `literature/stacks-project/restricted.tex`, the full proof of
lemma-rig-etale (0ALQ) and final paragraph of lemma-approximate (0AKA); also
Mathlib's full conormal construction and coordinate-basis signatures/docstrings.
The current blueprint ancestor's statement and proof were read from
`literature/blueprint/latest/`; this is the ordinary pre-completion subargument
recorded in the item's `blueprint.from.place`, not a change of the unit route.

Validation: `scompile.py Q146 lem-per-etale-supported-cotangent-completion`
compiled both its sandbox and final library-path versions cleanly (1.6 s each).
Initial errors were repaired by explicitly assigning `α.toAlgebra` in the helper
and qualifying `AlgebraicGeometry.Etale` within namespace `Algebra`.
There are no node faults or disputed mathematical clauses.

## Second reading by Q146

A separate clause-by-clause reread by the same worker was performed; the dispatcher
explicitly forbids spawning another agent, and the maintainer performs the
independent review of this delivery. The comparison above was checked against
both the node and final file, particularly the full inverse-image restriction,
the K/K² source and induced C-action, every coordinate α(∂f/∂y_j), the actual
kernel and quotient, both finite-generation clauses, and the shared exponent.
No hypothesis or conclusion is missing. The explicit `α.toAlgebra` correction
ensures the coordinate construction uses the supplied presentation; qualifying
scheme etaleness resolves the ring/scheme namespace ambiguity without changing
the hypothesis. The helper contains no proof placeholder; the sole postponed
theorem is the item's theorem and its docstring includes all seven proof steps.
