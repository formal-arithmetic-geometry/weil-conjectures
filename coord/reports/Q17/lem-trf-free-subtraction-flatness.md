## Worker report

This delivery states `Module.free_subtraction_flatness` in
`Sheaf.RingTheory.FreeSubtractionFlatness`. The theorem has one whole-proof `sorry`;
its docstring contains the three-step DAG proof with the local 05I3 input, the
05CL globalization, and the flat-extension diagram chase. There are no new
notions, dependency replacements, or changes to the natural-language statement.

The preceding BLOCKED result confused Q64's stage-1 split with a stage-2
statement landing. The base node is split and reviewed but has no Lean record.
The Q64 report is expressly a stage-1 report and records no matching declaration.
This packet provides the previously absent Lean statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings and their homomorphism: `(R A : Type u) [CommRing R]
  [CommRing A] [Algebra R A]`, with the actual map `algebraMap R A`.
- Flat ring map: `[Module.Flat R A]`. `RingHom.flat_algebraMap_iff` identifies
  this with flatness of the ring homomorphism.
- Finite presentation: `[Algebra.FinitePresentation R A]`, the algebra notion
  of finitely many generators and relations, underlying the dependency's
  affine-local scheme notion. In particular this is not module finite
  presentation or an added finite-module hypothesis on A.
- Every fibre remains a nonzero domain after every extension of its residue
  field: `[GeometricallyIntegral (Spec.map (CommRingCat.ofHom
  (algebraMap R A)))]`. This is the geometric-integrality clause of
  `def-pc-geometrically-irreducible`, not just geometric irreducibility or
  reducedness. Mathlib's `GeometricallyIntegral.iff_geometricallyIntegral_fiber`
  gives the fibrewise formulation. For affine schemes, integral means a
  nonzero domain, so empty fibres are excluded over a nonempty base.
- Finite A-module: `(N : Type v) [AddCommGroup N] [Module A N]
  [Module.Finite A N]`. The additional `[Module R N] [IsScalarTower R A N]`
  merely expresses restriction along `R → A`, whose compatible action is
  unique; it is not an additional mathematical property of N.
- Nonnegative rank and the given map: `(r : ℕ)
  (α : (Fin r → A) →ₗ[A] N)`. Since the index is finite, this is the same
  direct sum A^r; r = 0 is included.
- For each p the prime ξ_p is the inverse image of the fibre's zero prime:
  `(ξ : PrimeSpectrum R → PrimeSpectrum A)` and `hξ` equate `(ξ p).asIdeal`
  with the kernel of `Algebra.TensorProduct.includeRight : A →ₐ[R]
  p.asIdeal.ResidueField ⊗[R] A`. This is exactly the map a ↦ 1 tensor a.
  Tensor symmetry identifies this fibre with the node's A tensor_R κ(p).
  Its kernel is prime because geometric integrality makes the fibre a
  nonzero domain. Thus the displayed family exists and is determined
  uniquely by hξ; it is not a freely chosen prime or an extra restriction.
- Generic relative flatness: `hgenericFlat` says `Module.Flat R
  (LocalizedModule (ξ p).asIdeal.primeCompl N)` for every p.
  The same localized module has a canonical R_p action: if s is outside p,
  its image is a nonzero scalar of κ(p), hence a unit in the fibre, hence
  outside ξ_p. Thus such s acts invertibly on N_{ξ_p}. For that canonical
  action, `Module.flat_iff_of_isLocalization (Localization.AtPrime p.asIdeal)
  p.asIdeal.primeCompl` says that flatness over R and over R_p are
  equivalent. This is an equivalent formulation of precisely the stated
  hypothesis, using the same localized module; no extra tensor factor,
  arbitrary module action, or stronger flatness condition is assumed.
- Generic basis: `hgenericBasis` is `Function.Bijective
  (α.baseChange (ξ p).asIdeal.ResidueField)` for every p. This is an
  isomorphism of vector spaces, expressed as bijectivity of its canonical
  linear map. `LinearMap.baseChange` is scalar extension along A → κ(ξ_p).
  Tensor symmetry and the finite-free base-change isomorphism identify
  its source and target with κ(ξ_p)^r and N tensor_A κ(ξ_p).
- H is the cokernel: `N ⧸ LinearMap.range α` is the actual quotient module,
  not an arbitrary module having an unspecified cokernel property.
- First conclusion, universal injectivity over R: for every
  `(L : Type (max u w)) [AddCommGroup L] [Module R L]`, the canonical
  `((α.restrictScalars R).lTensor L)` is injective. The universe w is
  explicit and unrestricted, so this covers test modules in every larger
  universe and never quantifies only over a universe smaller than R.
- Second conclusion, equality of relative flat loci: for every
  `q : PrimeSpectrum A`, flatness of `LocalizedModule q.asIdeal.primeCompl N`
  is equivalent to flatness of the same localization of H. Here p is
  canonically `PrimeSpectrum.comap (algebraMap R A) q`. Every s outside p
  maps outside q, so both modules carry their canonical R_p actions.
  Apply the same `Module.flat_iff_of_isLocalization` to each to recover
  word for word the node's flatness equivalence over R_p. Quantifying
  only q loses no case: its inverse image p is unique.
- The final explanatory clauses about finiteness, flatness, localizations,
  and residue fields use the standard Mathlib definitions directly.

Dependency declarations read and used:

- `def-weil-pbc-module-localization`: `LocalizedModule`,
  `Mathlib.Algebra.Module.LocalizedModule.Basic`. Its docstring and
  construction use fractions m/s and the stated equivalence relation.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField`. The affine ring version used
  in the formula is `Ideal.ResidueField`,
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, literally the residue
  field of `Localization.AtPrime` and canonically the scheme residue field.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; the underlying points are
  `PrimeSpectrum`. These appear in the geometric-integrality hypothesis.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat`,
  `Mathlib.RingTheory.RingHom.Flat`, and its exact module form `Module.Flat`.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`. Its full
  signature and affine-local docstring use `RingHom.FinitePresentation`;
  the statement here uses its constituent `Algebra.FinitePresentation`
  because the node explicitly concerns a homomorphism of rings.
- `def-pc-geometrically-irreducible`: the geometric-integrality clause
  supplied by the existing `AlgebraicGeometry.GeometricallyIntegral` in
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`, as identified by
  the dependency's mathlib_match. The recorded primary name is
  `GeometricallyIrreducible`, and the record expressly names the integral,
  reduced, and connected variants as the other clauses.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, the finite generation of top.

The two proof dependencies `lem-trf-local-generic-basis-universal-injective`
and `lem-trf-universal-injective-check-stalks` have neither Lean records nor
Mathlib matches on the base. They are not used to type this statement and
have no modules to import. Their future use is recorded in the proof
docstring. No dependency needed for the statement is missing.

Edge cases checked before writing: r = 0 has the zero free module, and
H = N, so the flat-locus equivalence is reflexive. If R is the zero ring,
A and every unital A-module are zero; the base spectrum is empty and
universal injectivity still holds. If R is nonzero, A = 0 is rejected by
geometric integrality since the fibres would be empty. N = 0 requires
r = 0 whenever the base is nonempty by the residue-field isomorphism.
If α is an isomorphism, H = 0 and N is free over the flat A, as required.
As a test for a missing generic-flatness assumption, R = k[t], A = R[x],
N = A/(t), r = 1, and the quotient α have a basis isomorphism at the
fibre over (t), but N localized at ξ_(t) is not R_(t)-flat; our hypothesis
correctly rejects this example (there are also no fixed generic ranks
across all base points). For N = A, α = id, all hypotheses and both
conclusions hold. No noetherianity, nonzero-base, positive-rank, or
characteristic hypothesis was introduced.

Searches (all through the prescribed search wrapper unless marked rg):

- LeanFinder: "A generic basis map from a finite free module into a finite
  module over a flat finitely presented algebra with geometrically integral
  fibres is universally injective and subtracting it preserves the relative
  flat locus". Eight hits, including `Module.freeLocus_eq_univ`,
  `Module.exists_basis_of_span_of_flat`, `Algebra.HasGoingDown.of_flat`,
  and the flat equational criterion. None states this result.
- Loogle: `Module.Flat, LinearMap.lTensor`. Twelve hits, including flatness
  characterizations and `LinearMap.lTensor_injective_of_exact_of_flat`.
  These describe flatness or a short exact sequence with flat cokernel;
  none gives the geometric-fibre criterion in this item.
- Mathlib grep: `universally.injective|geometricallyIntegral|GeometricallyIntegral`
  in RingTheory: zero hits. Direct rg across Mathlib for
  `freeSubtraction|free_subtraction|subtraction.*flat|flat.*subtraction`:
  zero hits.
- LeanSearch: "For a flat finitely presented algebra with geometrically
  integral fibres, subtract a generic basis from a finite module to
  preserve its relative flat locus". Eight hits, including flatness
  descent and localization results; none states generic basis subtraction.
- rg across the upstream WeilConjectures tree and side lean/Sheaf for
  `lem-trf-free-subtraction-flatness|free_subtraction_flatness`: no hits.
  Broader `GeometricallyIntegral` / `universally.injective` searches
  returned geometric examples and universally injective scheme morphisms,
  but no equivalent module theorem. Related RingTheory searches found
  ordinary flat-localization statements only.

Validation: `scompile.py Q17 lem-trf-free-subtraction-flatness` compiled
this module independently on the server, with no errors or warnings.
The JSON copy changes only `lean`, whose statement is extracted verbatim
from the delivered theorem signature. No statement dispute or node fault
was found. The machine's UTC date is used for the Lean record.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
