## Worker report

The module `Sheaf.RingTheory.PolynomialPrimeHeightResidueDegree` states
`Polynomial.height_add_trdeg_residueField_eq`. Its only proof is `sorry`; no definitions,
helper theorems, new nodes, dependency repairs, or statement corrections are needed.

Source read: `literature/stacks-project/algebra.tex`, label `lemma-dimension-formula`
(Stacks Tag 02IJ), hypotheses and proof Case I. In particular that case states
transcendence degree one and proves equality in every instance, without universal
catenarity. The node's five proof steps are reproduced in the theorem docstring.

Hypothesis and clause correspondence:

- A commutative Noetherian domain R is `{R : Type u} [CommRing R]
  [IsNoetherianRing R] [IsDomain R]`. `IsDomain` includes nontriviality and absence
  of zero divisors; no further nonzero hypothesis is necessary.
- P = R[T] is `Polynomial R` with its standard R-algebra structure. Its algebra map
  is exactly the constant-polynomial inclusion, not a new arbitrary map.
- The two prime ideals are `(Q : Ideal (Polynomial R)) (p : Ideal R)` with
  `[Q.IsPrime] [p.IsPrime]`.
- Contraction Q intersect R = p is `(hpQ : p = Q.comap
  (algebraMap R (Polynomial R)))`. The equality is oriented this way to feed the
  existing canonical residue-field map.
- The node's kappa(a) = Frac(A/a) is `a.ResidueField`. Although defined as the
  residue field of `Localization.AtPrime a`, it has Mathlib's
  `IsFractionRing (A ⧸ a) a.ResidueField` instance in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`; that instance constructs
  fractions from local-ring representatives. This is a genuine fraction field
  of the specified quotient, with no new choice of mathematical object.
- The residue-field inclusion is `Ideal.ResidueField.map p Q
  (algebraMap R (Polynomial R)) hpQ`. Its `.toAlgebra` is supplied explicitly to
  `@Algebra.trdeg`, so no unspecified algebra structure is assumed. This map is
  induced by the map on localizations and sends base residues to their images
  (`Ideal.ResidueField.map_algebraMap`). Being a unital field homomorphism, it is
  injective.
- Height is `Ideal.height`. For a prime it agrees with `Order.height` on its prime
  spectrum point (`PrimeSpectrum.height_eq_orderHeight`), the supremum of the
  lengths of strict finite prime chains. Allowing the last prime to be below the
  given prime gives the same supremum as requiring it to be the given prime:
  append the given prime if necessary.
- The first assertion is the first conjunct `Algebra.trdeg R (Polynomial R) = 1`.
- The second assertion is exactly the second conjunct
  `Q.height + Cardinal.toENat (@Algebra.trdeg ... canonicalAlgebra) = p.height + 1`.
  Mathlib heights are extended naturals; `Cardinal.toENat` retains every finite
  cardinal and sends infinite cardinals to infinity, never to zero. The prime
  heights here are finite by Noetherianity, and the residue degree is zero or one
  by the two fibre cases. Thus this is precisely the displayed numerical formula,
  with no truncated subtraction or loss of an infinite case.

Statement dependencies used, with their recorded modules and declarations:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (and `isNoetherianRing_iff_ideal_fg` read).
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`.
- `def-kun-transcendence-degree`: `Mathlib.RingTheory.AlgebraicIndependent.Basic`,
  `Algebra.trdeg`.

All recorded proof dependencies with statements are imported, using plain imports
where they are only needed by the later proof:

- `lem-trf-mvpolynomial-transcendence-degree`:
  `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`,
  `MvPolynomial.trdeg_of_isDomain`; its one-variable form
  `Polynomial.trdeg_of_isDomain` was also read.
- `lem-weil-pbc-projective-module-flat`: `Mathlib.RingTheory.Flat.Basic`,
  `Module.Flat.of_projective`, `Module.Flat.of_free`.
- `lem-weil-pbc-finite-type-algebra-noetherian`: `Mathlib.RingTheory.FiniteType`,
  `Algebra.FiniteType.isNoetherianRing`.
- `lem-weil-pbc-fibre-ring-primes-bijection`:
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`,
  `PrimeSpectrum.preimageOrderIsoFiber`, `PrimeSpectrum.preimageEquivFiber`,
  and the associated explicit forward/inverse formulas. Tensor commutation
  changes the node's factor order to Mathlib's fibre convention.
- `lem-weil-pbc-fibre-ring-residue-field-iso`:
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`,
  `RingHom.SurjectiveOnStalks.residueFieldMap_bijective`,
  `Ideal.surjectiveOnStalks_residueField`; and
  `Mathlib.RingTheory.SurjectiveOnStalks`,
  `RingHom.SurjectiveOnStalks.baseChange` (already publicly imported by the
  residue-field module).
- `lem-weil-pbc-flat-fiber-prime-height`:
  `WeilConjectures.RingTheory.FlatFiberPrimeHeight`,
  `RingHom.height_eq_add_of_flat_fiber`.
- `lem-weil-pbc-localization-dimension-chains-below-prime`:
  `Mathlib.RingTheory.Ideal.Height`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height` (already a public statement import).
- `lem-sc-p1-polynomial-dimension-one`: `Mathlib.RingTheory.KrullDimension.PID`,
  `IsPrincipalIdealRing.ringKrullDim_eq_one`.
- `lem-weil-pbc-finite-type-domain-dimension-trdeg`:
  `WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg`,
  `finiteType_domain_ringKrullDim_eq_trdeg`.

Edge cases checked before writing:

- R a field and p = 0: Q = 0 gives height zero and residue degree one;
  a nonzero irreducible prime Q gives height one and residue degree zero.
- Arbitrary nonmaximal p and Q = pR[T]: the fibre prime is zero and contributes
  degree one. No maximality hypothesis is inserted on either prime.
- A nonzero fibre prime contributes height one and degree zero, including an
  irreducible polynomial of degree greater than one and an inseparable residue
  extension in positive characteristic.
- R = Z, p = (ell), Q = (ell) gives 1 + 1 = 1 + 1; Q = (ell,T) gives
  2 + 0 = 1 + 1. The zero prime upstairs and downstairs is also allowed.
- Zero rings are excluded exactly by the node's domain condition; Q and p cannot
  be the unit ideals because they are prime. No characteristic restriction, finite
  dimension assumption on R, or countability/smallness restriction is added.
  The explicit universe u is arbitrary and all constructed types live there.

Searches run through the prescribed msearch wrapper (Q69, this item):

- `leanfinder`: "For a Noetherian domain R and a prime Q of R[X] over p, height Q
  plus residue transcendence degree equals height p plus one". Eight hits,
  including `Polynomial.height_eq_height_add_one`, `Polynomial.height_map_C`,
  and the going-down height formula. None states both assertions for arbitrary Q.
- `loogle`: `Ideal.height, Polynomial`. Two hits:
  `Polynomial.height_eq_height_add_one` requires Q maximal;
  `Polynomial.height_map_C` requires p maximal. Their full source and docstrings
  were read in `Mathlib/RingTheory/KrullDimension/Polynomial.lean`.
- `grep`: `height.*trdeg|trdeg.*height`, subdirectory `RingTheory`: zero hits.
- `leansearch`: "For every prime Q of a polynomial ring R[X] over a Noetherian
  domain, height Q plus the residue transcendence degree equals the height of
  its contraction plus one". Eight hits, including the same maximal-prime
  theorem, general height definitions/bounds, and polynomial ring dimension.
  None is the arbitrary-prime residue formula together with the algebra degree.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf`:
  `height.*trdeg|trdeg.*height|lem-trf-polynomial-prime-height-residue-degree`.
  The existing `Ideal.height_add_trdeg_residueField_le` is only an inequality;
  `Ideal.height_add_trdeg_residueField_eq` requires universal catenarity. These
  do not supply the polynomial equality over arbitrary Noetherian domains.
  The other hits concern different dimension or valuation results.
- `grep -rn` for this item's exact id in `lean/WeilConjectures`: no result.
- `rg` for `PolynomialPrimeHeightResidueDegree` and
  `Polynomial.height_add_trdeg_residueField_eq` across Mathlib, both project
  source roots, and `dag/lean_names_upstream.json`: no existing declaration.

No node fault or disputed statement was found. The item changes only in `lean`.
The supplied example module has been withdrawn; its node now points at
`WeilConjectures.CategoryTheory.CompactObject`, whose module header and definition
were read for the current conventions.

Validation: prescribed scompile.py, sandbox and final module modes both clean
(1.2 seconds each); no errors or warnings were reported. `autoImplicit` is
explicitly disabled, the universe is declared, and the maximum Lean line width is 87.

## Second reading by Q69

This is a second pass by the assigned worker; the maintainer performs the independent
review, as specified by the dispatcher brief. Comparing the node with the finished
signature again: CommRing, IsNoetherianRing and IsDomain express all assumptions on R;
Polynomial R fixes the ring and its canonical inclusion; both IsPrime binders and hpQ
express exactly the two prime and contraction assumptions. The first conjunct keeps
the algebra transcendence-degree assertion, which a height-only theorem would omit.
The second conjunct uses precisely the induced map on the two quotient fraction fields,
not an arbitrary coefficient action. Cardinal.toENat is necessary only to add the
finite degree to Mathlib's extended-natural heights. The equality has the original
orientation and constant one. In particular no universal-catenarity or maximality
restriction from nearby search results has entered. The docstring carries all five
proof steps, and imports account for every currently stated proof dependency. No
mismatch was found and no mathematical statement was changed in this pass.
