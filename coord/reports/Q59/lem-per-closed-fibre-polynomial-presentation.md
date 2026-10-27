## Worker report

The module `Sheaf.RingTheory.ClosedFibrePolynomialPresentation` states
`Algebra.EssFiniteType.exists_polynomial_maximal_localization_quotient`, with one
`sorry` proof and no definitions. The node changes only in `lean`.

Source read: `literature/stacks-project/algebra.tex`, Tag 0AUG,
`lemma-localization-at-closed-point-special-fibre`, statement and entire proof.
The current blueprint ancestor `lem-per-artin-gabber-affine-curve` and its proof
were also read under `literature/blueprint/latest/`. The item is an algebraic
ingredient below that unit, not its own unit statement. Its existing statement
agrees with 0AUG, so no correction is needed. The removed prior module is absent
from both current source trees; its archived Lean review describes the same
interface, but is not treated as an existing declaration.

Hypotheses and clauses, in order:

- The commutative rings are `(R : Type u) (S : Type v) [CommRing R] [CommRing S]`.
  Independent, explicitly declared universes permit arbitrary ring sizes.
- The homomorphism is `[Algebra R S]`, with its ring map `algebraMap R S`.
  Every homomorphism of commutative rings gives this algebra structure.
- Essentially finite type is `[Algebra.EssFiniteType R S]`, exactly the recorded
  Mathlib notion; its definition and localization characterization were read.
- Both rings local is `[IsLocalRing R] [IsLocalRing S]`. No `IsLocalHom`
  assumption is present: nonlocal maps are included exactly as the source says.
- The maximal ideal of the base is `IsLocalRing.maximalIdeal R`.
- Some nonnegative integer is `∃ (n : ℕ)`. The polynomial ring is
  `MvPolynomial (Fin n) R`, including the empty variable set for zero.
- A maximal ideal of that polynomial ring is
  `(m : MaximalSpectrum (MvPolynomial (Fin n) R))`; its ideal is `m.asIdeal`.
  Mathlib's bundled maximal spectrum stores exactly an ideal and maximality.
- Lying over the base maximal ideal is the literal contraction equality
  `Ideal.comap (algebraMap R (MvPolynomial (Fin n) R)) m.asIdeal =
  IsLocalRing.maximalIdeal R`.
- The local polynomial ring is `Localization.AtPrime m.asIdeal`; maximality
  supplies primality via Mathlib's instances.
- A quotient of that ring is represented by
  `∃ (I : Ideal (Localization.AtPrime m.asIdeal))` and
  `Localization.AtPrime m.asIdeal ⧸ I`.
- The specified multiplicative subset is
  `T : Submonoid (Localization.AtPrime m.asIdeal ⧸ I)`. A submonoid is exactly
  a subset containing one and closed under multiplication; zero is not
  artificially prohibited.
- Being a localization of that quotient is
  `Nonempty (Localization T ≃ₐ[R] S)`. The equivalence is over the original R,
  using the canonical polynomial, localization, quotient, and localization
  algebra structures, so it respects the given homomorphism. Existence of
  an isomorphism is proposition-valued and chooses no data.
- The last explanatory clause defining a local ring is Mathlib's standard
  `IsLocalRing`, equivalent for commutative rings to having exactly one maximal
  ideal. It includes nontriviality, matching the node's convention.

Dependency declarations read and used:

- `def-weil-pbc-essentially-finite-type-algebra`: `Algebra.EssFiniteType`,
  `Mathlib.RingTheory.EssentialFiniteness`, and its fraction characterization.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and
  `MvPolynomial.algHom_ext`, `Mathlib.Algebra.MvPolynomial.Basic`;
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval` was read for the
  recorded universal-property clause. The statement needs only the ring itself.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. The additional recorded
  residue-field and fibre declarations were read in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` and `.Fiber`; these are used
  in the proof plan, not in the statement's type.

All recorded proof dependencies are present as imports. In addition to the
three public statement modules, plain imports supply `RingHom.FiniteType`
(`Mathlib.RingTheory.FiniteType`), `Ideal.exists_le_maximal`
(`Mathlib.RingTheory.Ideal.Maximal`), `ValuationRing` / `ValuationRing.TFAE`
(`Mathlib.RingTheory.Valuation.ValuationRing`),
`LocalSubring.exists_le_valuationSubring`
(`Mathlib.RingTheory.Valuation.LocalSubring`), and
`ValuationSubring.exists_comap_eq`
(`WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring`). Their signatures
were checked in the source. `Mathlib.RingTheory.Spectrum.Maximal.Defs` is a
public import for the bundled maximal ideal. The theorem docstring spells out
all seven accepted proof steps and the nodes each step uses: the first local
quotient presentation, proper-ideal case, dominating valuation ring, finite
pivot induction, inverse chart maps, properness in the new chart, and the
final quotient/localization fraction comparison.

Edge cases checked before finalizing:

- `n = 0` is permitted; for S = R use the unique base maximal ideal, zero
  quotient ideal, and localization at one. There is no positive-variable
  restriction.
- For a base field its maximal ideal is zero; the contraction equation is
  still exactly the source condition. Arbitrary characteristic is allowed.
- Nonlocal maps are retained. For R = k[t] localized at (t) and S = k(t), a
  chart with variable y mapping to t has maximal ideal (t,y); quotient by
  y-t and then invert t to obtain S. No maximal-ideal contraction condition
  is imposed on the original map R to S.
- R may have zero divisors and nilpotents; no domain, reducedness, finiteness
  of presentation or Noetherian hypothesis was added.
- The zero ring is excluded by having exactly one maximal ideal, as in Stacks
  and Mathlib's `IsLocalRing`; no extra nontriviality hypothesis was added.
- T and I are unrestricted; the existence of an equivalence to the nontrivial
  local ring S already prevents an unsuitable zero localization or quotient.

Searches actually run (Q59 / this item):

- `msearch.py leanfinder`: "An essentially finite type algebra over a local
  ring is a localization of a quotient of a polynomial ring localized at a
  maximal ideal over the base maximal ideal". Eight hits, including
  `Algebra.EssFiniteType.isLocalization`,
  `Algebra.essFiniteType_iff_exists_subalgebra`, and localization instances;
  none states the maximal-ideal-over-the-base presentation.
- `msearch.py loogle`: `Algebra.EssFiniteType, IsLocalRing`. Eight hits on
  formally unramified algebras, residue fields, and maximal ideals. None is
  0AUG; those theorems have additional hypotheses.
- `msearch.py grep`: `EssFiniteType|closed.point.special.fibre|polynomial_maximal_localization`
  in `RingTheory`. Twenty-five hits, including the class and localization
  material; no exact statement.
- `rg -n` for
  `polynomial_maximal_localization|0AUG|localization.at.closed.point.special.fibre`
  in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  returned no hits.
- `grep -rn 'lem-per-closed-fibre-polynomial-presentation' lean/WeilConjectures`
  returned no hits. Broader `closed.fibre|closed.point.special.fibre` searches
  found unrelated geometric closed-fibre theorems, not this algebraic statement.

Validation: prescribed `scompile.py` compiled both the sandbox check and library
module cleanly (7.8 s and 14.0 s). All universes and variables are explicit;
`set_option autoImplicit false` is enabled. There are no new nodes, dependency
repairs, statement changes, disputed statements, or other node faults.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
