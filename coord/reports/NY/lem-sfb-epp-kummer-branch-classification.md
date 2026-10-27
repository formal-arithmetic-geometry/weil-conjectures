## Worker report

The module `Sheaf.RingTheory.EppKummerBranchClassification` states
`IsDiscreteValuationRing.epp_kummer_branch_classification`, with `sorry` as its
whole proof. It also gives three real helper definitions belonging to this node:
`eppKummerPolynomial`, `eppKummerAlgebra`, and `EppKummerFieldCase`. All four
names are recorded in `lean.declarations`. No dependency record, natural-language
statement, statement dependency, or proof dependency changes. No new nodes or
statement corrections are needed.

Source read: Stacks Project, `more-algebra.tex`, `lemma-prepare` (Tag 09F2),
`lemma-extension-defined-by-nice-polynial` (Tag 09F3), cases (A)--(C), and the
finite-level definition immediately following it. The node's nine-step proof
corrects the printed Kummer substitution and case (C) sign; the declaration
docstring reproduces that accepted proof, including every dependency and all
nine steps. Complete and product normalizations use the node's Tags 09E8/09EM.

Clause-by-clause correspondence:

- A complete DVR R is `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`
  together with `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`. The canonical
  maximal ideal is used throughout. Universes `u` and `v` are independent and
  explicit, with no artificial universe equality.
- The characteristic-zero fraction field F is `[Field F] [Algebra R F]`
  `[IsFractionRing R F] [CharZero F]`.
- The residue characteristic is the prime `p`, with `hp : p.Prime` and
  `[CharP (IsLocalRing.ResidueField R) p]`.
- The root of unity is `ζ : R` with `hζ : IsPrimitiveRoot ζ p`. This is precisely
  multiplicative order p. Its image in F is always `algebraMap R F ζ`.
- The uniformizer is `t : R` with `ht : Irreducible t`; the dependency's exact
  equivalence `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies
  this with `maximalIdeal R = Ideal.span {t}`.
- The abbreviation w=1-ζ is expanded literally in the polynomial and the level
  hypothesis. `eppKummerPolynomial F p ζ` is
  `Polynomial.C (((1-ζ)^p)⁻¹) * ((1 + Polynomial.C (1-ζ)*Polynomial.X)^p - 1)`.
  Thus it is P over F, with actual data and no postponed construction.
- The finite-level hypothesis on `η : F` is `hlevel`: there exists
  `c ∈ maximalIdeal R` whose image in F equals `(1-ζ)^p*η`. This means membership
  in the embedded maximal ideal, not a stronger integral-parameter hypothesis.
- `eppKummerAlgebra` is `AdjoinRoot (P - Polynomial.C η)`, Mathlib's actual
  polynomial quotient `F[T]/(P-η)`, with its canonical F-algebra structure.
- The first disjunction says `Nonempty (D ≃ₐ[F] (Fin p → F))` or the field case.
  The equivalence is F-linear, so the split algebra is exactly F^p over F.
- The field case asserts `∃ hD : IsField D`, equips that same commutative ring
  with `hD.toField`, and asserts `FiniteDimensional F D`, `finrank F D = p`,
  `IsGalois F D`, and `IsCyclic (D ≃ₐ[F] D)`. `IsGalois` means normal and
  separable, using the recorded separability notion; no root field is selected.
  `IsField.toField` constructs the unique inverses, not a new underlying algebra.
- The R-algebra structure on D is the explicit composite of R → F → D.
  `S` is exactly `integralClosure R D`. The field case supplies its
  `IsDiscreteValuationRing` structure, the local inclusion `IsLocalHom`, and
  `IsAdicComplete (maximalIdeal S) S`. The local map induces Mathlib's canonical
  `Algebra (ResidueField R) (ResidueField S)`; no arbitrary residue embedding
  appears.
- Ramification index p is the exact ideal equality
  `(maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ p`.
  Unchanged residue field is `Function.Surjective` on the canonical residue-field
  map, which is already injective as a field homomorphism. This is the first
  general branch, hence total ramification in the stated degree-p field.
- Ramification index one is the exact equality of the extended maximal ideal
  with `maximalIdeal S`. The second general branch asserts finite residue degree
  p, then either `Algebra.IsSeparable` or
  `∀ x : ResidueField S, ∃ a : ResidueField R, algebraMap _ _ a = x^p`.
  Thus the purely inseparable clause is exactly the node's exponent-one
  condition, including its degree requirement.
- Case (A): `∃ r : R, algebraMap R F r = η` implies the index-one ideal equality
  in the field case. In the split case each field factor is F and its
  normalization is R, as witnessed by the final product-normalization equality;
  thus its extended maximal ideal is itself, giving index one for every factor.
- For a positive natural d, the equation
  `algebraMap R F t ^ d * η = algebraMap R F (a : R)` with `a : Rˣ` is equivalent
  to v(η)=-d for the valuation normalized by v(t)=1. This is the DVR unit-times-
  uniformizer decomposition, so no valuation hypothesis is added or removed.
  At η=0 the equation is impossible, matching v(0)=+∞. The normalized valuation
  is only used through these pole conditions, so no valuation needs choosing.
- Case (B): the theorem's second conjunct requires `EppKummerFieldCase` whenever
  the preceding positive pole presentation has `¬p ∣ d`. Within that field case,
  its corresponding universal clause requires the index-p equality and unchanged
  residue field. Thus the conclusion includes being a degree-p field, not merely
  an implication conditional on already being a field.
- Case (C): the third conjunct similarly requires the field case when `p ∣ d`
  and `∀ b : ResidueField R, b^p ≠ residue R a`. The field case's last universal
  clause then requires index one, finite residue degree p, and the displayed
  p-th-power condition for every residue element. Here `residue R a` is precisely
  the residue of t^d*η, since the pole equation identifies them.
- The final equality identifies `integralClosure R (Fin p → F)` with the
  embedded tuples `{x | ∀ j, ∃ r : R, algebraMap R F r = x j}`. This is the exact
  product R^p inside F^p, preserving its embedding rather than asserting an
  unspecified abstract ring equivalence. The equality is unconditional, as
  normalization of the split product does not depend on the value of η.

The helper `EppKummerFieldCase` is an explicit Prop definition expanding this
node's own field alternative, not a new independent notion. Its internal
`let`/`letI` expressions bind the actual quotient and normalization and the
structures whose existence is asserted. The theorem statement itself has no
`let`, hidden `show`, local notation, or private declarations. All helper data
are fully constructed; there is just one postponed theorem.

Statement dependencies read in full and used:

- `def-sc-discrete-valuation-ring`: Mathlib.RingTheory.DiscreteValuationRing.Basic,
  `IsDiscreteValuationRing`, with `Irreducible` for the uniformizer.
- `def-weil-pbc-adically-complete-ring`: Mathlib.RingTheory.AdicCompletion.Basic,
  `IsAdicComplete` (read its extension of `IsHausdorff` and `IsPrecomplete`).
- `def-pc-field-extension`: Mathlib.Algebra.Algebra.Defs, `Algebra`, with the
  fraction field interface from Mathlib.RingTheory.Localization.FractionRing.
- `def-weil-polynomial-ring`: Mathlib.Algebra.Polynomial.Basic, `Polynomial`,
  `Polynomial.C`, `Polynomial.X` and their real ring operations.
- `def-weil-pbc-separable-algebraic-extension`: Mathlib.FieldTheory.Separable,
  `Algebra.IsSeparable` (including the algebraicity inherent in that definition).
- `def-weil-pbc-integral-closure`: Mathlib.RingTheory.IntegralClosure.Algebra.Basic,
  `integralClosure`, whose carrier is `{x | IsIntegral R x}`.

The recorded proof modules are imported privately, including
`Sheaf.FieldTheory.MultiradicalGaloisDegree` (`IntermediateField.multiradical_galois_degree`),
`Sheaf.RingTheory.CompleteDVRFiniteNormalization`
(`IsDiscreteValuationRing.complete_finite_normalization`),
`Sheaf.NumberTheory.DvrGaloisDegreeData` (`NumberTheory.dvr_galois_degree_data`),
`WeilConjectures.FieldTheory.PurelyInseparablePthRootTower`
(`IsPurelyInseparable.exists_pth_root_tower`),
`Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents`
(`AlgebraicGeometry.exists_finite_etale_normal_generic_components`), and
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitStalk`
(`AlgebraicGeometry.Scheme.etale_trait_stalk`). The Mathlib proof matches likewise
supply their recorded modules. Proof dependencies with no recorded declaration
are left unstated here and are listed, with their proof roles, in the docstring:
`lem-sfb-epp-kummer-pole-calculus`, `lem-sfb-split-binomial-root-torsor`,
`lem-sfb-finite-free-field-fibre-dvr`. No statement construction waits on these
proof lemmas.

Edge cases checked:

- p=0 and p=1 are excluded precisely by primality. p=2 is included: ζ=-1,
  w=2 and P(T)=T²+T; the sign convention in the definition is correct.
- η=0 satisfies finite level and gives the split case: the distinct roots are
  `(ζ^j-1)/w`. It cannot satisfy either positive pole presentation.
- The excluded radicand zero, η=-w^(-p), fails finite level because w^p*η=-1
  is a unit, so it cannot give a nonreduced quotient inside the statement.
- For integral η, case (A) includes both split factors and a nonsplit unramified
  degree-p field; it does not assert that every integral parameter splits.
- d=0 is excluded only from the negative-valuation refinements and remains
  available in the general classification. Both p-divisible and nondivisible
  positive d are included.
- For perfect residue fields the non-pth-power premise of (C) cannot hold;
  imperfect residue fields remain fully allowed, and the exponent-one residue
  condition is explicit. No perfectness, residue finiteness, or separability
  of the residue extension is assumed.
- “Unchanged residue field” uses the canonical field embedding's surjectivity,
  which is equivalent to residue degree one without arbitrary identifications.

Searches performed (before defining the helpers):

- `msearch.py leanfinder`, query “Kummer extension of a complete discrete
  valuation field prime degree ramification residue purely inseparable”: eight
  hits, including `IsPRadical.isPurelyInseparable`, residue separability instances,
  and general ramification-degree formulas; no complete branch classification.
- `msearch.py loogle`, query `IsDiscreteValuationRing, IsGalois, IsCyclic`:
  zero hits.
- `msearch.py grep`, query `kummer|Kummer|ramificationIdx|intValuation` in
  `RingTheory/DiscreteValuationRing`: zero service hits. Direct `rg` searches
  located `IsDiscreteValuationRing.addVal` and the maximal-ideal multiplicative
  valuation, but no branch classification; the unit presentation avoids adding
  a private valuation definition.
- `msearch.py leansearch`, query “Kummer extension complete discrete valuation
  ring degree prime ramification classification”: eight hits, comprising
  general ramification/inertia formulas, cyclotomic-number-field ramification,
  and compact valuation rings; no match.
- Direct `rg` in the project's `lean/WeilConjectures/RingTheory` and
  `lean/Sheaf/RingTheory` for `kummer|Kummer|branch_classification|ramificationIdx|intValuation`
  found other Kummer normalization and tame ramification statements. None states
  this finite-level, prime-degree trichotomy with pole refinements.
- Direct `rg` over all `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `kummer.*[pP]olynomial|[pP]olynomial.*[kK]ummer|eppKummer|EppKummer` found only
  a distinct quadratic-action docstring, not the polynomial or these helpers.
  Searching `lem-sfb-epp-kummer-branch-classification` in upstream sources found
  no declaration attached to this node.

Validation: `scompile.py NY lem-sfb-epp-kummer-branch-classification` compiled
this module as both sandbox and library module against the published live
library, cleanly within the standard 60-second per-file limit. An initial
missing public import of `IsPrimitiveRoot` was repaired by adding
`public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`; the subsequent
compile had no errors or non-sorry warnings. `set_option autoImplicit false`
is explicit, all universes and variables are bound, and all lines fit 100
characters. No source or shared library file was edited.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
