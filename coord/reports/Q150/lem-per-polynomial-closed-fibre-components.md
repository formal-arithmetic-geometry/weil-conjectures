## Worker report

The module `Sheaf.RingTheory.PolynomialClosedFibreComponents` states
`MvPolynomial.isCatenaryRing_equidimensional_localizationAtMaximal`, with its only
proof `sorry`. No definitions, helper theorems, new nodes, dependency repairs, or
statement corrections are needed. Only the item's `lean` field changes.

Source read: Stacks Project `more-algebra.tex`, Tag 0AW5,
`lemma-formally-catenary`, especially the final two proof paragraphs (lines
32462–32484 in this checkout). The source takes C to be the equidimensional
completion and proves precisely that the polynomial localization over its closed
point is catenary, with all minimal-component quotients of dimension dim C + r.
The node extracts that assertion for any complete equidimensional Noetherian
local ring. The declaration docstring gives all eight steps of the accepted DAG
proof, including the omitted minimal-prime argument, quotient/localization
identifications, coefficientwise flatness, and arbitrary closed-point fibre
dimension. Proof-only imports preserve the DAG proof plan.

Hypothesis and conclusion correspondence:

- The commutative ring C is `(C : Type u) [CommRing C]`, with arbitrary explicitly
  declared universe `u`. `[IsNoetherianRing C]` renders Noetherianity, and
  `[IsLocalRing C]` renders locality. Its maximal ideal is
  `IsLocalRing.maximalIdeal C`; a separately named ideal n would duplicate that
  unique ideal.
- Completeness is `[IsAdicComplete (IsLocalRing.maximalIdeal C) C]`, including
  separatedness and completeness for the maximal-ideal adic topology. This is
  exactly the completeness companion recorded by `def-weil-pbc-adic-completion`.
- Equidimensionality of Spec C is `hequidim`: for every pair Z, W in
  `irreducibleComponents (AlgebraicGeometry.Spec (CommRingCat.of C))`,
  `topologicalKrullDim Z = topologicalKrullDim W`. Thus dimensions are those of
  the actual component subspaces, with the recorded Mathlib definitions. This
  directly spells out the property; it introduces no alternate spectrum or
  component notion.
- The finite number of variables is `(r : ℕ)`, with polynomial ring
  `MvPolynomial (Fin r) C`. This includes r = 0.
- The ideal n' is `(M : Ideal (MvPolynomial (Fin r) C)) [M.IsMaximal]`.
  The hypothesis `hclosed : M.comap (MvPolynomial.C : C →+*
  MvPolynomial (Fin r) C) = IsLocalRing.maximalIdeal C` is precisely that it lies
  over n. No rationality, prescribed generators, or residue-field equality is
  assumed. Maximality supplies primality for `Localization.AtPrime M`.
- The first conclusion is `IsCatenaryRing (Localization.AtPrime M)`, using the
  dependency's finite chain bound and equality of saturated chain lengths.
- The second conclusion explicitly asserts equal `topologicalKrullDim` for
  every pair of irreducible components of
  `AlgebraicGeometry.Spec (CommRingCat.of (Localization.AtPrime M))`.
- The third conclusion quantifies over every such component Z and asserts
  `topologicalKrullDim Z = ringKrullDim C + (r : WithBot ℕ∞)`. The common dimension
  type retains both infinities and ordinary finite dimensions. The Mathlib
  theorem `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` identifies the
  spectrum and ring dimensions used here.

Statement dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, with `isNoetherianRing_iff_ideal_fg` confirming the ideal
  formulation.
- `def-weil-pbc-adic-completion`:
  `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete` (the recorded
  companion of `AdicCompletion`). Read both compatible-sequence completion and
  the separated/precomplete predicate.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`. Its scheme and topological carrier are used directly.
- `def-weil-irreducible-components`: the node has no `lean` record and is a
  Mathlib leaf; its `mathlib_match` is
  `Mathlib.Topology.Irreducible`, `irreducibleComponents`, defined as maximal
  irreducible subsets. Read the definition and `IsIrreducible`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, defined using chains of irreducible closed sets.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsCatenaryRing`.
  Read its complete signature and the prime-chain and saturation definitions,
  as well as `IsExcellent` and `IsUniversallyCatenary`.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` and the coefficient map `MvPolynomial.C`.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`, the
  localization at the prime complement, with its local-ring structure.

Proof imports correspond to every recorded proof dependency:
`Sheaf.RingTheory.CompleteLocalExcellence`
(`isExcellent_of_isNoetherianRing_of_isAdicComplete`),
`Mathlib.RingTheory.RingHom.Flat` (`RingHom.Flat`),
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`),
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
(`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`),
`WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension`
(`MvPolynomial.ringKrullDim_localizationAtMaximal`),
`Mathlib.RingTheory.Ideal.MinimalPrime.Basic` (`Ideal.exists_minimalPrimes_le`),
and `Mathlib.RingTheory.Spectrum.Prime.Topology`
(`PrimeSpectrum.zeroLocus_minimalPrimes` and
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`). The remaining proof
modules are already public statement imports. No import cycle is introduced.

Edge cases checked before writing:

- r = 0: the localization is C itself; the conclusion is catenarity of the
  complete local ring and the original component dimensions, with addition 0.
- A field as C: this includes all polynomial maximal ideals, not merely
  rational ones, and yields dimension r by Stacks 00OP.
- Non-rational points: C = R[[t]], r = 1, M = (t, x² + 1) is included, and
  yields dimension 2. No hypothesis forces the residue field to equal R.
- Reducible equidimensional C = k[[u,v]]/(uv): both branches have dimension 1,
  so every localized polynomial component has dimension 1 + r. No domain or
  reducedness hypothesis appears.
- Nilpotents, for example C = k[ε]/(ε²), are allowed; the same component
  spectrum has dimension 0, so the answer is r.
- The zero ring is already excluded by Mathlib's nontrivial local-ring
  convention, agreeing with the source. No extra nonemptiness assumption was
  added; a local ring has a maximal ideal and a nonempty spectrum.
- The closed-point hypothesis is essential and not tautological. For
  C = k[[t]], the maximal ideal (tx - 1) of C[x] contracts to (0), not (t);
  its quotient is k((t)) and its localization has dimension 1 rather than
  dim C + 1 = 2. It is correctly excluded by `hclosed`.

Searches actually run (the launcher wrapper logged the external searches):

- `msearch.py`, LeanFinder: "A complete equidimensional Noetherian local ring
  has catenary equidimensional polynomial localizations at maximal ideals over
  its maximal ideal, every component has dimension dim C plus r". Eight hits:
  finite dimension of Noetherian local rings, polynomial height, and dimension
  bounds. None states the required catenarity and component assertion.
- `msearch.py`, Loogle: `"ringKrullDim", "MvPolynomial"`. Six hits, including
  `MvPolynomial.ringKrullDim_of_isNoetherianRing`, computing the global
  polynomial dimension rather than these local component dimensions.
- `msearch.py`, grep, RingTheory:
  `equidimensional|[pP]olynomial.*minimalPrimes|minimalPrimes.*[pP]olynomial`.
  Zero hits.
- `msearch.py`, LeanSearch: "Equidimensional polynomial localizations of
  complete Noetherian local rings at closed fibre maximal ideals are catenary
  and all components have dimension dim C plus r". Eight hits: global
  polynomial dimension, local dimension equals height, and other bounds; no
  exact match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `isCatenaryRing_equidimensional_localizationAtMaximal|[eE]quidimensional|polynomial-closed-fibre-components`
  found no declaration for this node. Existing equidimensional results concern
  schemes over fields, complete intersections, and relative fibres.
- A separate `rg` for `polynomial-closed-fibre-components` in
  `lean/WeilConjectures` found no match. A search for a named definition or
  class `IsEquidimensional` / `equidimensional` in Mathlib, WeilConjectures,
  and Sheaf found no general equidimensional predicate to reuse; the direct
  equal-component-dimension formulation therefore uses the existing notions.

The inherited `lean_removed` record confirms the former module was deleted
and its declaration survives nowhere; it is not an existing theorem to bind.
The inherited cosmetic observation about the absence of a separate ring
Krull-dimension definition edge needs no statement/interface correction:
`ringKrullDim` is Mathlib's established definition, and the topological/ring
bridge is already a proof dependency. No statement fault or
STATEMENT-DISPUTED flag is raised.

Validation: prescribed `scompile.py` compiled the sandbox and library forms
cleanly (3.6 s and 3.8 s). `autoImplicit` is disabled; the single universe and
all binders are explicit. The node's recorded signature is extracted verbatim
from `theorem` to before `:=`; no other node fields change.

## Second reading by Q150

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
