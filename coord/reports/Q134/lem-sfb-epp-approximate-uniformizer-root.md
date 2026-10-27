## Worker report

The module `Sheaf.RingTheory.SeparableApproximateUniformizerRoot` states
`IsDiscreteValuationRing.exists_separable_approximate_uniformizer_root`.
Its only theorem has proof `sorry`; no definitions or auxiliary claims are introduced.
The node is unchanged apart from its `lean` attachment.

Source checked: `literature/stacks-project/more-algebra.tex`,
`lemma-make-degree-q-extension`, Tag 09EW (also checked against
https://stacks.math.columbia.edu/tag/09EW). Its characteristic-p construction is
`X^q - pi^(h+q-1)*X - pi`. Completeness follows from the finite free quotient
and the cofinal maximal-ideal powers, as in the node's seven-step proof.
The latest blueprint was searched for the auxiliary uniformizer-approximation
statement; the node already records its historical supporting role rather than
claiming to be a current blueprint unit's statement.

Hypothesis and conclusion correspondence:

- Prime p: `(p : ℕ) (hp : p.Prime)`.
- R is a DVR: `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Mathlib's class includes the local principal
  ideal ring condition and nonzero maximal ideal, so excludes fields.
- Characteristic p: `[CharP R p]`.
- Completeness: `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`;
  this includes Hausdorffness as required by the dependency definition.
- Fraction field E: `(E : Type v) [Field E] [Algebra R E]
  [IsFractionRing R E]`.
- Uniformizer pi: `(pi : R) (hpi : Irreducible pi)`. This is equivalent to
  `maximalIdeal R = Ideal.span {pi}` by the recorded Mathlib DVR interface.
- Integers r >= 1 and h > 1: `(r : ℕ) (hr : 1 ≤ r) (h : ℕ) (hh : 1 < h)`.
  Natural numbers cover precisely these positive integer ranges. Everywhere
  q is expanded as `p ^ r`, without introducing a hidden let binder.
- Extension E1/E: existential `E1 : Type v`, `Field E1`, `Algebra E E1`.
  The additional existential `Algebra R E1` and `IsScalarTower R E E1`
  specify the induced R-algebra structure, not an additional mathematical
  hypothesis on the given rings. Tower compatibility forces the base map to
  be the composite R -> E -> E1.
- Separability: existential `Algebra.IsSeparable E E1`, which includes
  algebraicity by Mathlib's definition.
- Degree q: `Module.finrank E E1 = p ^ r`. The right side is positive;
  in particular the zero finrank of an infinite-dimensional space cannot
  satisfy this clause, so it also enforces finiteness.
- R1 is exactly the integral closure: every occurrence is the actual
  Mathlib `integralClosure R E1`, not a chosen unrelated ring.
- R1 is a DVR: existential `IsDiscreteValuationRing (integralClosure R E1)`.
  Its domain and commutative-ring instances are inherited from the field E1.
- R1 is complete: `IsAdicComplete (maximalIdeal (integralClosure R E1))
  (integralClosure R E1)`.
- Equality of residue fields: `∃ e : ResidueField R ≃+* ResidueField R1`
  with `∀ x : R, e (residue R x) = residue R1 (algebraMap R R1 x)`.
  The displayed compatibility ensures the canonical residue-field
  identification, not merely an abstract isomorphism. Since `residue R`
  is surjective, the compatibility uniquely determines e. This expresses
  exactly equality after canonical identification across different types.
- Extended-maximal-ideal formula: `Ideal.map (algebraMap R R1)
  (maximalIdeal R) = maximalIdeal R1 ^ (p ^ r)`.
- Same uniformizer and two coefficients: `∃ t b b' : R1, Irreducible t ∧ ...`.
- First identity: `t ^ (p ^ r) = algebraMap R R1 pi +
  algebraMap R R1 pi ^ h * b`.
- Second identity: `t ^ (p ^ r) = algebraMap R R1 pi +
  t ^ (h * p ^ r) * b'`. Multiplication precedence gives h*q.
  The common left-hand side encodes the chained equality in the node.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`, in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (class and equivalence read).
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`, in
  `Mathlib.RingTheory.AdicCompletion.Basic` (the class extends IsHausdorff and
  IsPrecomplete).
- `def-pc-field-extension`: `Algebra`, in `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`, in
  `Mathlib.FieldTheory.Separable` (signature, docstring and algebraicity instance read).
- `def-weil-pbc-integral-closure`: `integralClosure`, in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (carrier IsIntegral R x).
- `IsLocalRing.ResidueField`, `IsLocalRing.residue`, and the canonical-map
  interface from `Mathlib.RingTheory.LocalRing.ResidueField.Basic`;
  `Module.finrank` from `Mathlib.LinearAlgebra.Dimension.Finrank`.

Plain proof imports retain the already stated proof dependencies:
`Mathlib.RingTheory.AdjoinRoot` (`AdjoinRoot.powerBasis'`,
`Polynomial.Monic.free_adjoinRoot`, `Polynomial.Monic.finite_adjoinRoot`),
`Mathlib.FieldTheory.SeparableDegree`
(`IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`),
`Sheaf.RingTheory.ValuationRingNormal`
(`isDomain_isIntegrallyClosed_of_fractionField_element_or_inverse`), and
`WeilConjectures.RingTheory.FiniteModuleComplete`
(`finite_module_complete_over_complete_noetherian`). Their full relevant
signatures and docstrings were read. Polynomial separability is supplied by
`Mathlib.FieldTheory.Separable`, already a public statement import.
`lem-sfb-eisenstein-quotient-dvr` currently has neither a Lean record nor
Mathlib match, so there is no module to import yet; it is a proof-only
prerequisite and introduces no notion missing from this statement.

Edge cases checked before writing:

- p=2, r=1, h=2 gives q=2, N=3 and f=X^2-pi^3*X-pi; its
  derivative is the nonzero constant -pi^3. With b=pi*t the first identity
  is immediate from the equation. The unit u=1+pi^2*t gives the second.
- For general positive r, q>=2 and N-1>=1; the linear coefficient is
  nonzero over E, so the constructed degree-q extension is separable even
  when r>1. No assumption that p is invertible in R is introduced.
- R cannot be zero or a field, and pi cannot be zero or a unit by the
  DVR and irreducibility hypotheses. The residue field need not be perfect,
  finite, or algebraically closed.
- The two input universes u and v are independent. The existential E1 may
  be taken in E's own universe v, since its degree is finite (the quotient
  E[X]/(f) is in Type v); this does not restrict the input R or E.
- r=0 and h<=1 are excluded exactly as in the node. No new restrictions
  on the residue field, fraction field, or ramification are imposed.

Searches for an existing statement (all using the required wrapper):

- leanfinder: "A complete discrete valuation ring of characteristic p admits
  a separable totally ramified extension of degree p power with uniformizer
  approximating a root of the original uniformizer" returned eight hits:
  PreTilt/untilt declarations, Tilt, Field.henselian, and
  Valuation.exists_pow_Uniformizer. None constructs this extension.
- leansearch: "A discrete valuation ring in characteristic p has a separable
  totally ramified extension of degree p^r with an approximate root of its
  uniformizer" returned eight hits, including DVR constructors and
  Valuation.exists_pow_Uniformizer. None states the result.
- loogle: `IsDiscreteValuationRing, Algebra.IsSeparable`: zero hits.
- grep: `uniformizer.*separable|separable.*uniformizer|approximate.*[Uu]niformizer`:
  zero Mathlib hits.
- Project rg over `lean/WeilConjectures`, `lean/Sheaf` and the upstream name
  index for `09EW|approximate_uniformizer|approximateUniformizer|
  separable_uniformizer|separableUniformizer`: no existing declaration.
  Searching for the item's ID in WeilConjectures also found no declaration.
  Broader uniformizer searches found roots under invertibility hypotheses
  and results about a given extension of a strictly henselian DVR; these
  do not give this characteristic-p separable approximation construction.

No missing notions, dependency repairs, statement corrections, or disputed
statements were found. The module's docstring reproduces all seven proof steps.
Server compilation through `scompile.py` completed cleanly (1.7 seconds for
sandbox and library checks), with no unexpected warnings.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
