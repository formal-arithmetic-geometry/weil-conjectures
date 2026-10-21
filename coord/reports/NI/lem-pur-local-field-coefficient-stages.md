## Worker report

Item: `lem-pur-local-field-coefficient-stages`.
Module: `Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages`.
Declaration: `Padic.local_field_coefficient_stages`.
One theorem is stated with `sorry`; no definitions or proofs are added.
The node statement and dependency lists are unchanged.

Source opened: main-20261015 smooth-purity,
`sk-lem-sp-field-extension-towers.proof.md`, Part (1). Its opening finite-free
integer-ring input includes ramification. The node expands that input into the
positive finite coefficient levels needed for rational/qbar purity Steps 1–2.
I also read all seven DAG proof steps and their arithmetic dependency records.

Hypotheses, with no scheme or geometric assumptions:

- The prime is `(l : ℕ) [Fact l.Prime]`.
- `E : Type u`, `F : Type v`, their field and `Algebra (Padic l)` structures,
  and the two `FiniteDimensional (Padic l)` instances are the finite extensions.
  The universes `u` and `v` are independent.
- `Algebra E F` and `IsScalarTower (Padic l) E F` are the inclusion over the
  base field. A field algebra map is injective; no literal subtype assumption
  is needed. Finiteness of F/E follows from its finiteness over the base, and
  is not an extra hypothesis.
- `hcompat` is equality of the upper absolute value on `algebraMap E F x`
  with the lower absolute value. Both absolute values are the dependency's
  extending spectral absolute values.
- The rings R and S are the existing `coefficientExtensionIntegers l E/F`.
  The elements `t`, `v` are arbitrary, not only the dependency's chosen ones.
  `ht` and `hv` say their singleton-generated ideals equal the existing
  `coefficientExtensionMaximalIdeal` in their respective rings.

Conclusion, clause by clause:

- `∃ f` with `(f x : F) = algebraMap E F (x : E)` states the restriction
  of the given field inclusion. This condition determines f uniquely by
  subtype extensionality. It is not a freely chosen scalar map or assumption.
- `@Module.Free ... f.toAlgebra.toModule` and the corresponding
  `Module.Finite` assert finite freeness for exactly that scalar action.
- `∃ e w`, `1 ≤ e`, and `f t = (w : S) * v ^ e` are the positive
  ramification exponent and unit decomposition of the image of t.
- For each `n` with `1 ≤ n`, equality of `Ideal.span {f t ^ n}` and
  `Ideal.span {v ^ (e*n)}` is the equality of the upper principal ideals.
  Quotients by these equal ideals are canonically identical; this renders
  the displayed equality `S/t^n S = S/v^(en) S` without choosing another ring.
- The existential quotient homomorphism g sends the class of x to the class
  of f x. Its equation on `Ideal.Quotient.mk` uniquely determines the induced
  map. The `Module.Free` and `Module.Finite` clauses use g's scalar action,
  not an unrelated action on the same additive group.
- `Finite` and `IsLocalRing` are stated separately for both positive-level
  rings. A positive `N` with both coefficient-prime powers equal to zero
  gives annihilation by powers of l: multiplying any element by that zero
  scalar annihilates it. The proof plan obtains N=n, but the signature only
  asks for a power as in the statement.
- `∀ k, 1 ≤ k → ∃ n, 1 ≤ n ∧ k ≤ e*n` is cofinality in the positive
  integers. Since e≥1, no unramified or identity-extension case is excluded.
- For `1 ≤ m ≤ n`, `qR`, `qS`, `qV` are transitions for the lower,
  base-uniformizer upper, and upper-uniformizer towers. Their formulas on
  residue classes specify the canonical quotient maps uniquely.
- For arbitrary units a of R and b of S, all singleton-power ideals for
  a*t in R, f(a*t) in S, and b*v in S equal the original ideals.
  `HEq` of the quotient projections states equality of these canonical maps
  across the ideal identifications, without introducing a noncanonical
  isomorphism. Scalar maps specified on representatives are also `HEq`.
  A transition is uniquely determined by its composite with the surjective
  quotient projection, so the displayed projection equalities and the qR,
  qS, qV formulas give its independence under unit changes. This is exactly
  independence of the quotient systems and maps, not independence of bases.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, the dependency's recorded declaration.
  Its public import `Sheaf.NumberTheory.Padics.CoefficientExtension` supplies
  `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
  `coefficientExtensionMaximalIdeal`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, `coefficientExtensionRing`, and
  `coefficientExtensionTransition`. Their docstrings and full definitions
  were read. Arbitrary t uses the same Mathlib principal ideals and quotients.
- `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`:
  `Padic.exists_integral_basis`, the existing arithmetic proof input.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`:
  `Padic.extension_integers_dvr` (publicly imported by the coefficient module).
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`, already imported
  through the coefficient construction, is the recorded unit-power leaf.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`:
  `Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField`,
  imported for the finite-quotient proof input. `Ideal.Quotient.factor`
  describes the canonical transition; `Ideal.quotEquivOfEq` describes the
  identity-induced identification of quotients by equal ideals.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`; module finiteness,
  local rings, principal ideals and quotients use the existing Mathlib notions.

Searches made:

- msearch leansearch, query “Finite extensions of p-adic fields have finite
  free integer rings and cofinal ramified residue quotients”: eight hits,
  including PadicInt, finite-field extensions, PadicInt.isFractionRing and
  local-field finite residue fields; none states this theorem.
- msearch leanfinder, same query: eight hits including the local-field
  finite-residue-field instance, the Valued.integer finite-quotient lemma,
  ramification bounds, and number-field quotient results; no full match.
- msearch loogle, `IsDiscreteValuationRing, Module.Free`: zero hits.
- msearch grep, `coefficientExtension|ramification`, NumberTheory/LocalField:
  zero hits. Direct rg in Mathlib's quotient, DVR and valued-field files
  located the component signatures above.
- Direct rg for `coefficientExtension|local_field_integral|localFieldIntegral`
  in the upstream and Sheaf sources located the recorded constructions and
  integral-basis theorem. The upstream `PadicAlgCl.integersMap`,
  `finite_integersMap`, `integersShrinkMap`, `finite_integersShrinkMap`, and
  `free_integersShrinkMap` in `WeilConjectures.NumberTheory.Padics.IntegersFinite`
  were read: they use fields embedded in PadicAlgCl and its integer rings,
  and do not state the arbitrary-uniformizer, ramified finite-stage,
  cofinality and unit-independence clauses of this node. The recorded
  coefficient-extension interface is used here.
- Direct rg for the item id in upstream WeilConjectures found no attachment;
  `local_field_coefficient_stages|coefficient.*stages|ramified.*coefficient`
  in both libraries and `dag/lean_names_upstream.json` found no full match.
  The proper finite-coefficient-extension modules concern derived functors,
  not this arithmetic input. No notion is newly defined.

Edge cases checked before writing:

- E=F, t=v: e=1, scalar maps identities, all clauses hold.
- An unramified extension: e=1, residue extension can have any finite degree.
- A ramified quadratic extension of Q_2 with t=2 and v a square root of 2:
  e=2; S/t^n is free over R/t^n even though S/v^n need not be.
- n=1: lower residue field and upper ramified Artinian ring, both finite
  local rings; the upper quotient need not be reduced.
- n=0 is excluded only from the positive-stage locality assertion; ideal
  independence and projection equality remain valid at n=0 (zero quotient).
- m=n and identity transitions; arbitrary positive k in cofinality.
- l=2, arbitrary units, and unrelated ambient universes u,v are retained.

No statement correction, dependency repair, new node, or mathematical dispute.

## Second reading by NI

A second pass by the same dispatcher-started worker reopened the full node,
its seven-step proof and the delivered signature. No second agent was started,
following the explicit brief; independent review is by the maintainer.
I checked every hypothesis and conclusion against the mapping above. In
particular, the upper finite-free quotient is S/(f(t)^n), with equality to
S/(v^(e*n)), not S/(v^n). The two module actions are explicitly those of the
canonical characterized maps. Both positivity conditions are present, and
uniformizers are arbitrary. The finite/local assertions cover both rings;
cofinality and independence cover their maps as well as the ideals.
The repeated transition-map comparison clauses initially exceeded Lean's
elaboration budget. They were replaced by equality of the quotient projections;
the transition formulas and surjectivity determine exactly the same maps.
I changed the initial quantitative annihilation bound to an existential power,
matching the node's phrasing. No mathematical clause or hypothesis was lost.

Validation uses scompile.py and the prescribed deliver2.py dry run.
