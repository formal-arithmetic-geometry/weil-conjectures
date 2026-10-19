## Worker report

The retained module `lean/Sheaf/Paper/LocalizingClosureCtfEqualsBc.lean` states
`AlgebraicGeometry.ProEtale.localizingClosure_ctf_equals_bc` and defines
`localizingClosureCtfEqualsBcAssertions`.  The theorem fixes `ℓ` with
`[Fact ℓ.Prime]`, a qcqs `Scheme.{u}` (`[CompactSpace X] [QuasiSeparatedSpace X]`), a
commutative condensed ring object `Λ` (`[MonObj Λ] [IsCommMonObj Λ]`), and the displayed
five-coefficient disjunction `hΛ` (continuous `ℤ_ℓ`, continuous `ℚ_ℓ`, a finite
extension's valuation ring or field, or the finite-subextension-valued algebraic closure).
The conclusion is the assertion predicate followed by the field-coefficient specialization
with Tor interval `[0,0]`.

The assertion predicate renders every clause of the node as follows.

* For every constructible module `M`, the degree-zero `singleFunctor` object has Tor
  amplitude `[-1,0]`.
* For every bounded constructible `K`, integers `a ≤ b`, and homology concentrated in
  `[a,b]`, `K` has Tor amplitude `[a-1,b]`.
* The object properties `constantModelBoundedConstructible ⊓ finiteTorAmplitude` and
  `constantModelBoundedConstructible` are equal, and their `CategoryTheory.localizingClosure`
  properties are equal.
* For every finite discrete commutative ring `A` and qcqs `T`, the finite-coefficient
  property using `Profinite.continuousCoefficientRingObj A` is triangulated and stable under
  retracts (the `continuousCoefficientRingObj` convention is used exactly here).
* `scalarFiniteRingExample ℓ` records that the quotient of `ℤ/ℓ²` by `ℓ` is finite but has
  no finite projective resolution, that the explicit mapping-cone two-term complex
  `[A \xrightarrow{ℓ} A]` is `DerivedCategory.IsPerfectRingComplex`, and that its residue
  module in degree zero is not perfect.
* `constantFiniteRingExample ℓ` pulls the same residue module through
  `upperStarFromPoint` to `Spec k` and states constructibility together with failure of finite
  Tor amplitude for every separably closed field `k`.
* `finiteRingTruncationFailure ℓ` states that at every such `Spec k` there is a finite-Tor
  bounded constructible object whose standard lower truncation
  `(DerivedCategory.TStructure.t.truncGE 0).obj K` is not finite-Tor.  Thus the finite
  coefficient `Dctf` is thick by the preceding clause but is not truncation-stable.

The scalar helper definitions use the genuine quotient module and a mapping cone of the
multiplication-by-`ℓ` map; no data is `sorry`.  The constant example uses the cokernel of
`ℓ • 𝟙` in the condensed module category and its canonical point pullback.  The theorem
and all helper definitions are statement-only; the theorem proof is `sorry` as required for
stage 2.

Dependencies used in the statement are `Sheaf.Topology.ProfiniteCondensedRing`,
`Sheaf.Paper.CondensedConstantConstructibility` (constructible and bounded-constructible
properties), `Sheaf.Paper.ConstantModelTorAmplitude` (the well-definedness interface),
`Sheaf.Paper.LocalizingClosureExistence` (`localizingClosure_exists`), and
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`
(`DerivedCategory.IsPerfectRingComplex`). The upstream qlbar ring
`Profinite.padicAlgClRingObj`, from
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, is used directly in `hΛ`.
The current dependency binding supplied by Q83 is used; this packet contains no change to
`sk-def-sfb-qlbar-condensed`. Its earlier delivered signature beginning with `def` was the
tool's verbatim form; the previous report's claim about `noncomputable` was inaccurate.

Edge cases checked: the zero module and empty scheme; rank-zero finite presentations; `a=b`
and vanishing extreme cohomology; integral `[-1,0]` versus field `[0,0]`; empty strata and
covers; the `ℓ=2`, `A=ℤ/4` periodic resolution; the two-term perfect complex and its two
residue cohomology modules; separably closed point schemes; and the lower-truncation witness.

Searches made: `msearch.py` (`grep` for `TorAmplitude|Dctf|Dbc|constructible.*Tor`,
`leanfinder` for the integral/field assertions and finite-subextension coefficient ring,
`loogle` for `TorAmplitude`, `projectiveDimension`, and truncation declarations), `rg` over
`WeilConjectures/` and `lean/Sheaf/`, and `grep` over `dag/nodes/`.  No duplicate theorem or
usable Mathlib declaration for the item was found; `DerivedCategory.IsPerfectRingComplex` and
`ModuleCat.HasFiniteProjectiveDimension` were the exact existing declarations used.

The theorem docstring now lists all twelve source proof steps separately, including the
periodic-resolution, perfect-two-term, and truncation counterexamples (H8 repair).  No
`STATEMENT-DISPUTED` finding or node fault remains.


## Second reading by Q10

Repair self-check against the returned immutable head `a496697bf3fb`, the current shared
node, the source paragraph, and the saved Lean module: the only differences from the returned
module are docstrings. The prime hypothesis is `[Fact ℓ.Prime]`; qcqs is
`[CompactSpace X] [QuasiSeparatedSpace X]`; the commutative condensed coefficient object has
`[MonObj Λ] [IsCommMonObj Λ]`. The disjunction `hΛ` covers the five scalar choices, with
one existential branch covering both the valuation ring and field of a finite extension.
The assertion predicate retains the module bound `[-1,0]`, the bounded-complex bound
`[a-1,b]`, the equality of the two object properties and their localizing closures, finite-ring
thickness, and all three finite-ring example predicates. The final theorem conjunct retains
the field bound `[0,0]`. No mathematical mismatch was found in this repair reading.

H2 repaired: removed the sandbox dependency-node copy, so delivery leaves the current Q83
record and its declarations list intact. Removed the obsolete Dependency modules section
and corrected the inaccurate claim about the tool's verbatim `def` signature.
H8 repaired: all eight helpers and `localizingClosureCtfEqualsBcAssertions` now name the
source place and carry `(blueprint: det-def-localizing-closure-ctf-equals-bc)` in their own
docstrings. All eight helpers are listed in `lean.declarations`, alongside the assertion
predicate and theorem. Their data and all mathematical signatures are unchanged; the
only postponed proof is the named theorem with its twelve-step proof docstring.
