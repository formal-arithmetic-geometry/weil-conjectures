## Worker report

The module `Sheaf.Paper.ResidueControlledFiniteHoms` states
`WeilConjectures.residue_controlled_finite_homs`, with `sorry` as its only theorem proof.
The helper `integralFiniteInternalHom` is the node's displayed finite-level expression
T_n, constructed directly from the two reductions and the existing internal-Hom functor.
It has real data and introduces no independent mathematical notion. No integral
internal Hom, integral reconstruction or output-completeness assertion is introduced.

Source read: the complete node and its proof, and
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/cor-coef-integral-internal-hom.proof.md`.
The source explicitly obtains finite-Tor input reductions from integral-residue-tor
and their uniformly bounded constructible internal Homs from finite-constructible-hom.

Hypothesis and conclusion correspondence:

- Global finite-field datum: `D : FiniteFieldDatum.{u}`; its fields supply the prime p,
  positive exponent, finite field and fixed algebraic closure k. The scheme has
  `[X.Over (Spec (.of D.k))]`.
- Prime l distinct from p: `[Fact l.Prime]` and `_hl : l ≠ D.p`.
- Finite extension E/Q_l: `[Field E] [Algebra (Padic l) E]`
  `[FiniteDimensional (Padic l) E]`. Its ring, uniformizer and finite quotient rings
  are the recorded `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, `Padic.coefficientExtensionRing`.
- Separated finite-type X: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`
  of the structure morphism to `Spec D.k`; properness is not assumed.
- Nonnegative integer d with dim X ≤ d: `d : ℕ` and
  `_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`.
- Completed coefficient ring B: `scalarReductionSource l E X` is the actual category
  of modules over `completedIntegralCommRingSheafUnrestricted`, the inverse limit
  of the constant finite quotient sheaves. This is the ring used in the domain of K,L.
- K,L in integral D^b_c: the ambient `DerivedCategory (scalarReductionSource ...)`
  and `_hK`, `_hL : sfIntegralConstructible ...`. This includes derived completeness,
  constructibility of each reduction, and a common finite support interval.
- K_n,L_n: `(scalarReductionDerivedExtension l E X n).obj K` and its L counterpart.
  The API's n means exponent n+1, as documented in the module. Consequently
  `∀ n : ℕ` covers exactly all positive finite coefficient levels; residue level
  one is `(scalarReductionDerivedExtension l E X 0).obj K`.
- The ordered integer intervals [alpha,beta] and [gamma,epsilon]:
  `(a b c e : ℤ)`, `_hab : a ≤ b`, `_hce : c ≤ e`.
- Residue cohomology vanishes outside those intervals: `_hK₁`, `_hL₁` are the two
  inclusions of `proEtaleCohomologicalSupport` in `Set.Icc a b` and `Set.Icc c e`.
  Since support is precisely nonzero cohomology, these are the stated vanishings.
- T_n: `integralFiniteInternalHom l E X K L n` unfolds to
  `derivedInternalHomOfUniverses` over `proEtaleConstantRing X` of the quotient,
  applied contravariantly to K_n and covariantly to L_n.
- Bounded constructibility of every T_n: the first conjunct is
  `intrinsicFiniteTorsionConstructible l E (n+1) ... X T_n`.
- Tor amplitude over B_n: the second conjunct is `HasProEtaleTorAmplitude X ... T_n`
  with endpoints `c - b - 2 * (d : ℤ)` and `e - a + 2 * (d : ℤ)`.
  This is the recorded universal degree-zero sheaf test, not site-perfectness.
- Cohomological support: the final conjunct puts `proEtaleCohomologicalSupport T_n`
  in `Set.Icc` with those same endpoints. These endpoints occur outside any choice
  and do not depend on n, giving the requested uniformity.

Recorded dependency declarations read and reused (the respective modules are imported):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the coefficient constructions.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact`; `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: reexports the recorded
  completion and coefficient sheaf system used in `scalarReductionSource`.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `WeilConjectures.scalarReductionSource`, `scalarReductionDerivedExtension`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`:
  `AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`: reexports
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`, used on the original site.

The proof-only imports are the recorded modules `IntegralResidueTor`
(`integral_residue_tor`), `FiniteTorAmplitudeSites` (`finiteTorConstructible`),
`FiniteConstructibleHom` (`finite_constructible_derivedHom_proEtale`), and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`
(`AlgebraicGeometry.ProEtale.derivedTensor`). The docstring carries all three proof
steps, including the tensor-unit calculation of the support conclusion.

Edge cases checked before writing: n=1 is included as index zero; no exponent-zero
quotient is substituted for residue level. d=0 leaves [c-b,e-a]. Zero inputs and
empty X have empty support and satisfy each clause; the dimension predicate allows
negative infinity. Intervals of length zero and arbitrary negative endpoints are
allowed. l=p is excluded exactly as in the node. No invertibility, perfectness or
uniform integral output assumption is added. Site objects remain Type (u+1) and
arrows Type u; derivedInternalHomOfUniverses is explicitly specialized accordingly.
The ambient size u is arbitrary, as in the recorded integral constructibility API.

Searches actually run:

- `msearch.py ... leanfinder "Residue cohomology bounds imply uniform Tor amplitude
  for finite reductions of derived internal Hom of constructible integral adic sheaves"`:
  eight hits, on localCohomology.diagram and general derived-category support,
  fractions and injective/projective single-functor facts; no matching estimate.
- `msearch.py ... loogle '"torAmplitude", "Hom"'`: zero hits.
- `msearch.py ... grep 'residue.*(torAmplitude|TorAmplitude)|constructible.*(internalHom|derivedHom)'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Uniform bounds for finite coefficient derived internal
  Hom from residue cohomology of constructible integral complexes"`: eight hits on
  localized shifted Hom, representatives with support bounds, homological complex
  limits and cohomology classes; none states the finite sheaf estimate.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` for residue/Hom combinations found
  generic residue-field maps and other internal-Hom results; a targeted search for
  residue-controlled, residue_controlled, finite_homs found no declaration.
  `grep -rn` for the node id in `lean/WeilConjectures` and `rg` in
  `dag/lean_names_upstream.json` found no attachment.
- `rg` for the proposed two full-name suffixes in Mathlib, WeilConjectures, Sheaf
  and the upstream name table found no collisions.

No statement correction, new node, dependency repair or STATEMENT-DISPUTED fault.
The first prescribed scompile run compiled both the sandbox and library module cleanly
in 2.6 and 2.7 seconds respectively, with no warnings or errors.

## Second reading by Q18

I reopened the node, dependency definitions and delivered signature for a second pass.
This is a self-check; the dispatcher explicitly prohibits starting another agent,
and the maintainer supplies the independent delivery review.
The global datum, prime inequality, finite field extension, structure morphism,
separatedness, the two finite-type conditions, natural dimension bound, integral
constructibility of both objects, two ordered integer intervals, and both residue
support inclusions match the binders individually. The finite-Hom helper has the
correct contravariance and coefficient quotient exponent n+1. Each of the three
conclusions uses that same object; both quantitative conclusions use the literal
[c-b-2d,e-a+2d] interval, with no n-dependent bound. In particular the support clause
is present separately and the conclusion only quantifies over positive finite levels.
No mismatch or change was found in this second reading.
