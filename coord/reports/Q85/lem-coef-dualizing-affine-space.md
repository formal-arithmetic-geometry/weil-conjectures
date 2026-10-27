## Worker report

The module `Sheaf.SixFunctors.AffineDualizingCoefficient` states
`AlgebraicGeometry.Etale.affine_dualizing_coefficient`. Its proof is `sorry`.
All supporting definitions have complete data. They assemble existing canonical
functors, adjunctions and maps, or spell out the clauses of this same node as
propositions. No definition is chosen from a mere existence statement.

The stage-1 PASS by Q118 is the reviewed split on which this stage-2 statement
builds. This delivery does not split the node again. This packet repairs the independent stage-2 return on immutable head
`b0e977539402`; its accepted mathematical clauses are retained.

Hypotheses and clauses, in the order of the node:

- The finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`. Its fields
  specify the prime p, q=p^a, the finite field and its algebraic closure k.
  `S = Spec (.of D.k)` is the geometric point, in the original scheme universe.
- The prime ell is `l : ℕ`, `[Fact l.Prime]`, and `_hl : l ≠ D.p`.
  `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` are exactly the finite extension of Q_l.
- Levels are `m n : ℕ+` and `hmn : m ≤ n`. Thus the complete range
  `1 ≤ m ≤ n` is covered, with actual levels m,n rather than an implicit shift.
  `RingHom.ulift (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn))`,
  with the explicit recorded coefficient ideals at levels n and m, is the quotient map
  from `ULift (Padic.coefficientExtensionRing l E n)` to the corresponding
  m quotient. Its definition is the lifted `Ideal.Quotient.factor` for powers
  of the recorded uniformizer ideal. The ULift is solely the established
  module-sheaf size convention; it preserves the rings and the quotient map.
- The dimension is unrestricted `r : ℕ`. `affineTraceTower S r` and
  `affineTraceProjection S r` are the existing coordinate model of A^r_S and
  its structure morphism. `affineTraceAffineSpaceIso S r` is its existing
  canonical polynomial-coordinate isomorphism to Mathlib's affine r-space.
  In particular the zero-dimensional tower is literally S with identity map.
  Its separated and finite-type properties are supplied by the existing
  `affineTraceProjection_properties` and its instances, not extra hypotheses.
- Ordinary small etale derived module categories are `DerivedCategoryModule`.
  F is `rightDerivedLowerShriek`, G is `rightDerivedUpperShriek`, omega is
  `dualizingComplex (ModuleCat R) (affineTraceProjection S r)`, and epsilon is
  `(rightDerivedUpperShriekAdjunction ...).counit.app (𝟙_ (DerivedCategoryModule R S))`.
  These are the published ambient functors on whole unbounded categories.
  The introductory notation for a general separated finite-type Y is provided
  by these same existing functors and `ExceptionalCoefficients.dualizingScalarMap`;
  the theorem's conclusion concerns the stated specialization Y=P.
- T is `scalarExtension` along the actual quotient. The source and target retain
  different coefficient categories. `scalarTensorIso` in the imported interface
  identifies its restricted value with derived tensor by B; it is characterized
  on K-flat representatives. No flatness of B/A is assumed.
- Bounded constructibility for each of omega_A and omega_B is exactly
  `DerivedCategory.isBoundedConstructible`; this uses the dependency's finite
  constructible cohomology and finite vanishing interval. Each finite-Tor premise
  is `∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn ... a b omega`.
  That recorded predicate tests EVERY module sheaf in degree zero. Both premises
  appear separately for both named dualizing objects inside
  `AffineDualizingCoefficientAssertion`, before any conclusion.
- The canonical comparison c is `ExceptionalCoefficients.compactSupportMap`,
  computed with the same chosen compactification as F, by the proper scalar
  mate followed by direct image of the open scalar comparison. It is the
  unbounded ordinary-etale coefficient arrow, rather than an arbitrary map.
  The first conclusion explicitly asserts its invertibility at omega_A, so
  the total inverse `comparisonInverse` used in the next clauses is its inverse.
- u is the EXISTING `ExceptionalCoefficients.dualizingScalarMap`. Its definition
  transposes `comparisonInverse`, followed by scalar extension of the A-counit,
  and then the scalar-unit comparison. `AffineDualizingMateEquation` writes
  the exact equation `F_B.map u ≫ epsilon_B = c_inverse ≫ T(epsilon_A) ≫ unit`.
  The next clause states that every arrow satisfying it equals this u. Thus
  neither an arbitrary isomorphism nor a freely supplied mate is substituted.
- The main `IsIso (ExceptionalCoefficients.dualizingScalarMap ...)` is the
  claimed invertibility of that specified map. The next two `IsIso` clauses
  assert invertibility of the actual chosen-adjoint counits for A and B.
- The shared modulus is existentially `N=l^e`, with `(N:A)=0`, `(N:B)=0`
  and `IsUnit (N : Γ(S, ⊤))`. These are conclusions describing the choice of
  annihilator; they add no hypotheses. N is positive since l is prime.
- The twists are EXACTLY `Scheme.finiteEtaleTateTwist`, whose first line is
  sheafified extension of the existing roots-of-unity sheaf from Z/N and whose
  subsequent values are its tensor powers. They are not the abstract `HasTateTwist`
  coefficients or pro-etale twists. The displayed isomorphisms identify each
  tower-right-adjoint value with its finite Tate r-power in degree zero shifted
  by `2 * (r : ℤ)` in the DERIVED category.
- `affineDualizingTowerComparison` is a real recursive construction from the
  canonical unbounded identity and composition comparisons. After transporting
  the existing tower adjunction along it, `affineDualizingTowerIso` uses
  `Adjunction.rightAdjointUniq` for the two adjoints of the SAME whole-category
  F. `AffineDualizingTraceNormalization` states exactly that the chosen counit
  equals F of this isomorphism, the inverse tower comparison and the actual
  `affineTraceCounit`, and the explicit constant-to-derived-unit isomorphism,
  in that order. This is the explicit coordinate-tower
  normalization, with no independent trace map chosen.
- The ordinary coefficient identifications c(d) are fixed by
  `AffineDualizingTateNormalization`: at zero, the quotient on constant sections;
  at one, `finiteEtaleTateOneGenerator A N ... a z` maps to the B generator
  with coefficient phi(a); at every higher power, the ordinary oplax tensorator
  followed by the previous and first-power maps. These specify the balanced
  rank-one maps rather than arbitrary isomorphisms of line sheaves.
  `affineDualizingShiftedSingleMap` uses the EXISTING
  `WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T F`, followed
  by `(DerivedCategory.singleFunctor _ 0).map c`, to derive that ordinary
  map, then the adjunction-induced shift constraint.
  Its `IsIso` clause supplies precisely T(A_P(r)[2r]) ≅ B_P(r)[2r]. Composing
  with T of `affineDualizingTowerIso` and the displayed Tate identification
  therefore identifies the source of the actual u with B_P(r)[2r]. The family
  c(d) records the tensor-power recursion specifying this comparison, not a
  separate assumption or a coefficient-trace compatibility theorem.
- For r=0 the last implication gives an equality with the LITERAL
  `𝟙 (𝟙_ (DerivedCategoryModule B S))`. Its source coordinates are inverse scalar unit,
  scalar extension of the inverse identity-adjunction dualizing isomorphism,
  then u, then the target identity-adjunction isomorphism. Thus it includes
  the requested identity-adjunction normalization even though the published
  exceptional adjoints are chosen and not definitionally identity functors.

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction`:
  `AlgebraicGeometry.Etale.nonempty_affineSpaceAmbientAdjunction`, on the whole
  unbounded categories; the theorem's proof plan uses it for the Tate normal form.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, the unbounded D(j_!) then R(q_*)
  composite, and its chosen-compactification notation `rightDerivedLowerShriek`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint` and
  `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`:
  the ambient left-adjoint theorem, `rightDerivedUpperShriek` and its adjunction.
- `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`: `dualizingComplex`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor` and `.Coefficients`:
  `derivedTensor`, `DerivedCategoryModule`, `hasTorAmplitudeIn` and the unit.
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` reexports the recorded interval
  notion without replacing it by the lower-bound variant.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `DerivedCategory.isBoundedConstructible`.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  documented Padic extension-ring/uniformizer conventions.
- Mathlib morphism classes `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`
  (modules `.Morphisms.Separated`, `.FiniteType`, `.QuasiCompact`, `.Proper`),
  through the published affine-coordinate-tower instances.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`: `exists_affineSpaceTopTrace`,
  reexporting the ordered `affineTraceAdjunction`, `affineTraceCounit`, tower
  geometry and ordinary finite coefficient units.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: ordinary finite Tate
  sheaves, their roots generator, and the stated normalized pullback interface.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`:
  `compactSupportCoefficientComparisonPlus` and its coefficient tensor models.
  The existing unbounded compact-support scalar mate from
  `Sheaf.Paper.ExceptionalCoefficientMaps` supplies its whole-category version;
  the actual `dualizingScalarMap` is reexported by
  `Sheaf.Paper.ExceptionalCoefficientComparison`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleLowerShriekId`, `unboundedEtaleLowerShriekCompIso` and
  `rightDerivedLowerShriekIso`, used in the real tower construction.
- `WeilConjectures.SixFunctors.Etale.Derived.Invertible`:
  `singleFunctorObjUnitIso`, reused by `affineDualizingUnitIso` to make the
  constant sheaf/derived tensor-unit identification explicit. This avoids costly
  implicit conversions while preserving the canonical coefficient unit.
- `Mathlib.CategoryTheory.Adjunction.Unique`: `Adjunction.rightAdjointUniq`.
- `Sheaf.Paper.VectorPurityScalarSingle`:
  `WeilConjectures.PurityFiniteSetting.purityScalarSingleMap`, the generic
  scalar/single adjunction comparison owned by the definition node
  `def-pur-vector-purity-scalar-single`. Its full current server source was
  read using `scompile.py --source`; it applies to arbitrary coefficient
  sheaves and makes no flatness assumption. The ordinary map c is applied
  afterward by the existing derived single functor.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, owning node
  `def-weil-l-adic-coefficient-extension`: `Padic.coefficientExtensionRing`,
  `Padic.coefficientExtensionIdeal`, and `Padic.finite_coefficientExtensionRing`.
  The quotient arrow is inlined using `Ideal.Quotient.factor`, with
  `Ideal.pow_le_pow_right hmn` expressing the inclusion of the n-th ideal
  power in the m-th. `RingHom.ulift` implements the required universe lift.
  Two `letI` binders register its positive-level finiteness directly from
  the recorded theorem and `Equiv.ulift.finite_iff`; they are constructed
  instances, not additional assumptions.

The added stmt_deps are the landed definition owners
`def-pur-exceptional-coefficient-tensor-maps`,
`def-pur-vector-purity-scalar-single`, and
`def-weil-l-adic-coefficient-extension`.
The theorem nodes `lem-sp-p1-splitting-scalar` and
`lem-sf-compact-coefficient-composition` have both been dropped: their
conclusions are not needed to state this item. Their modules are not imported.
No new node or dependency module is needed. All original statement and proof
dependencies are retained.
The proof-only imports include the stated Tate-line flatness, connected scalar
endomorphism detector, affine-line connected components, localized extension-zero
linearity, ringed pushforward linearity, change-of-rings model and open-site
localization declarations. The theorem docstring gives all seven reviewed proof
steps and their named dependencies.

Edge cases checked before writing: r=0 uses identity projection and identity
adjunction coordinates; m=n is the identity quotient; m=1 is the smallest allowed
level; n>m permits a genuinely nonflat quotient. The finite-Tor premise is on
omega, never on B/A. Affine space over a field is nonempty including r=0; the
connected-line detector is not applied to an empty scheme. Universes are bound
explicitly: schemes and coefficient field in u, coefficient rings and sheaf
modules in u+1, derived categories as published. No additional universe equality
or boundedness condition on the ambient adjunction is imposed.

Searches (actual msearch.py calls, with records in the sandbox searches.jsonl):

- LeanSearch: “The coefficient change map for the dualizing complex of affine
  space defined by its adjunction counit is invertible”. Eight generic hits,
  including `Adjunction.inv_counit_map`; none states the etale coefficient result.
- LeanFinder: “The counit-defined coefficient reduction map on the etale dualizing
  complex of affine space is an isomorphism”. Eight affine-coordinate hits,
  no existing theorem with this conclusion.
- Loogle: `CategoryTheory.Adjunction.rightAdjointUniq`. Twelve results; the
  uniqueness construction and its counit equation are reused, not the desired
  affine-space coefficient theorem.
- Mathlib grep: `dualizing.*coefficient|coefficient.*dualizing|affine.*counit`:
  no hits. Earlier narrower grep and Loogle searches also found no exact result.
- Project rg, in BOTH lean/WeilConjectures and lean/Sheaf, for the exact blueprint
  id and the new full declaration names: no existing statement. Concept searches
  found `FiniteDualizing`, `ExceptionalCoefficientComparison`, `AffineSpaceTopTrace`,
  and the connected-line detector. `FiniteDualizing` is the downstream general
  theorem, not this node, and is not imported. Its ordinary maps already use
  the same exceptional-coefficient constructions reused here. Searches for Tate
  scalar comparisons originally found `p1ScalarSingleMap`. The repair uses
  the definition-owned `purityScalarSingleMap` instead, as requested by the
  independent review; its module and DAG node were read in full. No private copy
  of the coefficient unit, derived scalar extension, dualizing complex, Tate
  twist, quotient ring or canonical compact-support comparison was introduced.

No statement correction and no STATEMENT-DISPUTED flag. The source was read at
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md`,
especially paragraphs 2--3, and the full seven-step reviewed DAG proof.

## Returned-delivery repair

H2/H4, immutable head `b0e977539402`: repaired both unnecessary theorem
statement dependencies. The derived degree-zero map now reuses the landed
`def-pur-vector-purity-scalar-single` declaration, composed with the ordinary
arrow under the derived single functor. The coefficient quotient is the
literal `RingHom.ulift (Ideal.Quotient.factor ...)` on the ideals from
`def-weil-l-adic-coefficient-extension`. Finiteness comes directly from that
node's existing positive-level theorem; there is no replacement finite-ring
assumption. Dropped both flagged theorem stmt_deps and imports.

Landing blocker: removed the public import of the quarantined
`Sheaf.Paper.P1SplittingScalar`; the replacement module's live server source
was checked. No quarantine path is used by this delivery.

Comparison with current main: the base item still has its original thirteen
stmt_deps and no Lean record. Apart from the new lean record, this packet
only adds the three landed definition owners listed above; it changes no
statement, source, reviewed split, proof, or proof_deps. The retained saved
packet initially passed `deliver2.py --no-push` as `95a4ba9fa2d`; this semantic
repair is required by the independent return despite that mechanical pass.

## Second reading by Q85

Self-check of the repaired node and file (the maintainer supplies the
independent review): all original hypothesis/clause matches listed in the
Worker report are retained. The finite quotient has the same source n and
target m: `m ≤ n` yields the required ideal inclusion, including equality.
The scalar/single arrow now factors through degree zero of ordinary scalar
extension of F, then degree zero of c, so its endpoints and its adjunction
normalization agree with the reviewed arrow. The derived shift is unchanged.
The constructed finite instances add no hypotheses. All ten declarations
remain recorded, all variables/universes are explicit, and only the main
named theorem has a postponed proof. The counit equation, uniqueness,
IsIso assertions, coordinate-tower normalization, pinned P1 data, Tate
normal form, generator recursion and literal zero-dimensional identity are
unchanged. Both constructibility and finite-Tor premises remain on both
named omega objects; m=n and nonflat n>m remain covered.

Validation: fresh `scompile.py Q85 lem-coef-dualizing-affine-space`
compiled the repaired module under its sandbox name (32.9 s) and library
name (54.8 s), with no compiler messages. The only postponed proof is
`affine_dualizing_coefficient`. Delivery preflight is run again on this
repaired packet before pushing.
