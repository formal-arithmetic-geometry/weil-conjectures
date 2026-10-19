## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality` states
`AlgebraicGeometry.curve_finite_level_poincare_duality`, with one sorry, and constructs the
raw canonical map `AlgebraicGeometry.curveFiniteLevelCupTrace` with real data. Nothing is proved.
The latter specializes the existing cup and degree-normalized trace; it chooses neither an
arbitrary pairing nor a primitive root. The two already landed notion nodes are added to
stmt_deps, as authorized by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES).

Hypothesis and clause correspondence:

- The base field is `k₀ : Type u` with `[Field k₀]`; `K`, its algebra structure, and
  `[IsAlgClosure k₀ K]` express the algebraic closure. No finite-field hypothesis is added.
- The curve `C₀/k₀` is `C₀ : Scheme.{u}` with `C₀.Over (Spec (.of k₀))`.
  `SmoothOfRelativeDimension 1` expresses smooth dimension one, `IsProjective` expresses
  projectivity, and `GeometricallyConnected` expresses geometric connectedness.
  Properness, separatedness and finite type follow from these existing classes.
- `C₀.baseChangeField k₀ K` is the existing actual categorical pullback, precisely C in (3.4).
  There is no replacement by an unrelated algebraically closed curve and no extra class
  assumed on this base change. In the helper, smoothness and properness are inferred on the
  pullback, and connectedness is `GeometricallyConnected.connectedSpace_of_subsingleton`.
  `topologicalKrullDim_eq_of_smoothOfRelativeDimension` supplies dimension one; these existing
  facts build the `IsConnectedCurve` structure required by the published trace.
- `ell : ℕ`, `[Fact ell.Prime]`, `[CharP k₀ c]`, `hell : ell ≠ c` spell out the prime and
  characteristic conventions of the cited twist definition. `n : ℕ`, `hn : 1 ≤ n` spell out
  its positive-level convention. Characteristic on K is transported along the injective
  algebra map, and algebraic closedness is obtained from `IsAlgClosure`, neither assumed.
- `Sheaf.H (...constantZMod (ell ^ n)) 1` is H¹(C,A_n), in the existing ordinary Ext encoding.
  The record for `def-weil-pbc-etale-cohomology` explicitly licenses this encoding, with its
  comparison to the recorded `Etale.cohomology` functor a stage-3 bridge.
- `Sheaf.H (...rootsOfUnitySheaf (ell ^ n)) 1` is H¹(C,A_n(1)) on the etale site. The twist
  dependency's module is publicly imported. Its finite coefficient is the root line; the
  source and the Kummer-Jacobian node explicitly read its etale realization as mu_(ell^n).
  No chosen trivialization identifies the two factors.
- The value is literally `ZMod (ell ^ n)`, and pointwise equality forces the map b to be
  `Scheme.finiteCoefficientCup ... 1 1 2 rfl`, followed by the existing
  `Scheme.degreeNormalizedCurveTrace`. Existence of b packages this fixed function as a
  biadditive map; it is not an arbitrary-map hypothesis.
- `b : H¹(C,A_n) →+ H¹(C,mu_(ell^n)) →+ ZMod (ell ^ n)` gives biadditivity. This is
  A_n-bilinearity, because for any residue a, its scalar action is natural multiplication
  by a representative. Additive maps commute with that multiplication. The groups are
  killed by ell^n by their coefficient structures (and this also follows from the two
  displayed bijections into Hom groups killed by ell^n). Thus there is no scalar-structure
  choice and no claim restricted to prime-field coefficients.
- `Function.Bijective b` and `Function.Bijective b.flip` say that both adjoints to the full
  A_n-duals are isomorphisms. Every additive homomorphism between Z/N-modules is uniquely
  Z/N-linear, so these are precisely the two bijectivity clauses of Mathlib's
  `LinearMap.IsPerfPair`, without introducing duplicate module instances on `Sheaf.H`.

Dependency declarations read and used:

- `Sheaf.Paper.IntrinsicCoefficientTwists` publicly imports
  `Sheaf.Paper.CoefficientTwistsDetailed`: `finiteCoefficientTwist`, `coefficientTwistLine`,
  and the completed-root-line constructions give the specified coefficient convention.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology A X i = rightDerivedGlobalSections A X ⋙
  DerivedCategory.homologyFunctor A i`; the node record describes `Sheaf.H` as its ordinary
  abelian-sheaf Ext realization.
- `Sheaf.AlgebraicGeometry.Curve.FiniteCoefficientCup`:
  `AlgebraicGeometry.Scheme.finiteCoefficientCup` is the signed Yoneda construction with
  coefficient evaluation. I read its full definition, the comparison bijection, and the
  actual module-valued roots sheaf, including the unsigned Cech sign convention.
- `Sheaf.AlgebraicGeometry.Curve.DegreeNormalizedTrace`:
  `AlgebraicGeometry.Scheme.degreeNormalizedCurveTrace` is fixed by the uniqueness theorem
  taking the Kummer class of every closed point to 1. I read its signature, construction
  and existence/uniqueness proof docstring. Both new dependencies already have usable Lean.
- `WeilConjectures.AlgebraicGeometry.BaseChangeField`: `Scheme.baseChangeField` is the
  pullback and its structure map is `pullback.snd`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsProjective` and its inherited
  `IsHProjective.isProper` give the actual projectivity hypothesis and properness.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `topologicalKrullDim_eq_of_smoothOfRelativeDimension` gives dimension one on the connected
  geometric pullback. Mathlib `GeometricallyConnected.connectedSpace_of_subsingleton` gives
  its connectedness.

The recorded proof-dependency modules are imported without `public`: abelian etale/pro-etale
comparison, curve cohomological dimension, the bounded-free splitting lemma, abelian-variety
final theorem and proper curve cohomology. The other proof dependencies have no recorded
module yet, so there is no module to import for them. The complete five-step argument is in
the theorem docstring. A node proof limitation is preserved visibly: its third step only
specializes the finite-field conventions, while its statement and downstream H1 dual Tate
module cover arbitrary k₀. The statement is true over arbitrary k₀ by ordinary geometric
Poincare duality. I did not silently restrict it to finite fields or change the DAG proof.

Edge cases checked: genus zero gives two zero groups and their bijective zero adjoints;
ell=2 is allowed, and n>1 uses Z/(ell^n), not a field or a domain; n=1 is included; n=0 is
outside the positive-level convention of the cited twist definition. Characteristic zero
has c=0 and is allowed. The empty scheme and dimension-zero schemes are excluded by the
connected dimension-one curve hypotheses as in the paper. Field and scheme universes are
arbitrary u; coefficient sheaves use the common u+1 lift. No equality between site object
and morphism universes is imposed.

Searches actually run:

- msearch leanfinder: `perfect cup trace pairing degree one etale cohomology smooth
  projective curve ZMod prime power`: eight unrelated field trace, class group and
  elliptic-curve hits; no theorem about this pairing.
- msearch loogle: `LinearMap.IsPerfPair, ZMod`: zero hits.
- msearch grep: `IsPerfPair|poincarePairing|cupTrace` in Mathlib/AlgebraicGeometry: zero hits.
- rg over upstream WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json for
  the proposed declaration names: no conflicts. Upstream grep for the node id found only
  comments in FundamentalGroup/Frobenius.lean, not a declaration of finite-level duality.
- Source rg for degreewise Poincare pairings found the general TateOrientation framework;
  I read Degreewise.lean and TraceCup.lean. Its degreewise duality is explicitly restricted
  to finite domains and gives only a noncanonical isomorphism, not the present prime-power
  canonical perfect pairing. Consequently it cannot be recorded as an existing match.
- Project/DAG searches for cup and trace found the two exact existing construction nodes
  above. Their modules are reused, with no new definition node and no dependency repair.

No statement correction and no STATEMENT-DISPUTED flag: all original hypotheses and the
canonical pairing conclusion are retained. Validation results are recorded below.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
