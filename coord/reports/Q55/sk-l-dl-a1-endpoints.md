## Worker report

Item: `sk-l-dl-a1-endpoints`, group Q55, 2026-10-18.

Existing declaration match; no Lean module is added. The four declarations in the current
published module `WeilConjectures.WeilSheaf.CurveEndpoints` state all the clauses of this
node. I read the complete current source with `scompile.py --source`, including its shared
variable declarations, local finite-type instance, and all four theorem docstrings and types.
The older local source has these same declarations in
`WeilConjectures.DeligneLaumon.AffineLine.Endpoints`; the live source-reader, rather than that
older path, determines the delivered module name. The DAG already identifies this item
with `lem-a1-middle-extension-endpoints` in `blueprint.same_as`; that node's existing record
lists the same four theorem names. The item's statement, dependencies and proof are unchanged.

Source checked: main-20261015, sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/_section.md,
including its four named Lean declarations and entire mathematical statement. The source
of the item is the unit itself. There is no mathematical correction or disputed statement.
This attachment records statements, not a claim that their proofs are complete. The current
first three endpoint declarations have sorry proofs. No existing proof is edited or copied.

### Hypotheses, objects and clauses

- The finite field is `{k₀ : Type u} [Field k₀] [Finite k₀]`, with arbitrary explicit universe
  `u`. This permits every finite field, not only prime fields. The coefficient prime is
  `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`. The chosen standard coefficient closure
  is `PadicAlgCl l`; the geometric fibre uses `AlgebraicClosure k₀`. These are the fixed
  algebraic closures underlying the existing upstream Weil-sheaf realization.
- `C₀` is `{C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]` with
  `[SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]` and
  `[GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]`. Smooth relative dimension one
  over a field is the smooth pure one-dimensional curve condition, with no properness or
  extra characteristic hypothesis. Smoothness gives locally finite type; the local instance
  in the existing source derives exactly this fact. An affine scheme over the field is
  quasi-compact and its structure map is separated, so the cohomology expressions have
  their required separated finite-type hypotheses.
- `U₀` is `{U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]`; `j : U ⟶ C` carries
  `[IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]`. The last
  instance is density of the image. All maps are over the same finite field.
- The existing signatures also carry `[QuasiCompact j]`; the degree-two equivalence
  explicitly carries quasi-compactness and local finite type of `U` over the field. These
  are consequences, not restrictions: `C` is finite type over a field and Noetherian,
  every open subset of its Noetherian space is quasi-compact, and open immersions are
  locally finite type. Thus every `j` and `U₀` in the node is covered. No affineness of
  `U₀` is assumed in the signatures.
- The lisse Weil sheaf is `(F : WeilSheaf k₀ l U)` and `(hF : F.IsLisse)`. Its underlying
  object is a constructible adic sheaf on the geometric fibre with geometric-Frobenius
  descent. There is no requirement of a Frobenius-stable integral lattice.
- `j_*F` is exactly `(WeilSheaf.directImage j).obj F`. I read
  `WeilConjectures.WeilSheaf.OpenImmersion`: `directImage` is the ordinary sheaf
  `lowerStar`, not `higherDirectImage`, `derivedLowerStar` or an intermediate extension
  of an unshifted perverse object. The cohomology construction places this sheaf in
  degree zero before applying compact-support direct image.
- Geometric cohomology is `G.compactlySupportedCohomology r`. I read the definition in
  `WeilConjectures.WeilSheaf.Cohomology`: it is cohomology of `Ra_!` after geometric base
  change, evaluated by global sections on `Spec (AlgebraicClosure k₀)`, retaining its
  induced geometric Frobenius. It does not take arithmetic Galois invariants.
- `H_c^0(C,j_*F)=0` is
  `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`, whose
  conclusion is `Subsingleton (((WeilSheaf.directImage j).obj F).
  compactlySupportedCohomology 0).carrier`. Subsingleton of the vector space says exactly
  that its only vector is zero.
- The statement of vanishing outside `{0,1,2}` is
  `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`, for
  `{r : ℤ}` and `(hr : r < 0 ∨ 2 < r)`, with the same subsingleton conclusion at degree
  `r`. Integral indexing includes all negative degrees, not just degrees above two.
- The degree-two clause is
  `AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two`:
  `Nonempty ((((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).Equiv
    ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1)))`.
  `FrobeniusModule.Equiv` is a linear equivalence with the intertwining equation
  `e (M.frobenius x) = N.frobenius (e x)`, so Frobenius equivariance is included.
  Nonempty is appropriate here because the node asserts an isomorphism, not a chosen
  isomorphism or a formula for its map.
- I read `WeilSheaf.geometricCoinvariants` in `WeilConjectures.WeilSheaf.Dual`. It is
  `FrobeniusModule.dual (globalSections (F.dual hF))`, retaining the dual Frobenius.
  On the connected geometric open its meaning is exactly the specified quotient:
  `Γ(U,F^∨)=(V^∨)^{π₁(U)}=(V_{π₁(U)})^∨`, and finite-dimensional double duality gives
  `V_{π₁(U)}`. This is the invariant/annihilator calculation already spelled out in
  step 9 of the item's proof, not coinvariants of the full arithmetic group.
  The geometric fibre representation in the node enters through this identification;
  the endpoint theorem does not take an independently chosen representation as input.
- `tateTwist (Nat.card k₀) (-1)` is the required Tate twist. The definition in
  `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule` rescales Frobenius by `q^(-n)`;
  at `n=-1` its eigenvalues are multiplied by `q`. Thus this is the node's geometric
  convention, with weight raised by two.
- The conditional weight clause is
  `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`:
  `(ι : PadicAlgCl l →+* ℂ)`, `{w : ℝ}`, and `(hw : F.IsPunctuallyPureOfWeight ι w)` imply
  `(((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).
    IsPureOfWeightOver k₀ ι (w + 2)`.
  Punctual purity tests local eigenvalues using the residue cardinality; the output
  tests the global geometric Frobenius using `Nat.card k₀`. The zero module is allowed:
  purity quantifies over eigenvalues and does not assert a nonzero eigenvector exists.
  Purity is required only in this fourth clause, not in any of the other three.

### Recorded dependencies and their declarations

I read every statement-dependency node and its current Lean record, and the source signatures
and docstrings. No private replacement notion is introduced.

1. `sk-d-dl-a1-setup`: `WeilConjectures.DeligneLaumon.AffineLine.Defs`,
   `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant` and
   `AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity`. Neither of these two extra
   predicates is a hypothesis of this endpoint lemma. The relevant inherited conventions
   are finite field, geometric Frobenius, ordinary direct image and the `(-1)` weight shift.
2. `def-wf-middle-extension`: `Sheaf.Paper.CommonStageCurveWeilMiddleExtension`,
   `WeilConjectures.qbarCurveWeilOrdinaryPushforward`. Its public import chain retains
   `Sheaf.Paper.CurveWeilMiddleExtension` and
   `AlgebraicGeometry.WeilSheaf.curveWeilMiddleExtension`, whose data are literally the
   existing ordinary `WeilSheaf.directImage`. The matched upstream theorem uses this
   retained ordinary Weil-sheaf realization. It is not a second definition of `j_*`.
3. `def-wf-fundamental-representation`: `Sheaf.Paper.EtaleWeilFundamentalRepresentation`,
   `AlgebraicGeometry.Scheme.etaleFundamentalRep`, with its finite-cover path normalization,
   geometric restriction, and degree-one operator. This module also publicly imports the
   existing upstream fundamental-representation module. The matched endpoint statement
   expresses geometric coinvariants intrinsically as the dual of sections of the dual;
   its equivalence to the geometric-representation quotient is the finite-dimensional
   calculation above. It does not replace the geometric subgroup by the full Weil group.
4. `def-real-weil-representation-operations`:
   `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra`,
   `AlgebraicGeometry.WeilGroup.detLine` and `semisimplification`. Their docstrings point
   to Mathlib `Representation.dual`, `.invariants` and `.Coinvariants` for the ordinary
   operations used in the statement. Determinants and semisimplification themselves
   are not hypotheses or conclusions of this lemma.
5. `def-weil-ordinary-compact-cohomology`:
   `Sheaf.Paper.CommonStageCompactWeilCohomology`,
   `WeilConjectures.commonStageCompactWeilCohomology` and `adicCompactCohomology`.
   Its public import chain retains `Sheaf.Paper.OrdinaryCompactWeilCohomology` and
   `AlgebraicGeometry.WeilSheaf.ordinaryCompactWeilSheafCohomology`; the second component
   of the latter is literally `F.compactlySupportedCohomology r`, which occurs in all
   four existing endpoint statements. I read both this adapter and the underlying
   upstream `Cohomology` definition.

This delivery attaches the existing sheaf-level endpoint theorem. It neither identifies
categories of fixed pairs with derived categories of Weil sheaves nor adds a comparison
between them. The recorded dependencies retain their newer interfaces and their publicly
exported upstream sheaf interfaces. No imports or helper modules are needed in a delivery
that writes no Lean module.

### Edge cases checked

- `j = id` is included: for a smooth affine curve it gives `H_c^0(C,F)=0` and the usual
  top-degree coinvariant description.
- Constant sheaf on the affine line gives `H_c^2=Qbar_l(-1)` with Frobenius `q` and
  weight `2` for the constant weight-zero sheaf, verifying the Tate sign.
- A nontrivial Kummer character on the multiplicative group has zero geometric
  coinvariants, consistent with zero top cohomology of its middle extension.
- Zero sheaf and zero coinvariant quotient are allowed, including the conditional
  purity clause. There is no nonzero-sheaf, positive-rank or nonzero-eigenvalue hypothesis.
- Negative degree `r=-1` and the first degree beyond the range `r=3` are included in
  the range statement. Degree one is not inadvertently declared zero.
- A geometrically connected smooth relative-dimension-one scheme is nonempty; an
  empty open cannot be dominant in it. No nonempty case is excluded by extra data.
- A proper positive-dimensional connected curve cannot also be affine. The support
  argument therefore does not silently impose an additional nonproperness assumption.
- Arbitrary finite fields, all primes different from their characteristic, and arbitrary
  real weights are covered. No genus, tameness or unramified-at-infinity assumption occurs.

### Searches

- `msearch.py`, LeanFinder: "Compactly supported cohomology of ordinary middle extension
  of lisse sheaf on smooth affine curve vanishes in degree zero and above two and degree
  two is geometric coinvariants Tate twist". Eight hits concerned abstract group cohomology,
  Hilbert 90 and standard resolutions; none stated curve endpoints.
- `msearch.py`, Loogle: `compactlySupportedCohomology, Representation.coinvariants`.
  Zero hits, unknown identifier `compactlySupportedCohomology` in the Mathlib service.
- `msearch.py`, grep: `compactlySupportedCohomology.*directImage|coinvariants.*tateTwist`.
  Zero Mathlib hits. Direct `rg` for `geometricCoinvariants|compactlySupportedCohomology`
  under Mathlib/AlgebraicGeometry likewise gave no match.
- `rg` for the endpoint declaration names and the item ID in upstream and `lean/Sheaf`,
  and the prescribed `grep -rn` for the item ID upstream, located all four statements
  in the older local `DeligneLaumon/AffineLine/Endpoints.lean`; the Sheaf hits were
  proof-support docstrings, not another endpoint theorem.
- `rg` on `dag/lean_names_upstream.json` found the same endpoint declaration names.
  The item's own audit names `WeilConjectures.WeilSheaf.CurveEndpoints`. The required
  `scompile.py --source WeilConjectures.WeilSheaf.CurveEndpoints` returned that current
  module, including all four statements. I also read current `Defs`, `Category`,
  `OpenImmersion`, `Cohomology`, `Dual`, `GeometricCoinvariants`, and the recorded setup
  and representation-operations modules through the source wrapper where local files
  were absent. This confirms the match by full types and definitions, not names alone.

### Validation

The delivery wrapper checks all four fully qualified declarations by importing the current
published module and compiling its existing-declaration probe through `scompile.py`.
There is no delivered Lean file to compile separately. The node copy changes only `lean`;
its four-declaration record avoids recording only the range clause of the unit.

## Second reading by Q55

No second reading by a worker: under the direct-delivery instruction the worker delivers
without spawning agents, and the maintainer's independent review is the only review.
