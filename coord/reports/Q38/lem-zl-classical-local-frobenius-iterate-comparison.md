## Worker report

Q38 states `lem-zl-classical-local-frobenius-iterate-comparison` in
`Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison`. Its theorem is
`WeilConjectures.ClassicalLocalFrobenius.classical_local_frobenius_iterate_comparison`.
The proof is `sorry`; the docstring gives all nine steps of the node's proof.
There is no statement correction and no disputed mathematical statement.

Hypotheses and clauses, read against the node:

- The finite field, prime power, chosen algebraic closure, and geometric fibre are
  the existing `D : FiniteFieldDatum.{u}` and `D.geometricFiber Y₀`.
  `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give exactly the coefficient-prime
  assumptions. `Ω : Type (u+1)` has `Field`, `Algebra ℚ_[l]`, and
  `IsAlgClosure ℚ_[l]`. This is the carrier-size convention of the published
  classical algebraic-coefficient category, not an equality of site universes.
- `Y₀ : Over (Spec (.of D.k₀))`, `LocallyOfFiniteType Y₀.hom`,
  `QuasiCompact Y₀.hom`, and `IsSeparated Y₀.hom` express separated finite type.
  No smoothness, nonemptiness, or positive-rank hypothesis occurs.
- `S : ZlClassicalRealization ...` is the recorded normalized realization, with
  its actual pullback/unit pinning. The theorem supplies the stalk-unit Fact
  from `stalkPrimeUnits`; it does not assume another invertibility condition.
  `S.weil.obj M` is precisely its realized Weil object, not an independently
  selected sf object or an arbitrary identification of its Weil structure.
- `ComparisonAssertions` quantifies a unique family of natural isomorphisms
  `S.functor ⋙ LocalFrobeniusLarge.stalk ... x ≅ fibre l Ω x`.
  `fibre` has the literal published `lisseAlgebraicFiber` object function.
  `CompletedNormalization` fixes this family using the SAME finite-stage
  isomorphism extracted from `S.pullback_pinning`, its inverse on sf fibres,
  normalized ordinary sections, and completed reduction germs. For every j,
  `RepresentsCompletedGerm` compares the j-th projection of the actual inverse
  limit with the canonical etale/pro-etale germ map. The pure tensor formula
  sends `a tensor germ(b tensor v)` to `a tensor (b tensor w)`.
  No arbitrary isomorphism or stalk/limit interchange replaces this map.
- Positive integer n in the node is represented by index `n : ℕ` with exponent
  n+1, exactly as `localPositivePower`. The return hypothesis is the actual
  equality `x ≫ gY^[n+1] = gs^[n+1] ≫ x`. The statement covers every geometric
  lift with this return, hence every specified extension-field point; it never
  replaces this equality by a fixed-point equation over k.
- `FactorSquares` contains three separate equations. Its first identifies every
  `LocalFrobeniusLarge.transportIterate` with `classicalTransport`; its middle
  equation compares the two actual pullback factorizations through
  `returnComparison` and `classicalReturn`; its last compares
  `LocalFrobeniusLarge.weilIterate` with `classicalWeilIterate`. Intermediate
  comparisons are constructed from c, point-pullback composition, and the pinned
  `realizationIterate`, not independently existential vector-space maps.
- The third conjunct of `ComparisonAssertions` is the requested operator
  conjugacy, in Lean's left-to-right composition order:
  `sfOperator ≫ c.hom = c.hom ≫ classicalOperator`. Both operators are the
  transport, middle-comparison, and Weil-map composite on their actual fibres.
  Classical transport uses `FiniteEtale.fiberReparamIso` and
  `etaleAlgebraicPathIso`; the pullback fibre maps use finite etale germs,
  inverse limits, rationalization, and algebraic scalar extension.
- The next conjunct quantifies EVERY Weil morphism `f : M ⟶ N`, using its
  actual `f.hom.f`. No inverse of f or monomorphism condition is assumed.
  c is moreover natural in all underlying classical sheaf morphisms.
- The coefficient conjunct quantifies every arrow of `LisseCoefficientPairs`
  and its actual `lisseCoefficientCocartesian.Q.map`. Thus it includes finite
  coefficient extension, identity extension, towers, and arbitrary finite-stage
  lifts in the existing cocartesian/common-stage Hom prescription.
  The sf point functor's representative formula uses `stageScalar`, fixed by
  the tensor-flattening formula on every representative and coefficient tower.
- Constant extension by m+1 uses `gY^[m+1]`, `gs^[m+1]`, and exactly the old
  iterated Weil structure. `transport_blocks`, `sfWeil_blocks`, and
  `classicalWeil_blocks` identify the new n+1 iterates with the old product
  (m+1)(n+1). `constantExtension_operators` compares both entire operators,
  and the final conjunct gives their intertwining at every product-period
  semilinear return. Equality transports only compare the two presentations of
  these powers; they are not arbitrary comparison maps.
- All Weil recursions take rational isomorphisms. No integral lattice stable
  under theta or theta inverse is selected or assumed. Scheme automorphisms
  are semilinear; none is required to be k-linear. Rank zero is unrestricted.

Dependency declarations used (their full signatures and docstrings were read):

- `Sheaf.Paper.LisseIntegralSmallCoefficients`, together with its public classical
  lisse interfaces: `LisseIntegralSheafOfUniverses`, `lisseIntegralFiber`,
  `lisseAlgebraicFiber`, `lisseAlgebraicFiberFunctor`,
  `lisseAlgebraicFiber_ofModel`, and `lisseCoefficientCocartesian`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeart` and the common-stage heart
  used by the recorded normalized realization and Weil-heart categories.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `inclusion`, `stageSystem`,
  `commonStageDerivedPullback`, and its exact object prescription.
- `Sheaf.Paper.LisseRationalRealization`: `LisseRealization.lisse_rational_realization`;
  its data and normalization interfaces are used through
  `LisseRationalRealizationData`, `LissePointNormalization`, and their public imports:
  `At`, `Along`, `PointAt`, `PointNormalized`, `PullNormalized`, `sections`,
  `fibre`, and the normalized ordinary section comparisons.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`.
  `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `geometricFrobenius`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and the imported finite
  coefficient conventions: coefficient integer rings, their reductions, finite
  coefficient fields, and small `Coefficient`/`coefficientInclusion`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfWeilPrimeInvertible`, and the actual fixed-pair Weil category.
- `Sheaf.Paper.NormalizedClassicalWeilRealization`: `ZlClassicalRealization`,
  `ZlClassicalPullbackModels`, `zlClassicalModel`, `zlCompletedBase`,
  `zlRealizationBase`, `ZlClassicalWeil`, and `ZlClassicalRealization.weil`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower`,
  `localPullbackComposition`, `localPointTransport`, and the existing finite
  local operators. The large-coefficient interface repair below preserves them.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso`,
  `frobeniusPointPrimeInvertible`, and its coefficient-size conventions.
- `Sheaf.Paper.LisseAdicAutomorphismPullback`:
  `lisseAlgebraicAutomorphismPullback`, `lisseAlgebraicAutomorphismFiberIso`.
  `WeilConjectures.AlgebraicGeometry.Etale.Lisse.PathTransport`:
  `etaleAlgebraicPathIso`; `FiniteEtale.fiberReparamIso` supplies the actual path.
- `Sheaf.Paper.LisseCompletedSystemData`: `CompletedLisse.System`,
  `RawRational`, `etaleDiagram`, `proEtaleDiagram`, completion and rationalization.
  `Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk`:
  `Scheme.proEtale_comparison_stalk` with its canonical germ prescription.
- Proof dependency `Sheaf.TraceFormula.PointTransportComposition` is imported.
  The two nodes for scalar-comparison coherence and point-transport realization
  have no recorded Lean module yet; no fabricated import is added for them.

Edge cases checked before and after writing: empty Y gives vacuous point clauses;
rank-zero and zero morphisms satisfy all tensor/projection formulas; n=0 denotes
period one, never a forbidden zero iterate; m=0 denotes unchanged constant field.
The product index `(m+1)*(n+1)-1` has no truncation loss since both factors are
positive. Identity and tower coefficient extensions retain their specified
comparisons. The rational rank-one Weil map multiplication by l is allowed even
when theta inverse preserves no chosen integral lattice. The return equality keeps
the nontrivial Frobenius on Spec k, rather than assuming k-linearity.

Searches (performed before introducing the declarations):

- msearch LeanFinder, “Normalized realization of a classical lisse Weil sheaf
  intertwines local Frobenius operators and iterated point transports”: eight
  irrelevant normalization/Witt-isocrystal results; no exact statement.
- msearch Loogle, “lisseAlgebraicAutomorphismFiberIso, localFrobeniusOperator,
  ZlClassicalRealization”: no Mathlib match (project identifier is not in Loogle).
- msearch Mathlib grep, `localFrobenius|lisse.*Frobenius|Classical.*Weil`: zero hits.
- rg in the prescribed upstream `WeilConjectures` and project `Sheaf` sources
  located the classical path/fibre, normalized realization, local finite
  Frobenius, and common-stage interfaces listed above, but no theorem or canonical
  comparison data giving this statement. The item-id search in upstream gave no
  duplicate theorem.
- New-node LeanSearch, “Normalized completed inverse limit fibre comparison with
  ordinary sections for lisse adic realization”: eight results about ordinary
  limits or algebraic adic completion, none about the required lisse comparison.
- New-node LeanFinder, “Canonical compositors for classical lisse adic automorphism
  pullback and block iteration of local Frobenius”: eight ring-Frobenius results,
  no classical lisse compositor or completed normalization.
- New-node Mathlib grep,
  `CompletedNormalization|RepresentsCompletedGerm|classicalComposition_existsUnique`:
  zero hits. Searches in DAG nodes and both source trees found no duplicate notion;
  blueprint_refs search “classical local Frobenius” returned no nodes.
  Exact returned search text is retained in each new node's `mathlib_searches`.

Source grounding: Bhatt--Scholze, Proposition 6.8.4(1),(4), Proposition 6.8.14(2),
Remark 6.8.15 (PDF pp.58–63), and the current blueprint's
real-mixed-by-curves proof paragraph 1 and this node's nine-step refinement.

## New nodes

`def-zl-classical-local-frobenius-data` owns
`Sheaf.Paper.ClassicalLocalFrobeniusData`: canonical classical compositor with its
finite-germ fibre characterization, rational Weil iteration, actual classical
local factors, pinned realization iteration, the two fixed intermediate fibre
comparisons, the three factor squares, and block-iteration definitions. The
existing automorphism-pullback node supplies the one-step pullback and fibre
comparison but not these compositors and all-period local factor data. Sources
are BS 6.8.4 and 6.8.15 and the node's blueprint proof. The searches above exclude
an existing exact definition. All canonical choices are from uniquely
characterized maps; every postponed helper theorem has its own source/proof
docstring and is listed in the owning node's `lean.declarations`.

`def-zl-completed-local-fibre-comparison-data` owns
`Sheaf.Paper.CompletedLocalFibreComparisonData`: the SAME pinned finite model,
ordinary germ map, actual finite etale/pro-etale comparison, inverse-limit germ
criterion, rationalized completed section, canonical carrier-lift tensor map,
literal finite-stage endpoint transports, and `CompletedNormalization`. The
existing completion and realization data do not define this combined normalized
fibre comparison. Its source is BS 6.8.4(1),(4), 6.8.14(2), 6.8.15. The recorded
searches give no exact prior notion. Finite reductions are retained individually;
no arbitrary pro-etale stalk/limit interchange or arbitrary vector-space
isomorphism is used.

## Dependency modules

`def-weil-local-frobenius-trace` receives a lean-only §1(B) repair in
`Sheaf.Paper.LocalFrobeniusLargeCoefficients`. The existing algebraically closed
operator has Ω and the scheme in the same carrier universe, whereas the
published classical lisse algebraic coefficients have Ω in Type (u+1). This
module retains the original module and declarations and supplies its same local
operator construction for that required size. The point functor is specified on
EVERY finite-stage representative by the canonical cohomology/scalar comparisons
and tensor flattening. Pullback composition comes from the actual finite-stage
`localPullbackComposition`; point transport comes from `localPointTransport`;
Weil iteration is explicit recursion, and return is the actual semilinear
factorization. No equality of site/coefficient universes is imposed.

## Second reading by Q38

The dispatcher explicitly forbids starting another agent, so this is a separate
second pass by Q38, not a claim of an independent worker review. I reread the node,
source proof, and all four modules together. The pass caught the need to retain
completed finite-level germs rather than an unspecified fibre isomorphism, and
the need to fix BOTH intermediate comparisons from c and the pinned realization.
Those are now explicit in CompletedNormalization and FactorSquares. It also
caught universe unfolding at finite inclusion/pullback boundaries: canonical
object-equality transports and named point-section comparisons replace implicit
identifications. The constant-field operator now uses its literal new scheme
powers, not a definition by the desired old operator. Rank zero, semilinearity,
rational-only Weil maps, arbitrary morphisms, and identity/tower scalar arrows
remain covered. No mathematical statement was weakened to resolve elaboration.

### Clause-by-clause second reading (maintainer reviewer, delivery 97c7d55e)

The pass above was a self-review by the writing group. This reading was done
independently against the node, BS 6.8.4(1),(4), 6.8.15, the four delivered modules
and the recorded dependency declarations.

- q = p^a, k_0 = F_q, k = closure: `D : FiniteFieldDatum.{u}`, `D.geometricFiber Y₀`. OK.
- l prime, l ≠ p: `[Fact l.Prime]`, `hl : l ≠ D.p`. OK.
- Ω algebraic closure of Q_l: `Ω : Type (u+1)`, `IsAlgClosure ℚ_[l] Ω`; the size is the
  one fixed by the cited `ZlClassicalRealization` (def-zl-normalized), not an extra
  restriction. OK.
- Y_0 separated finite type: `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on
  `Y₀.hom`; no smoothness, nonemptiness or rank hypothesis. OK.
- (M, θ) classical lisse Ω-Weil sheaf for the classical pullback: `M : ZlClassicalWeil`
  = `EtaleLisseWeilSheaf l Ω (D.geometricFrobenius Y₀)`, rational θ. OK.
- (K, ϑ) normalized realization with pinned pullback/unit: `S : ZlClassicalRealization`
  and `(S.weil.obj M).obj`, i.e. `IsoAlgebra.mapOfNatIso S.pullback`; ϑ = R(θ)∘d_1 by
  definition. The stalk-unit Fact is discharged by `stalkPrimeUnits`, so no assumption
  is added. OK.
- c_x̄ by the completed inverse-limit comparison: `∃! c`, pinned by
  `CompletedNormalization` (the pinned stage iso `pinnedStage` = the witness of
  `S.pullback_pinning`, normalized point/pullback sections, the germ criterion
  `RepresentsCompletedGerm` through the unit-germ-normalized
  `proEtale_comparison_stalk` comparison, and the formula a⊗germ(b·v) ↦ a⊗(b⊗w)).
  The family is natural on `LisseAlgebraicSheaf`; uniqueness is plausible since these
  germs generate every model fibre and every object is a finite free model up to iso. OK.
- c F^(n)_K = F^(n)_M c for every n ≥ 1 and x ∈ Y_0(F_{q^n}): third conjunct,
  `operator … n h ≫ c.hom = c.hom ≫ classicalOperator … n h`, n ↦ exponent n+1, for
  every geometric lift with `x ≫ gY^(n+1) = gs^(n+1) ≫ x` (so every return point;
  no k-linearity). Lean order `f ≫ g` reverses the TeX order correctly. OK.
- the three factor squares (transport iterates, pullback-composition at
  g_Y^n x̄ = x̄ g_s^n, θ^[n]/ϑ^[n]): `FactorSquares`, with the intermediate comparisons
  built from c, `LocalFrobeniusLarge.composition` and `realizationIterate`. The
  classical transport is `etaleAlgebraicPathIso` along `fiberReparamIso(gs^(n+1)).symm`,
  i.e. z ↦ gs^(n+1) ≫ z, the same direction as the sf restriction/coprojection transport
  (and as `ZlClassicalFibreComparison.local_operator` of the parent). The recursions of
  `classicalWeilIterate` and `LocalFrobeniusLarge.weilIterate` are θ^[r+1] =
  θ^[r]∘H^r(θ)∘compositor, matching def-weil-local-frobenius-trace. OK.
- natural on Weil morphisms (no invertibility): fourth conjunct over all `f : M ⟶ N`. OK.
- compatible with coefficient extension: fifth conjunct over every arrow of
  `LisseCoefficientPairs` (identity, towers, arbitrary representatives), and
  `CompletedNormalization` holds at every finite E. OK.
- constant extension m: `blockOperator` / `classicalBlockOperator` use gY^(m+1),
  gs^(m+1) and θ^[m+1], ϑ^[m+1] on the same Y; the identification with the old
  (m+1)(n+1)-fold maps is `constantExtension_operators` (with `transport_blocks`,
  `sfWeil_blocks`, `classicalWeil_blocks`), and the sixth conjunct is the intertwining
  at every product-period return. OK.
- no integrality, no k-linearity, rank zero: nothing in the Lean assumes them. OK.

Edge cases: empty Y_0 (point clauses vacuous); rank 0 (zero fibres); n = 0 / m = 0 are
periods 1 and unchanged base field; (m+1)(n+1)-1 has no truncation.

Dependency module: the recorded Qbar operator of def-weil-local-frobenius-trace has
Ω : Type u, while ZlClassicalRealization fixes Ω : Type (u+1); the §1(B) module
`LocalFrobeniusLargeCoefficients` keeps the finite-stage construction (point
transport, `localPullbackComposition`, Weil recursion, return) and extends H⁰ to Ω with
tensor-normalized scalar comparisons. The old module stays a public import.

Reviewer repairs: the unused plain imports `Sheaf.Paper.LisseRationalRealization` and
`Sheaf.TraceFormula.PointTransportComposition` were removed from
`ClassicalLocalFrobeniusData` (the item module keeps them as proof imports), and that
module's title was corrected; clean compile. def-zl-completed-local-fibre-comparison-data
now cites def-per-continuous-rational-realization-data, the owner of
`ContinuousRational.moduleUnit` used by `sectionGerm`.
