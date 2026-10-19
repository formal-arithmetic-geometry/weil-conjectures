## Worker report

The module `Sheaf.Paper.GeometricFiberFiniteExtension` defines the canonical chosen
Cartesian square of the geometric fibre and states
`AlgebraicGeometry.Scheme.geometricFiber_finiteExtension_properBaseChange`.
The square has `P = Spec (.of Ω)`, `X_ybar = pullback f ybar`, projections
`pullback.fst f ybar` and `pullback.snd f ybar`, the commutativity equation
`pullback.condition`, and the identity isomorphism to the chosen pullback.

The theorem's hypotheses render the node statement as follows.

* A prime `l` and finite extension `E / ℚ_[l]` are rendered by
  `[Fact l.Prime]`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]`.
* The proper morphism is `f : X ⟶ Y` with `[IsProper f]`.
* The geometric point is `ybar : Spec (.of Ω) ⟶ Y` with
  `[Field Ω] [IsAlgClosed Ω]`.
* The geometric fibre and its projections are the canonical pullback
  `pullback f ybar`, `pullback.fst f ybar`, and `pullback.snd f ybar`; the latter has
  `[IsProper (pullback.snd f ybar)]`, which is the node's properness of `a_ybar`.
* Noetherian hypotheses are the four instances on `X`, `Y`, `pullback f ybar`, and
  `Spec (.of Ω)`. Finite-dimensional hypotheses are the four explicit bounds
  `_dimX`, `_dimY`, `_dimFiber`, and `_dimPoint` using `topologicalKrullDim`.
* Invertibility of `l` on all four schemes is rendered by `_hlX`, `_hlY`, `_hlFiber`,
  and `_hlPoint` as `IsUnit (l : Γ(T, ⊤))`.
* The geometric-fibre bound is `_hFibres`, quantified over every algebraically closed
  field `Ω' : Type u` and geometric point `y : Spec (.of Ω') ⟶ Y`, with bound `e`.
* The conclusion existentially supplies the four constructibility restrictions for
  direct images and completed pullbacks. For every raw rational object `K` in
  `PbcRationalCategory X (pbcPadicCoefficientDatum l E)
  (Padic.coefficientExtensionUniformizer l E)`—the raw localization denoted `Dbc(X,E)`—
  it asserts `IsIso` for the specified component
  `finiteExtensionRationalExchangeComponent l E (geometricFiberSquare f ybar) K`.
  Its two endpoints are respectively the completed pullback of `ybar` after `f_*`
  and the direct image along `pullback.snd f ybar` after pullback along
  `pullback.fst f ybar`, matching `L ybar^* R f_* K` and
  `R a_ybar,* L i_ybar^* K` in `Dbc(Spec Ω,E)`.

The theorem uses the recorded declaration
`AlgebraicGeometry.Scheme.finiteExtension_properBaseChange` from
`Sheaf.Paper.FiniteExtensionProperBaseChange`, and the recorded definitions
`AlgebraicGeometry.IsProper` (Mathlib),
`IsAlgClosed` and `CategoryTheory.Limits.pullback` (Mathlib),
`AlgebraicGeometry.Scheme.dim` (Sheaf.AlgebraicGeometry.Dimension),
`AlgebraicGeometry.ChosenCartesianSquare` (Sheaf.AlgebraicGeometry.ChosenCartesianSquare),
and `AlgebraicGeometry.Scheme.PbcRationalDerivedCategory` /
`PbcRationalCategory` (Sheaf.Paper.PbcRationalCategory). The parent theorem also
provides the rational exchange component and its endpoint constructions.

Edge cases checked: `K = 0`; an empty geometric fibre; `f = 𝟙 _`; `e = 0`; an
unramified or ramified finite extension; `E = ℚ_[l]`; and the excluded case where
`l` is not invertible on one of the four schemes (the explicit `IsUnit` hypotheses
correctly reject it). The pullback construction works uniformly for every
algebraically closed `Ω` and does not assume the fibre is nonempty.

Searches made: `msearch.py leanfinder` for a proper-base-change geometric-fibre
isomorphism (only unrelated Mathlib categorical and stalk hits); `msearch.py
leansearch` for proper base change of rational l-adic constructible complexes (only
ordinary scheme stability results); `msearch.py loogle` for `baseChange` and
`CategoryTheory.IsIso` (only generic categorical base-change results); `rg` over
`WeilConjectures` and `lean/Sheaf` for geometric-fibre/proper-base-change names (no
matching theorem); and `grep -rl` over `dag/nodes` for duplicate geometric-fibre
finite-extension statements (none). The dependency node records and source
signatures were read in full. No `STATEMENT-DISPUTED` flag and no node correction
are needed.

## Second reading by Q03

Independent maintainer second reading of immutable delivery
644a00131cd10a66d2b1a87708c4ce3f741816c2, performed 2026-10-17. The original
placeholder is replaced by this reading; no mathematical statement is changed.

Read the item and all seven statement-dependency nodes in the immutable packet
and snapshot, and the exact declarations in the read-only group clone and pinned
Mathlib. Read the master blueprint item (order 1358), finite-extension theorem
(order 1357), finite-level geometric-fibre corollary (order 1322), rational-category
source (order 1305), Cartesian-square source (order 994), and dimension/base-change
sources (orders 452/451). The item is the stated specialization of the parent
finite-extension theorem, with its category-domain hypotheses explicit.

Hypothesis and conclusion matching:

* Prime and finite extension: `(l : ℕ) [Fact l.Prime]`, `Field E`,
  `Algebra ℚ_[l] E`, and `FiniteDimensional ℚ_[l] E` give exactly the coefficients.
  `pbcPadicCoefficientDatum` uses the actual valuation ring, principal uniformizer
  ideal and positive quotient rings; its property choices are proof data only.
* Proper map and geometric point: `f : X ⟶ Y`, `IsProper f`, `Field Ω`,
  `IsAlgClosed Ω`, and `ybar : Spec (.of Ω) ⟶ Y` match the node. Mathlib's
  properness includes quasi-compactness through universal closedness, hence finite
  type. Its geometric-point description agrees with `SpecToEquivOfField`.
* Fibre and square: `pullback f ybar`, `pullback.fst f ybar`, and
  `pullback.snd f ybar` are the scheme-theoretic fibre and its two projections.
  `geometricFiberSquare` uses `pullback.condition`, `Iso.refl`, and the actual
  projection equations. This is real data with alpha the identity, not a chosen
  arbitrary square or an arbitrary exchange map.
* All four noetherian instances and `_dimX`, `_dimY`, `_dimFiber`, `_dimPoint`
  give precisely the four finiteness assumptions. `topologicalKrullDim` agrees
  with the recorded `Scheme.dim` by `Scheme.dim_eq_topologicalKrullDim`, also on
  the empty scheme. `IsProper (pullback.snd f ybar)` is the explicit assumption
  on the second projection. It is also inherited from proper base change.
* `_hlX`, `_hlY`, `_hlFiber`, `_hlPoint` express invertibility of l on each
  scheme. Global invertibility is equivalent to stalkwise invertibility for this
  constant section, so it imposes no extra condition.
* `e : ℕ` and `_hFibres` give the nonnegative bound on every geometric fibre of
  f. Test fields are in the same scheme universe, not an unrelated lower universe.
* The four existential witnesses are properties placing the four existing
  operations in the full integral subcategories. They precede the quantifier over
  every rational K, as in the parent theorem, and do not choose new operations.
* `PbcRationalCategory` is the published raw scalar localization of
  `PbcBoundedConstructibleComplete`, with unchanged integral objects and Hom
  localized at the uniformizer. There is no Karoubi envelope or condensed-category
  substitution. `finiteExtensionRationalExchangeComponent` is literally the
  localization of `constructibleCompleteExchangeComponent`, with endpoints
  completed pullback along ybar after f_* and direct image along the second
  projection after completed pullback along the first. `IsIso` therefore gives
  exactly the displayed exchange in the rational category on Spec Ω.

The parent theorem's signature supplies exactly these witnesses and component
for this square. Its defining exchange was read, not inferred from its name.
The module docstring and theorem docstring cite the source and blueprint node;
the proof description constructs the square, checks the hypotheses and specializes
the parent theorem. The only theorem body is `by sorry`. The square helper has
real data and introduces no independent mathematical notion requiring a new node.

Universes: `Scheme.{u}` and geometric-point fields `Type u` follow the recorded
scheme API; coefficient fields `Type (u + 1)` follow the actual unlifted coefficient
interface in `IntegralUniformCoefficient`. The small pro-etale site's object and
morphism sizes are retained; no equality between them is imposed. There are no
unbound variables (`autoImplicit false`), extra base-field assumptions, normed-field
instances, separateness hypotheses on X or Y, or nonemptiness assumptions.

Edge cases: zero K, uniformizer-power torsion objects, empty fibre, empty X,
f the identity, e=0, E=Q_l (in the coefficient universe), ramified and unramified
finite extensions, and algebraically closed Ω of arbitrary allowed characteristic.
Characteristic l is excluded exactly by the explicit invertibility assumptions.
Empty Y admits no ybar, consistently with the statement. The fibre-dimension
bounds use bottom for empty fibres and do not force them nonempty.

Independent searches used `rg` for geometric-fibre/exchange, stalk/proper,
rational/geometric-fibre and exact declaration names in lean/Sheaf, pinned Mathlib
AlgebraicGeometry, the older WeilConjectures tree and the group clone's current
WeilConjectures tree. No exact duplicate was found. The existing condensed proper
base-change theorem in the group clone's 51-module framework was read in full:
it has condensed coefficients and finite-type separated schemes over a positive
characteristic field, so it is not an exact match and is not used as a substitute.
The worker's recorded semantic and type-pattern searches were also inspected.

Findings repaired: H11, the original second-reading text was a placeholder rather
than a reading; this section replaces it. The helper was missing from the item's
`lean.declarations`; the replacement lean record lists both declarations, as
required by the same-notion helper rule. `lean.statement` is already verbatim equal
to the theorem signature and is preserved. There are no new nodes, dependency
repairs, stage-2 statement corrections or citer changes.

Compiler evidence: the original report supplied no command/output transcript.
Independent reproduction used exactly:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q03 cor-weil-pbc-geometric-fiber-finite-extension snapshot/lean/Sheaf/Paper/GeometricFiberFiniteExtension.lean
```

Exit code 0. Wrapper output: sandbox Sheaf/Stage2/Sandbox0.lean passed in 3.8 s;
library Sheaf/Paper/GeometricFiberFiniteExtension.lean passed in 2.6 s. The current
wrapper submits to the server's private side overlay with wire confirmation;
it emitted no errors or warnings. No direct ssh command, global build, live Lean
write, repository edit, branch mutation, delivery or landing was performed.
