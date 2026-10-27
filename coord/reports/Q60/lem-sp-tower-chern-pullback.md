## Worker report

Module: `Sheaf.Paper.TowerChernPullback`.
Declaration: `AlgebraicGeometry.ProEtale.tower_firstChern_pullback`.
This states the equality of the actual coefficient-linear Chern morphisms after
arbitrary scheme pullback. Its only proof is `sorry`. No definitions, auxiliary
theorems, new nodes, dependency repairs or statement corrections are delivered.
The accepted Q74 stage-1 split is preserved, including all seven proof steps.

The inherited BLOCKED ending concerned stage 1. The current node has no Lean
record and coord/queue.tsv lists stage 2. coord/brief-stage2.md section 0 expressly
authorizes this handoff without a released stage-1 repair note.

### Every hypothesis and clause

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Its valuation ring | The existing `Padic.coefficientExtensionIntegers l E` inside `Arings l E T` |
| Any morphism X to Y | `{X Y : Scheme.{u}} (f : X ⟶ Y)` |
| ell invertible on X and Y | `_hX : IsUnit (l : Γ(X, ⊤))` and `_hY : IsUnit (l : Γ(Y, ⊤))` |
| Invertible O_Y-module L | `(L : Y.Modules) [Scheme.Modules.IsInvertible L]` |
| B_n = O_E/ell^n, n >= 1, with quotient transitions | `Arings l E T` is `spCoefficientCommRings l E T`; its internal index n denotes exponent n+1 and its maps are the quotient maps |
| Varying-coefficient towers and ordinary derived categories | `Systems T (Arings l E T)` and `D T (Arings l E T)`, the recorded module category of the system topos and its ordinary derived category |
| The exact tower inverse-image functor | `SpTowerShriek.pull l E b g`, definitionally `g.pull.mapDerivedCategory`; `g` is the recorded normalized geometric realization of f, not an unconstrained functor |
| The two constructed Chern morphisms | `firstChern l E cY (Scheme.Pic.ofIsInvertible L)` and `firstChern l E cX (Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L))` |
| Same connecting-morphism sign convention | `_nY : cY.Normalized l E` and `_nX : cX.Normalized l E` fix the unit, Kummer boundary target, and scalar-extension normalizations |
| theta^0, coefficient-unit identification | `(θ₀ : CoefficientPullback l E b f g)` and `(θ₀.derivedIso l E).hom`; its section normalization is the actual constant coefficient map |
| theta^1, roots and coefficient maps | `(θ₁ : LinePullback l E f g cY cX)` and `(θ₁.derivedIso l E).hom`; its ordinary adjoint on every root tensor is precisely coefficient restriction tensor root restriction |
| Power/quotient transitions z tensor a -> z^ell tensor bar a | Inherited from `cY.rootForget`, `cX.rootForget`, the scalar models, and `LinePullback.iso`, which is an isomorphism of whole module systems; its normalization uses the existing power-compatible `restrictRoot` |
| Canonical shift comparison | `((SpTowerShriek.pull l E b g).commShiftIso (2 : ℤ)).hom.app (line l E cY)` |
| theta^1[2] composed with f^*c_1(L) | The left-hand composite: mapped `firstChern`, shift comparison, then `((θ₁.derivedIso l E).hom)⟦(2 : ℤ)⟧'` |
| c_1(f^*L) composed with theta^0 | The right-hand composite: coefficient-unit comparison followed by `firstChern` of the actual pulled-back invertible module |
| Equality in D(Tow(X,O_E)) | A literal equality of morphisms in `D X (Arings l E X)`, with both source and target fixed by the displayed constructions |
| No Noetherian, finite-type or flatness hypothesis | None occurs. The only geometric binder is `f : X ⟶ Y` |

The presentation parameters `b`, `g`, `cY`, `cX`, `θ₀`, `θ₁` name the canonical
constructions already supplied by the dependencies. They do not substitute arbitrary
morphisms for these constructions. `b.realization` is the section-normalized
 equivalence from `spCoefficientTowers` to the recorded system-site category.
`g.generic`, `g.pull_eq`, its coefficient equalities and normalized level comparisons
fix the inverse image induced by the actual small pro-etale morphism. `cY` and
`cX` contain actual universal derived scalar models; `firstChern` is a definition
of their composite, never a free arrow. The two `Normalized` hypotheses express
exactly the stipulated choice of the same Kummer construction and sign. The two
pullback records include their normalization equations. No existence, cartesian
condition on L, or arbitrary derived-map comparison has been assumed in place
of the conclusion.

The coefficient ring and scheme universe are both written u, as in the existing
Chern interface. This is a common ambient universe: any two initially different
bounds can be placed in their maximum. The site remains `T.ProEt` with object
universe u+1 and morphism universe u; no equality of those site universes is imposed.
Module coefficients are at u+1 and the ordinary derived localization at u+2.

### Dependency declarations read and used

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, retaining the imported coefficient
  integer-ring constructions of `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and its pullback instance.
  `WeilConjectures.AlgebraicGeometry.Picard.Group` supplies
  `Scheme.Pic.ofIsInvertible`, so both Chern inputs come from actual invertible modules.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`:
  `AlgebraicGeometry.ProEtale.spCoefficientTowers`, `spEllIdeal`, and its quotient diagram.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `spCoefficientCommRings`, `SpCoefficientTowersAbelian`, and
  `sp_coefficient_towers_abelian`. These provide the actual varying-ring system category.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.SemilinearDerivedSectionsData` and
  `semilinearDerivedSections`; their geometric interface is used by
  `SpTowerShriek.Geometry` and its exact localized `pull`.
- `Sheaf.Paper.SmoothPurityTowerClasses`:
  `AlgebraicGeometry.ProEtale.TowerClasses`. Its public imported construction
  modules give `SpTowerClasses.Chern`, `Chern.Normalized`, `firstChern`, `line`,
  `CoefficientPullback.derivedIso` and `LinePullback.derivedIso`.
  The ordinary pullback records were read in `TowerClassDiagonal` and
  `TowerClassPullback`; their derived comparisons in `TowerClassDiagonal` and
  `TowerClassProjective`. `TowerClassChern` was read in full: its `firstChern`
  is the prescribed scalar extension of `firstChernR` with the shift and target maps.
- `Sheaf.Paper.CartesianCoefficientTwists`:
  `spRoots_cartesian`, `spFiniteTwists_cartesian`, and `spTwists_cartesian`,
  including the full root-transition compatibility clause. Their root and
  coefficient maps are the same ones used in the section normalizations.

Each available proof dependency is imported, using plain imports for proof-only
modules. Mathlib leaves use their recorded files: DerivedCategory.Ext.Map,
DerivedCategory.ShortExact, DerivedCategory.TStructure and DerivedCategory.FullyFaithful.
No proof import cycle is introduced: the new module has no existing importers.

### Edge cases checked

- Identity f: the normalized unit and root comparisons give the identical Chern arrow.
- Trivial line: the line-bundle extension splits and the resulting Chern arrow is zero.
- Empty X or Y: no Nonempty premise is imposed; global-ring units, site functors,
  empty-chart root restriction and module pullback retain their existing meanings.
- First positive coefficient level: internal index zero is exponent one; no level is lost.
- Ramified E: quotients are by ell powers, not by uniformizer powers of the same
  exponent. No unramified or flat coefficient-map hypothesis is introduced.
- Arbitrary nonflat f and schemes without finiteness conditions: exactness is that
  of the topos inverse image, not tensor exactness over structure sheaves.
- Negative derived degrees and arbitrary whole systems: no boundedness or
  normalization subcategory is substituted for the ordinary derived category.
- The equation is formed before evaluation; equality detection by finite-level
  evaluation is neither asserted nor assumed.

### Searches

`msearch.py` was run with group Q60 and this item:

- LeanFinder: "Kummer first Chern classes of line bundles commute with scheme
  pullback in the ordinary derived category of varying coefficient towers";
  eight results about ordinary scheme/module pullback, no tower Chern equation.
- LeanFinder: "Kummer first Chern class commutes with pullback in derived categories
  of coefficient towers"; eight ordinary module pullback/coherence hits, no match.
- Loogle: `"Chern"`; only Lean matcher-name substring matches, unrelated.
- Mathlib grep: `chern|Chern|kummer|Kummer`, subdirectory `AlgebraicGeometry`;
  zero hits.
- LeanSearch: "Kummer first Chern morphism commutes with pullback on inverse
  systems of sheaves"; ordinary sheaf/module pullback and stalk results, no match.
- `rg` of the project `WeilConjectures` and `Sheaf` trees for Chern/Kummer pullback
  and this item: the finite etale result
  `Etale.leftDerivedUpperStar_map_chernClass` exists in
  `WeilConjectures.EtaleCohomology.Purity.Smooth.ExtendScalarsCohomologyPullback`.
  Its signature was read: it treats one finite coefficient ring on the etale site,
  and is not this equation in the derived category of coefficient systems.
  The existing tower construction modules define the required objects and
  comparisons but do not assert this naturality equality.
- Search for `tower_firstChern_pullback` and `lem-sp-tower-chern-pullback` in both
  source roots found no existing declaration before this delivery.

No STATEMENT-DISPUTED flag or node fault remains. No statement change is needed.

### Validation

The required `scompile.py Q60 lem-sp-tower-chern-pullback` passed for the delivered
file in both sandbox and library module forms (43.7 s and 16.9 s). No errors or
non-sorry warnings. All variables and the sole universe u are explicitly bound;
`autoImplicit` is false. The theorem's proof is exactly `by sorry`.

## Second reading by Q60

The worker re-read the final signature against each clause, as recorded above.
This is a self-check, not an independent second worker review. The dispatch
explicitly prohibits starting other agents and says the maintainer's independent
review reads this delivery. No independent review is claimed here. The checks
specifically covered composite orientation, the necessary commShift comparison,
actual invertible-module pullback, the Kummer sign normalizations and the
whole-system (rather than finite-level) Hom type. No mismatch was found.
