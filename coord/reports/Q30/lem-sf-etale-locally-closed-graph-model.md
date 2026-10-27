## Worker report

Module: `Sheaf.SixFunctors.EtaleLocallyClosedGraphModel`.
Main declaration: `AlgebraicGeometry.Etale.etaleLocallyClosedGraphModel`.
The node's mathematical statement and dependencies are unchanged. This module exposes the
actual product-graph comparison, rather than selecting an unspecified endpoint isomorphism
from the upstream `nonempty_iso_rightDerivedLowerShriekOfCompactification` theorem.
All helper declarations belong to the graph construction described by this node. They do
not introduce a second definition of derived direct image, extension by zero, their
compositors, or proper/open exchange. There are no new nodes or dependency repairs.

Hypothesis and clause correspondence:

- A finite commutative ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`. This is the
  published six-functor coefficient universe. The zero ring is permitted.
- Arbitrary schemes and a morphism: `{X Y C U P : Scheme.{u}} {f : X ⟶ Y}`. There are no
  Noetherian, quasi-compact-open, separated-scheme, boundedness, or constructibility binders.
- The supplied factorization `X --j--> C --c--> Y`: the explicit maps `j,c`, instances
  `[IsOpenImmersion j] [IsProper c]`, and `h₁ : j ≫ c = f`.
- The proper-open-proper factorization: explicit maps `a,e,π`, instances `[IsProper a]`,
  `[IsOpenImmersion e]`, `[IsProper π]`, and `h₂ : a ≫ e ≫ π = f`.
- The common product is exactly `pullback π c`. Its projections `p₁,p₂` are
  `pullback.fst π c` and `pullback.snd π c`. The equality supplied to `locallyClosedGraphV`
  is `(Category.assoc a e π).trans (h₂.trans h₁.symm)`, so its components are exactly
  `(a ≫ e,j)`, rather than additional freely chosen maps.
- `O₁ = T ×_C X` is `pullback (pullback.snd π c) j`; `O₂ = T ×_P U` is
  `pullback (pullback.fst π c) e`. Their open maps `b₁,b₂` are the first projections;
  their proper projections `q₁,q₂` are the second projections.
- `locallyClosedGraphS₁` is `pullback.lift v (𝟙 X) ...` and
  `locallyClosedGraphS₂` is `pullback.lift v a ...`. Thus their composites with `q₁,q₂`
  are definitionally specified by the pullback-lift projection laws to be `𝟙 X,a`.
- `O₁₂` is `pullback b₁ b₂`, with `u₁,u₂` the first and second projections.
  `locallyClosedGraphS₁₂` is `pullback.lift s₁ s₂ ...`. Its composites with `u₁,u₂`
  are therefore the required `s₁,s₂`, with the same graph in `T`.
- Properness of all three maps is asserted by the fields `properS₁`, `properS₂`,
  `properS₁₂` of `LocallyClosedGraphModel`. These are conclusions, not assumptions of
  `etaleLocallyClosedGraphModel`. The first two are instance fields for use in the
  specified middle comparison. The model's other fields follow them in the structure,
  so the main theorem needs no properness assumption on either graph.
- All functors act on ordinary unbounded small-etale module derived categories:
  `D((j)_!open[ModuleCat.{u + 1} A])` is termwise exact extension by zero descended to
  `DerivedCategory (Sheaf _ (ModuleCat A))`; `R((c)_*[ModuleCat.{u + 1} A])` is the
  published total right derived pushforward. Functor composition `F ⋙ G` means first F,
  then G, so `Dj_! ⋙ Rc_*` renders the node's `Rc_* Dj_!`.
- The specified `B₁` is the real definition `locallyClosedGraphSide₁`. It inserts
  `(rightDerivedLowerStarIdIso A X).symm` and the inverse direct-image compositor for
  `s₁ ≫ q₁ = 𝟙 X`, applies `openImmersionLowerShriekLowerStarExchangeIso` for the flipped
  pullback square of `p₂,j`, and composes `p₂,c` to `p₁ ≫ π` using
  `pullback.condition.symm`. Its type is the exact two endpoint words in the node.
- The specified `B₂` is `locallyClosedGraphSide₂`. It inserts the inverse direct-image
  compositor for `s₂ ≫ q₂ = a`, applies the corresponding exchange for `p₁,e`, and
  composes `p₁,π`. Again its type is the exact word in the node.
- The specified middle comparison is `locallyClosedGraphMiddle`: invert the
  `rightDerivedLowerStarCompOpenImmersionLowerShriekIso` for `s₁₂,u₁,s₁`, combine
  `Du₁_!` and `Db₁_!` by the inverse open compositor, use
  `mapDerivedCategoryOpenImmersionLowerShriekCongr ... pullback.condition`, split the
  composite over `O₂`, and apply the interchange for `s₁₂,u₂,s₂`. These are exactly the
  six displayed middle words in the node, with the required directions. Both factorizations
  are forced by `pullback.lift_fst`/`pullback.lift_snd`, discharged by simplification in the
  definition, not by an additional geometric assumption.
- `locallyClosedGraphIso` is exactly `B₁`, then the inverse associator, then
  `Functor.isoWhiskerRight B₁₂ R(πp₁)_*`, then the associator, then `B₂.symm`.
  This renders `B = B₂⁻¹ ◦ R(πp₁)_*(B₁₂) ◦ B₁` in Lean's composition convention.
- The model's `comparison` is an isomorphism of those endpoint functors and its
  `comparison_eq` requires equality with `locallyClosedGraphIso`, fixing the actual
  comparison, not merely its isomorphism class. The main theorem is `Nonempty` of this
  constrained record. The definition of the canonical iso has real data and never
  chooses data from this existence assertion.
- Every displayed comparison is typed as a natural isomorphism (`≅` of functors), so
  its inverse equations and naturality are part of the type. Open maps and the open
  intersection projections use the existing base-change instances. The identity-top
  exchange uses the existing proof that factoring through an open gives its Cartesian
  square. Direct-image compositors are the published adjunction-normalized ones.
- No tensor-compatibility conclusion is present.

Dependency declarations read and used (full signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category of
  scheme morphisms, recorded on def-pc-scheme.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`, its
  composition instance, and `isOpenImmersion_stableUnderBaseChange` and pullback instances.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, its proper
  pullback instances, and `IsProper.of_comp` (proper-to-separated, used by the proof plan).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.lift`, and its projection laws and `pullback.condition`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, with
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` is exactly the ordinary unbounded
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))` used by these functors.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, its additive and exactness
  instances, including `preservesFiniteLimits_openImmersionLowerShriek`.
- `Sheaf.AlgebraicGeometry.EtaleProperOpenTensorSquare`:
  `AlgebraicGeometry.Etale.etaleProperOpenTensorSquare`; its first conjunct says the
  exact exchange used here is invertible. The second, tensor, conjunct is not asserted
  for B. The comparison used here is the same upstream
  `openImmersionLowerShriekLowerStarExchange`, explicitly the unit/base-change/counit
  mate. The existing `openImmersionLowerShriekLowerStarExchangeIso` is `asIso` of it.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriekComp` (re-exported from upstream)
  and `openImmersionLowerShriekComp_coherence`. The existing
  `mapDerivedCategoryOpenImmersionLowerShriekComp` descends that same open compositor.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, whose normalized
  comparison on K-injective representatives is the cited general framework.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`, supplying
  the composite-adjunction and identity normalization. For the exact-inverse-image
  etale realization, `rightDerivedLowerStarComp` in upstream `Derived.UpperLowerStar`
  is explicitly the conjugate of pullback composition through the composite adjunction.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  existing `rightDerivedLowerStarCompOfEq`, `rightDerivedLowerStarIdIso`,
  `mapDerivedCategoryOpenImmersionLowerShriekComp`,
  `mapDerivedCategoryOpenImmersionLowerShriekCongr`,
  `rightDerivedLowerStarCompOpenImmersionLowerShriekIso`, and
  `openImmersionLowerShriekLowerStarExchangeIso` are used directly; none is redefined.

Edge cases checked: the empty X and empty opens impose no extra nonemptiness requirement;
all maps and pullbacks remain defined. The zero coefficient ring is allowed. Taking any
factorization map to be the identity uses the existing identity and composition isos,
without extra quasi-compactness assumptions. Neither the graph nor its intersection is
assumed a closed immersion, avoiding an unwarranted strengthening of properness. Schemes
need not be separated over a ground base. Unbounded complexes, including zero and
arbitrarily shifted complexes, are in the functors' domain. No test-scheme quantification
uses an independent smaller universe. No extra size equality is imposed.

Searches made using the prescribed msearch wrapper:

- LeanFinder: `Explicit proper open proper product graph comparison of unbounded etale
  compact support derived direct images` returned eight affine-transition-limit and
  compact-open-cover results. None is an etale graph comparison.
- Loogle: `"lowerShriek", "Iso"` returned zero hits.
- Mathlib grep in AlgebraicGeometry:
  `graphModel|locallyClosed|rightDerivedLowerShriek` returned twelve locally-closed-locus
  results (group schemes, immersion loci, quasi-finite morphisms); none constructs the
  specified derived comparison.
- LeanSearch: `Unbounded etale compact support explicit graph comparison proper open
  proper factorization` returned eight properness/etale-locus results; none is a match.
- `rg` of upstream SixFunctors and `lean/Sheaf/AlgebraicGeometry` for `graphModel`,
  `locallyClosed`, and `nonempty_iso_rightDerivedLowerShriekOfCompactification` found the
  source theorem at `Derived/LowerShriekComposition.lean:193`; its local `eA,eB,eC` are
  not publicly named constructions, and its signature does not assert properness of the
  graph maps or identify its witness. Existing unrelated locally-closed closure models
  concern a different comparison and were not duplicated.
- `rg` for the node id in `lean/WeilConjectures` gave no exact binding. Searching
  `locallyClosedGraph|LocallyClosedGraphModel` across `WeilConjectures`, `Sheaf`, and
  `dag/lean_names_upstream.json` gave no existing declaration with the new names.

Validation: the module compiled cleanly through the prescribed `scompile.py`, both as a
sandbox file and with its library module name. The only postponed theorem is
`etaleLocallyClosedGraphModel`, with its full six-step natural-language proof in its
source docstring. All constructions have real bodies. No statement dispute or correction.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
