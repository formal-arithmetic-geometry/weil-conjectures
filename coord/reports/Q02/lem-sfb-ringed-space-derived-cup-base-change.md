## Worker report

The item is stated by `AlgebraicGeometry.RingedSpace.derivedCup_baseChange` in
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedCupBaseChange`. Its only postponed proof is
that named theorem. The module also defines the two actual composite arrows,
`CupSquarePresentation.cupFirst` and `CupSquarePresentation.exchangeFirstCup`.
All their data are compositions of the recorded cup, exchange and canonical tensor
comparisons. No theorem is proved and no definition contains `sorry`.

I read Stacks `cohomology.tex`, `lemma-base-change-cup-product` (0H99), including its
omitted proof, and `remark-cup-product` (0B68). The former gives precisely the square
of derived morphisms, without Cartesian, flatness or boundedness assumptions; the
latter specifies the cup as the adjoint of tensor comparison followed by the two
counits. The node's supplied five-step proof is carried into the theorem docstring.

Hypothesis and clause correspondence:

- The four spaces with sheaves of commutative rings are `X X' Y Y' : RingedSpace.{u}`.
  The new `cupCorner` uses exactly `Opens X`, its open-cover topology, and `X.sheaf`;
  it does not introduce a scheme, another site, or constant coefficients.
- The common module universe is explicit `u`. Each of the four module categories
  has its own explicit `HasDerivedCategory.{w}` argument in the common chosen
  localization universe. This is the size convention, with no equality imposed
  between the topological/coefficients universe `u` and derived Hom universe `w`.
  `Opens X` is a set in `u`, so its use in `RingedTensorCorner.{u,w}` is small as
  requested. A common large bound is allowed by the node's size convention.
- The four ringed-space maps are the theorem arguments `f f' g g'`. `_comm :
  g' ≫ f = f' ≫ g` is equality in the ringed-space category, including the structural
  sheaf maps, not just equality of continuous functions. It is needed to construct
  the simultaneous ringed square, even though the already presented square is used
  in the displayed formula.
- The representation of each map is pinned by `CupEdgeRealization`: `inverse` and
  `direct` are topological sheaf pullback/pushforward; `inverseRing` is the actual
  inverse-image ring; `ringMap` is the actual `tensorPullbackRingMap` of the structural
  sheaf map. `object_eq` and `map_eq` are verbatim the inverse-image-then-change-of-rings
  formulas in the recorded general derived adjunction. `pushforward` is the recorded
  `moduleDirectImage v`; `right` is the recorded K-injective `derivedModuleDirectImage v`.
- `RingedTensorModel` supplies the natural identification of each tensor bifunctor
  on flat-term K-flat pairs. `RingedTensorEdge` retains the additive ordinary tensor
  pullback, its total left-derived comparison, its adjunction, and its canonical
  ordinary pure-tensor normalization. Its `tensorComparison` is the existing unique
  K-flat-representative-normalized comparison, not a free natural isomorphism.
- The relative cups are literally `SheafOfModules.RingedSiteCup.relative` for the
  two vertical edges, with their models. Its definition is the adjunction Hom
  equivalence applied to tensor comparison followed by the two counits.
- `p.square.exchange` is literally the existing `RingedTensorSquare.exchange`, the
  Mathlib mate of `p.square.derivedComparison`. Its derived comparison is the unique
  extension of the ordinary module square, characterized on K-flat representatives.
  The insertion equation of `RingedTensorSquare` enforces ring compatibility and
  fixes the module square on scalar-extension generators. In the open-set topos
  the set comparison is canonical: a natural transformation between these geometric
  inverse images is fixed on the open subterminal generators. No tensor-square
  coherence identity is assumed as presentation data.
- For all unbounded `K L : DerivedCategory (SheafOfModules (moduleRings X))`, the first
  conjunct is `p.cupFirst K L = p.exchangeFirstCup K L`. Expanding the first gives
  `Lg*(c_f) ≫ beta_(K tensor L) ≫ Rf'*(mu_g')`; expanding the second gives `mu_g ≫
  (beta_K tensor beta_L) ≫ c_f'`. These are the displayed node arrows in Lean's
  left-to-right composition convention, with exactly the stated common source and
  target in the derived category of modules on `Y'`.
- The next conjunct quantifies over `K L K' L'` and morphisms `a : K ⟶ K'`,
  `b : L ⟶ L'`. It states the naturality square with the input map
  `Lg*(Rf_*a tensor Rf_*b)` and output map `Rf'_*(Lg'^*a tensor Lg'^*b)`.
  The first conjunct transfers the same naturality to the second route.
- The final conjunct quantifies over arbitrary `M` and `a : K tensor L ⟶ M`.
  It equates `Lg*(c_f ≫ Rf_*a) ≫ beta_M` with the second route followed by
  `Rf'_*(mu_g' inverse ≫ Lg'^*a)`. Thus it retains the coefficient-composed
  clause and the canonical inverse tensor identification with its correct direction.
- No Cartesian, flatness, quasi-coherence, Tor-amplitude, boundedness or invertible
  exchange hypothesis occurs. The only inverse in the coefficient clause is the
  pullback tensor isomorphism, never the base-change map.

`Nonempty (CupSquarePresentation f f' g g')` is a conclusion, not an added assumption.
It supplies the missing open-site specialization. The formula then quantifies over
EVERY such presentation, so the statement does not hold only for a conveniently
chosen representation. Nothing is defined by selecting data from this postponed
existence conclusion. The defined presentation consists of the existing canonical
objects and their normalization data; it contains neither the desired equality nor
an arbitrary base-change map. This records explicitly the choices of models which
are implicit in the source, together with independence of those choices.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q` and `Qh`; full signature and docstrings read.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is
  transparently Mathlib's `SheafOfModules`; the existing Mathlib underlying category
  is used in all signatures. Its object and morphism structures were also read in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`.
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `moduleDirectImage`, `derivedModuleDirectImage`, and their K-injective computation
  documentation. `moduleRings` is its imported recorded ring-sheaf specialization.
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral`: compatibility import
  of `AlgebraicGeometry.RingedSpace.derivedModulePullback_adjunction`; its complete
  adopted source statement and proof documentation were read, including the precise
  object/map formulas and comparison on K-flat complexes. Its public tensor ring map
  and topological inverse-image module formulas are used, without a copied pullback.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its equality with the live
  `IsAcyclicTensorKFlat` specialization. The existing `RingedTensorModel` uses the
  corresponding acyclicity predicate; no second K-flatness definition is made.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal` and its existing localized sheafified tensor. The actual
  tensor model fields are the existing `RingedTensorModel` representation isomorphisms.
- `Sheaf.CategoryTheory.RingedSiteModuleCupProduct`:
  `SheafOfModules.RingedSiteCup.relative`, signature, docstring, and complete defining
  expression read and used literally for both relative cups.
- `Sheaf.Paper.RingedTensorSquarePresentation`: `RingedTensorCorner`,
  `RingedTensorModel`, `RingedTensorEdge`, `tensorComparison`, `insertion`,
  `RingedTensorSquare`. All fields/signatures/docstrings were read.
- `Sheaf.Paper.RingedExchangeTensorCoherence`:
  `RingedTensorSquare.derivedComparison`, `exchange`, `RingedTensorEdge.projection`,
  `ringedExchangeTensorCoherence`. Its canonical comparison and mate definitions
  were read; the equality is the planned proof input, without assuming it as data.
- Proof imports `Sheaf.Paper.ProjectionMateExact` and
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` retain the recorded
  projection transpose/naturality and canonical tensor-pullback inputs.
  `def-weil-pbc-adjunction-mate` is the Mathlib `mateEquiv` interface publicly imported
  by the square presentation, not a missing private construction.

Edge cases checked before writing: empty ringed spaces still have the set of opens
and their ordinary module category; zero rings and zero complexes remain allowed;
no positive cohomological degree, boundedness or nonzero coefficient is required.
Identity squares reduce to the usual cup under the canonical adjunction/model
identifications. Non-Cartesian commuting squares and nonflat structural maps are
included because the only square assumption is equality of ringed-space composites.
The coefficient map may be zero, identity (to the tensor object), or completely
arbitrary. There is no inverse of beta in any definition or theorem clause.

Searches for the item:

- `msearch.py leanfinder`: “For a commutative square of ringed spaces derived relative
  cup products commute with base change” returned 8 hits on underived pullback
  composition and scheme identities, not this derived equality.
- `msearch.py leansearch`: “Derived relative cup product is compatible with the base
  change map for a commutative square of ringed spaces” returned 8 hits on Kähler
  differentials, linear base change and tensor maps, not this equality.
- `msearch.py loogle`: `"cup", "baseChange"` returned 0 hits.
- `msearch.py grep`: `cupProduct|cup_product|relativeCup` in `CategoryTheory` returned
  0 hits. Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `derivedCup.*base|cup.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*[Cc]up` found only specialized
  Kummer/adic product applications and supported cup code, not this general theorem.
  Search by the exact item id found no existing Lean declaration.

Server validation: both delivered modules compiled individually, in dependency order,
through `scompile.py`, with no errors or warnings. The presentation compiled in about
4 seconds and the main statement in about 6 seconds, within the unchanged 60-second
limit. All variables/universes are bound; `autoImplicit` is explicitly disabled.
The only `sorry` is the main named theorem and has the complete five-step proof plan.
The item statement, proof and proof dependencies are unchanged; its statement
dependencies gain only the new definition node below. No statement dispute remains.

## New nodes

`def-sfb-ringed-space-cup-presentation` defines the open-set-site specialization of
the EXISTING generic ringed tensor square presentation. Its module is
`Sheaf.AlgebraicGeometry.RingedSpaceCupPresentation`, primary declaration
`AlgebraicGeometry.RingedSpace.CupSquarePresentation`, with helpers `cupCorner` and
`CupEdgeRealization`. It fixes the exact four original spaces/sites/ring sheaves,
the four actual ring maps, the precise underived pullback formulas and both direct
images. It retains the existing canonical comparison and insertion normalization.
It does not reconstruct module sheaves, derived categories, tensor products,
K-flatness, cups, or mates. Its source is the open-site interpretation of Stacks
0H99, together with 0B68 and 079W. All definitions are explicit structure data; no
existence proof is hidden in a definition.

I searched `dag/nodes` for the specialization and ran `tools/blueprint_refs.py search
'ringed space tensor square presentation'` (0 matches). A broader DAG search found
scheme coefficient/stalk/single-degree applications and the existing generic
presentation, none supplying this particular open-site specialization. Direct `rg`
in both project Lean trees for `RingedSpaceTensorSquare|spaceTensorCorner|SpaceTensorEdge`
found no declaration. The new node's logged searches are:

- LeanSearch query “A commutative square of ringed spaces induces the canonical
  tensor compatible square of derived module pullback functors on the open set sites”:
  8 hits on ordinary module pullback/adjunction and abstract `CatCommSq.iso`.
- LeanFinder query “Canonical tensor square presentation of a commutative square of
  ringed spaces using open set sites derived tensor K-flat models and actual derived
  direct images”: 8 hits on presheaf tensors, relative differentials and flat ring tensors.
- Loogle query `"RingedSpace", "tensor"`: 0 hits.
- Mathlib grep query `RingedSpaceTensorSquare|spaceTensorCorner|SpaceTensorEdge`: 0 hits.

The ancestry command reports the inherited nearest blueprint ancestor as `None`;
the new node preserves that null ancestor and prepends the item to the inherited
`via` chain. This supporting specialization does not change a blueprint unit.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
