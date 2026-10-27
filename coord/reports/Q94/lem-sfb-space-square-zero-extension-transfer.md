## Worker report

Q94 states `AlgebraicGeometry.AlgebraicSpace.exists_kernelPushout_isEquivalence`
in `Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionTransfer`, with a single
postponed theorem proof. The new definition module
`Sheaf.AlgebraicGeometry.SpaceFixedIdealExtensions` supplies the missing category
and normalized kernel-pushout interface. All its data are explicit; it contains
no sorry. The item's natural-language statement and proof are unchanged.

Clause-by-clause correspondence:

- Schemes and algebraic spaces over S: `{S : Scheme.{u}}` and
  `{X B B' : AlgebraicSpace S}` use the existing fppf-sheaf full subcategory.
  Morphisms are its actual natural transformations, and module sheaves are
  the existing `X.Modules` on its small etale site with its structure sheaf.
- First-order base thickening: `i : B ⟶ B'` and
  `hi : IsSpaceFirstOrderThickening i`. The predicate tests representable
  scheme base changes by the existing scheme `IsFirstOrderThickening`, namely
  closed immersion with square-zero ideal. Such a map is surjective on points
  because a square-zero ideal lies in every prime, including the zero ideal.
  Thus this includes exactly the stipulated full underlying closed subset.
- Its ideal and common etale site: `T : ThickeningSiteModel i` is the existing
  normalized etale-site equivalence with actual scheme reduction pullbacks;
  `J : SquareZeroIdeal T` identifies the ideal with the sectionwise kernel
  of its regular-function quotient. These are normalized presentations of
  the given thickening and its ideal, not arbitrary replacement ring maps.
  No quasi-coherence or chosen tensor structure is assumed for J.
- The morphism is `f : X ⟶ B`. Quasi-compactness is
  `[CompactSpace (Point X.obj.obj)]`, using the existing point topology.
  Quasi-separatedness is `hqs : IsAbsolutelyQuasiSeparated X`, the existing
  affine-test criterion equivalent to quasi-compactness of the absolute
  diagonal; no restriction on the base S is added.
- Arbitrary kernel modules and their map are `{F G : X.Modules}` and
  `u : F ⟶ G`. There is no `IsQuasicoherent` assumption on either kernel.
- The unbounded derived category and its full D_QCoh subcategory are the
  existing `X.DerivedModules` and `X.DerivedQCoh`, on the equivalent small
  affine ringed model in the original section universe u.
  `[HasDerivedCategory.{w} X.SmallModules]` allows any localization morphism
  universe w, independently of u; it is the node's derived-category choice.
- The hypothesis `h` quantifies over EVERY `K : X.DerivedQCoh`. Its map is
  `a ↦ a ≫ (DerivedCategory.singleFunctor X.SmallModules 0).map
  (X.smallModuleRestriction.map u)`, so it is exactly postcomposition with
  u[0] from Hom(K,F[0]) to Hom(K,G[0]); `Function.Bijective` is the stipulated
  universal Hom test. The use of the existing restriction equivalence
  preserves all Hom sets and cohomology and does not change the test.
- The fixed inverse-image ideal map is represented by its scalar-extension
  adjoint `c : (moduleTensorPullback f).obj J.obj ⟶ F`. This is equivalent to
  an f^{-1}O_B-linear map f^{-1}J → F, NOT an assumption that F is pulled back
  or that a mere inverse image equals tensor pullback. The adjunction sends
  d to `(a ⊗ j ↦ a d(j))` and its inverse restricts to `1 ⊗ j`.
- Extension objects are EXACTLY the existing `SpaceSquareZeroExtension
  (f ≫ i) F`: commutative ring sheaf, quotient to O_X, specified additive
  kernel inclusion, sectionwise injection and exactness at the middle,
  LOCAL surjectivity of the quotient, square-zero kernel, prescribed quotient
  scalar action, and compatible base algebra map on all chart squares.
  In particular sectionwise surjectivity is never imposed.
- `SpaceExtensionMap` requires its ring-sheaf natural transformation to
  preserve the base map, quotient and coefficient map; for identity coefficient
  maps it gives precisely the extension category's morphisms. RingCat maps
  are unital. Its identity, composition and category laws have actual terms.
- `HasBaseIdealMap` requires the base action on each j to equal
  `inclusion(c(1 ⊗ j))`, using the existing `moduleTensorSection` normalization
  and the actual normalized reduction arrow. All compatible chart pairs and
  all ideal sections are quantified. It therefore gives exactly c_E = c.
  `FixedIdealExtensions` is the FULL subcategory for this predicate.
- The target category uses `c ≫ u`, precisely u c. The conclusion supplies
  `P : FixedIdealExtensions ... c ⥤ FixedIdealExtensions ... (c ≫ u)` with
  `Nonempty (IsKernelPushout u P)` AND `P.IsEquivalence`.
  `IsKernelPushout.arrow` gives actual natural coefficient-u algebra maps;
  `universal` factors every map to an extension with any kernel H and every
  G → H uniquely. This is the kernel-pushout universal property, not an
  arbitrary functor or map. It determines P up to the unique natural
  isomorphism preserving these arrows. Existence is asserted as part of the
  theorem, and no data are chosen from a merely existential sorry theorem.
  Consequently every representative of canonical pushout is an equivalence.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structurePresheaf`, `structureSheaf`, `Modules`, scheme-test representability.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`; the existing
  `SheafOfModules` is used through `X.Modules`, including its linear morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  specialized slice instances for Mathlib `SheafOfModules.IsQuasicoherent`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`; `...FullyFaithful`: the degree-zero single functor
  and its full and faithful instances (the recorded proof dependency).
- `Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData`:
  `SpaceSquareZeroExtension`, `ChartRingMap`, `IsSpaceFirstOrderThickening`,
  `ThickeningSiteModel`, `chartOver`.
- `Sheaf.AlgebraicGeometry.SpaceSquareZeroStalkData`: `SquareZeroIdeal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleTensorPullback`, `moduleTensorAdjunction`, `moduleTensorSection`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedQCoh`,
  `DerivedModules`, `derivedQCohProperty`, with the existing small-model
  restriction from `AlgebraicSpaceSmallRingedModel`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`, with the inherited point topology.
- Proof-only imports use the recorded `SpaceNaiveCotangentComplex` module,
  `isQuasicoherent_moduleTensorPullback` from
  `AlgebraicSpaceModulePullbackQuasiCoherent`, and the recorded sheaf tensor
  module `CochainTensorUniverses`.
  `lem-sfb-space-first-order-ringed-description`,
  `lem-sfb-space-naive-cotangent-quasicoherent`, and
  `lem-sfb-etale-algebra-extension-ext` have no Lean record/module at the read
  base, so there is no module for those proof-only dependencies to import.
  Their arguments are retained in the theorem docstring; their absence is
  not a missing object in this statement.
- `def-weil-size-convention` has a convention-only record; explicit `u w`
  and the existing small affine ringed model render that metatheoretic rule.

Source and edge checks: read defos.tex's full setup and proofs of Tags 0D3P
and 0D3Q, the current blueprint unit at literature/blueprint/latest, and all
statement dependency signatures/docstrings. Checked i = identity (J = 0),
F = G = 0, u = identity, c = 0, the empty space, non-quasi-coherent F or G,
empty fixed-map extension categories, and empty Hom sets. No nonemptiness,
flatness, finite presentation, Noetherian hypothesis, or independent small
universe is imposed. In particular fixed-c categories can be empty; the
conclusion forces the matching target to be empty too. The unrestricted
split extension need not have a given c, so it is not incorrectly used as a
fixed-c object. Absolute quasi-separatedness is used even over a base which
is not quasi-separated.

Searches: the prescribed msearch.py calls and raw search-log responses are
recorded in the new node's mathlib_searches. LeanFinder queried pushout of
square-zero ring-sheaf extensions under derived quasi-coherent Hom tests:
eight hits for module functors and unrelated sheaf pushouts, no transfer
statement. Loogle `Algebra.Extension, TrivSqZeroExt`: zero hits. Mathlib grep
`SquareZero.*Extension|Extension.*Pushout` in Algebra: zero hits. LeanSearch
queried the category with fixed base-ideal map: eight hits for ring pushouts,
individual infinitesimal extensions and split square-zero rings, none with
this small-etale fixed-ideal category. Direct rg of WeilConjectures, Sheaf
and dag/lean_names_upstream.json found none of the new declaration names.
Direct rg of the item id in WeilConjectures found no match. Broader library
and DAG searches found and reused the existing space extension objects,
normalized ideal presentation, derived calculus and absolute-QS predicate.
`blueprint_refs.py search` for `fixed base ideal square zero extension` and
`kernel pushout` each returned zero matching blueprint nodes. The existing
TopCat.SquareZero.Problem and TopCat.SquareZeroSheaf.Hom concern sheaves on
the opens of a topological space, not an algebraic space's small etale site;
they do not supply this category. No existing declaration states the item.

Compilation: both delivered modules passed scompile.py separately in
sandbox and library-module contexts, with no errors or warnings. The only
postponed theorem is the item theorem; no data definition contains sorry.
No statement dispute or source-based correction was necessary.

## New nodes

`def-sfb-space-fixed-ideal-extensions` defines coefficient-changing maps
between the EXISTING SpaceSquareZeroExtension objects, their fixed-kernel
category, the full fixed-base-ideal subcategory and the kernel-pushout
universal-property interface. Source: defos.tex, setup preceding Tag 0D3Q.
Its searches are recorded as above, including the original machine search
responses. It does not duplicate SpaceSquareZeroExtension, SquareZeroIdeal,
first-order thickenings, tensor pullback, or the topological-space-only
extension definitions. All data are real; this definition makes no existence
assertion. The item additionally cites the already landed derived-module
calculus and absolute-quasi-separatedness nodes for their exact interfaces.

## Second reading by Q94

Reopened the item JSON and both final Lean modules for a separate clause
check. This is a worker self-check; no independent agent was started, as the
dispatch brief forbids doing so. Independent mathematical review belongs to
the maintainer's delivery review.

Checked again: the test uses postcomposition with u[0] on all D_QCoh objects;
F and G remain arbitrary. The site model is normalized on actual scheme
pullbacks, the ideal presentation is the kernel, and local exactness of
extension quotients has not become sectionwise surjectivity. Tensor-adjoint
c retains precisely inverse-image linear maps. The equation on each chart
uses the composite with the actual reduction arrow; no arbitrary base action
is substituted. Morphisms preserve base, kernel and quotient, and the fixed
categories are full. The functor's universal property tests every target
kernel and extension, not only fixed-c objects, so it specifies genuine
kernel pushout. Its natural arrows fix the functor on maps. The existential
conclusion includes existence and equivalence rather than assuming either.
Checked empty categories, zero ideal, empty spaces and arbitrary w again.
No mathematical mismatch found. During elaboration the category instance
was made reducible so consumers can read the actual extension-map subtype;
this changes transparency only. No statement changed.
