## Worker report

The module `Sheaf.AlgebraicGeometry.CartierPairTensorAddition` states the complete
item in four theorem declarations, with five `sorry` proofs in total (including
the commuting-square lemma needed to define its canonical cone map). All other
declarations supply real data. No statement correction or disputed statement.

The statement is factored into successive conclusions: the first theorem proves
that the product ideal is Cartier and constructs the normalized framed
isomorphism; the second applies to that isomorphism and Cartier proof; the third
expresses the extension equality; the fourth gives naturality for every inclusion
of opens. Thus `hZ` and `he` in the later clauses are the earlier conclusions,
not additional geometric assumptions.

Clause-by-clause correspondence:

* A scheme T is `T : Scheme.{u}`. The divisors are `i₁ : D₁ ⟶ T` and
  `i₂ : D₂ ⟶ T`, with `IsClosedImmersion` and `h₁/h₂ : iₐ.ker.IsInvertible`.
  The latter is precisely the recorded locally-regular-principal Cartier ideal,
  including over nonreduced schemes. The specified Z is `k : Z ⟶ T`, also a
  closed immersion, with `hk : k.ker = i₁.ker * i₂.ker`.
* Ideals are the existing `Scheme.Hom.ker`; dual line bundles are
  `iₐ.ker.toModulesᵛ`. Canonical sections are the existing
  `supportedDivisorSection iₐ`, the transpose of the ideal inclusion.
* The first conclusion of `cartierPairTensor_geometry` is
  `k.ker.IsInvertible`. Its next two conclusions are the equality of ranges
  with their union and `k.openComplement = i₁.openComplement ⊓ i₂.openComplement`.
  The affine-ideal clause gives the product equation `Ideal.span {f₁ * f₂}`
  whenever the two ideals have equations f₁ and f₂.
* The witnesses `μ` and `e` are ideal multiplication and the dual framed
  isomorphism. The equation with `toModulesι` specifies μ as actual
  multiplication. The equation with `dualEvaluation` and `tensorμ` specifies
  e by the canonical pairing; it excludes an arbitrary line-bundle isomorphism.
  The last equation sends `supportedDivisorSection k` to the tensor of the
  two sections, with the inverse left unitor supplying O → O tensor O.
* `cartierPairFrameTorsor` is an adapter to `Modules.etaleIsoTorsor` of the
  existing dual ideal. It only supplies its canonical invertibility instances;
  it does not reconstruct or choose a torsor. `cartierPairFrameVal` is its
  existing ordinary-pullback frame map.
* `cartierPairTensor_frames` supplies τ₁ over W₁, τ₂ over W₂ and τZ over
  W₁ intersection W₂. Their three valuation equations specify exactly the
  pulled-back canonical sections. The family m is specified on every etale
  object by tensoring its frames and transporting by e inverse, using the
  monoidal structure of the existing ordinary pullback.
* Naturality, anti-diagonal invariance, equivariance in the first variable,
  and the universal property against every sheaf of sets identify this m with
  the binary contracted-product quotient. This is the binary version of the
  recorded `ContractedProductPresentation` quotient property; the source node
  explicitly allows the binary contracted product. The specified-section
  equation says m sends the two restricted sections to τZ. Equivariance in the
  other variable follows from the stated anti-diagonal invariance and first
  equivariance; it is not a new assumption.
* The last clause of `cartierPairTensor_frames`, for every injective resolution
  I of `T.gmSheaf`, is exactly the displayed alpha addition equation. Alpha is
  `-relativeTorsorEquiv ... (Quotient.mk _ ⟨P,τ⟩)`, the Ext-normalized class
  used by the existing `relative_torsor_cohomology` proof, rather than the raw
  relative lifting class.
* `cartierPairOpenInclusion` constructs the etale map from W to V.
  `cartierPairRestriction_square` states its actual restriction square.
  `cartierPairRestriction` applies the existing `relativeFiberMap` to identity
  on global sections and restriction on open sections. Its homology is rₐ.
  In the actual-cone coordinates its map is (x,y) → (x,y restricted to W),
  retaining the differential convention (dx,-res(x)-dy).
* `cartierPairTensor_extensions` supplies q₁ and q₂ on the actual sheaves
  `lowerStar iₐ (supportedIntegralConstant Dₐ)`. The equations with
  `supportedIntegralUnit` and uniqueness characterize the canonical supported
  constant restrictions, including nonreduced supports. The open-closed
  quotient makes the supported integral unit epi, so this characterization
  determines the map on the full sheaf, rather than merely on global one.
* Its β variables are precisely classes satisfying the existing
  `CartierPoleBoundarySpec`, which is the relative extension realization with
  the canonical complementary frame killed. Their first equation is
  βZ = q₁*β₁ + q₂*β₂ in derived Ext¹. The second is the same equality in
  `YonedaExtension.Classes`, with addition explicitly supplied by
  `c.classGroup` of every normalized `YonedaDerivedExtComparison` c. That
  comparison's `baer_sum` field identifies addition with the geometric Baer
  construction and its naturality field identifies precomposition with
  extension pullback. `cartierPairYonedaClass` uses the inverse of that
  comparison on -β: the recorded positive-projection Yoneda convention sends
  a short extension to minus Mathlib's `extClass`. This prevents a silent sign
  change when naming the actual extension's Yoneda class.
* `cartierPairTensor_naturality` quantifies over all W ≤ V, every complex map
  and every integer degree. Its first square gives coefficient naturality,
  in particular for every augmentation-preserving lift of a coefficient map.
  Its second gives the square with `relativeConnecting` in every split
  horseshoe model. Every short exact coefficient sequence has such a model
  by the recorded injective horseshoe theorem, so no coefficient sequence
  or connecting homomorphism is excluded.
* No smoothness, reducedness, distinctness, proper intersection, nonemptiness,
  coefficient torsion, or invertibility-of-exponent hypotheses occur.

Dependency declarations used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, through opens.
* `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `IdealSheafData.IsInvertible.isInvertible_dual_toModules`, `Modules.dual`,
  `IdealSheafData.toModules`; the invertible-ideal predicate comes from its
  recorded `IdealSheaf.Invertible` import.
* `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`: the recorded
  `nonempty_equiv_quotient_torsor` and the concrete `Modules.etaleIsoTorsor`,
  `etaleIsoTorsorVal` it imports. The latter are used to retain actual frames.
* `WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation`:
  `Sheaf.Torsor.ContractedProductPresentation`, whose sheaf quotient universal
  property is rendered for the binary torsor product.
* `Sheaf.CategoryTheory.Sites.TorsorWithSection`:
  `Sheaf.Torsor.WithSection` and `WithSection.Classes`, via the classifier.
* `Sheaf.AlgebraicGeometry.RelativeEtaleCohomology`:
  `relativeSections`, `relativeSectionRestriction`, `relativeSectionComplex`,
  `relativeCohomology`, `relativeFiberMap`.
* `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`:
  `relative_torsor_cohomology`, `relativeSectionMap`, `relativeConnecting`.
* `Sheaf.CategoryTheory.Sites.RelativeTorsorExtension`:
  `Sheaf.Torsor.relative_extension_existsUnique`.
* `Sheaf.AlgebraicGeometry.RelativeCocycleCoordinates`: `relativeTorsorEquiv`.
* `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`:
  `supportedDivisorSection`, `supportedDivisorSectionPullback`,
  `supportedIntegralConstant`, `supportedIntegralUnit`.
* `Sheaf.AlgebraicGeometry.CartierPoleBoundary`: `CartierPoleBoundarySpec`.
* `Sheaf.CategoryTheory.YonedaDerivedExtComparison`:
  `YonedaDerivedExtComparison`, its `comparison`, `classGroup`, `baer_sum`,
  `shortExact_class` and `naturality` interfaces.

The supported-boundary and relative-class owners were added to stmt_deps because
their already landed canonical definitions are used directly. The Yoneda comparison
structure now has the definition-node owner described below. No dependency module
is changed.
Every recorded proof dependency with a module is imported, including the
normalization, relative class naturality, open-closed exact sequence, open
adjunction, Yoneda/Baer interfaces, pushout exactness, horseshoe resolutions,
injective-resolution lift and enough-injectives/naturality Mathlib modules.
No import cycle was encountered.

Edge cases checked mathematically before writing: the empty scheme; the empty
divisor (unit ideal); either or both complementary opens empty; disconnected
opens; equal divisors (the product ideal records multiplicity); intersecting
Cartier divisors; nilpotents in T. Products of nonzerodivisors remain regular in
every commutative ring. No division by a local equation in T is required.
All degrees n in Z occur in naturality. Scheme universe u and coefficient
universe u+1 follow the supplied small-etale interfaces.

Searches made:

* msearch leanfinder, “Cartier divisor tensor product line bundle relative
  torsor cohomology”: eight hits, including `ModuleCat.tilde`,
  `CommRing.Pic.mk_tensor`, `CommRing.Pic.mul_eq_tensor`; no framed relative
  torsor or supported extension result.
* msearch loogle, `"IsInvertible", "mul"`: zero hits.
* msearch grep, `Cartier.*tensor|relativeTorsor` in AlgebraicGeometry: zero
  Mathlib hits. Earlier `Cartier|frameTorsor|relativeFrameClass` likewise did
  not supply this theorem.
* msearch leansearch, “The relative cohomology class of a contracted product
  of torsors with sections is the sum of their classes”: eight hits on
  hom-complex cocycle addition and resolution equivalences; none is this
  framed Cartier assertion.
* rg in Mathlib, WeilConjectures and Sheaf for CartierPair, frameTorsor,
  divisorSection, relativeFrameClass, CartierPoleBoundarySpec and supported
  constants found the canonical interfaces cited above. The existing
  `classH1_etaleIsoTorsor_tensorObj` states ordinary unframed H¹ additivity;
  it omits the relative sections, support maps and extension assertion.
* grep of the item's blueprint id in WeilConjectures found no existing
  declaration. rg of every new declaration name across all three source
  trees found no collision.

Sources read: Stacks divisors.tex definitions and lemmas for sums of effective
Cartier divisors (01WT/01WU); sites-cohomology.tex lemma-torsors-h1 (03AJ),
including its free extension construction; cohomology.tex
remark-support-functorial (0G78); the current blueprint divisor-class proof
clause (b); recorded Lean source signatures/docstrings and the normalization
and Yoneda-comparison conventions. The accepted DAG proof is reproduced by
steps in the five theorem docstrings.

Validation: scompile.py compiled both sandbox and library module cleanly after
repairing public visibility of the raw relative classifier and supplying the
Yoneda class group's explicit Add instance when forgetting its additive
comparison to an equivalence. No proof was filled. All variables and universes
are bound, and all lines have at most 100 characters.

## New nodes

`def-pur-yoneda-derived-ext-comparison-data` owns the unchanged existing
`CategoryTheory.YonedaDerivedExtComparison` in
`Sheaf.CategoryTheory.YonedaDerivedExtComparison`, with `existing: true`.
It defines the type of normalized additive comparison data, without asserting
inhabitation. Its source is the positive-projection class preceding Stacks 06XU,
06XV, splice composition and the geometric Baer operation in Homology 010I.
The definition reuses `def-coef-yoneda-extension-data`, `def-pc-ext`,
`def-sp-abelian` and `def-sp-injective-resolutions`; no structure or module is
moved, copied or changed. The existing signature is recorded verbatim.

Each field is accounted for: `classGroup` supplies the class group in every
positive degree; `comparison` is its additive equivalence to derived Ext;
`shortExact_class` fixes the negative Mathlib connecting-class convention;
`splice_class` fixes the signed recursive splice formula; `naturality` states
the equation for arbitrary endpoint maps; `baer_sum` and `baer_exists` specify
the actual geometric addition and its existence; `split_iff` gives precisely
the degree-one zero criterion; `injective_vanishing` covers every injective
second argument. Arbitrary object, morphism and Ext universes remain explicit.
The cases n=0, split extensions, zero endpoints and injective coefficients are
included; enough injectives is not an extra hypothesis.

Searches run for this repair: msearch LeanSearch,
“A normalized natural additive comparison between Yoneda extension classes and
derived Ext with Baer sum and short exact sequence normalization” (eight hits
on Ext and extClass); msearch LeanFinder, “Yoneda extension classes additive
equivalence derived Ext Baer sum normalized comparison” (eight hits on derived
Hom/Ext and resolution equivalences); msearch grep,
`YonedaDerivedExtComparison|Yoneda.*[Cc]omparison|[Cc]omparison.*Yoneda`
(four unrelated representable-Yoneda comparison hits). Exact logged results
are in the new node. Direct rg of WeilConjectures and Sheaf finds the existing
structure in the unchanged published module; searching definition-node Lean
records finds no owner of that structure. `blueprint_refs.py search` with
`Yoneda.*comparison|comparison.*Yoneda|Baer` found zero blueprint nodes;
`ancestor` identifies `lem-pur-divisor-class`.

## Returned delivery repair

The return on immutable head `4f53d047f14f` identified one H2 fault: the plain
comparison structure was being cited through its existence theorem node.
The saved packet's initial dry run passed at `44649d56a95`, but this did not
resolve that content fault. The item's stmt_deps now cites
`def-pur-yoneda-derived-ext-comparison-data` in place of
`lem-coef-yoneda-derived-ext-comparison`. The latter remains in proof_deps
verbatim and its module remains imported. `cartierPairYonedaClass` and the
quantified comparison `c` in `cartierPairTensor_extensions` therefore depend
on a definition node. `nonempty_yonedaDerivedExtComparison` is reserved for
the eventual proof. The accepted relative-torsor classifier dependency remains
as reviewed: `relativeTorsorEquiv` is constructed from that theorem's proofs.
The module and all its signatures are unchanged from the returned packet.
No mathematical statement correction is involved.

Repair validation: scompile.py compiled the unchanged item as both sandbox and
library module with no diagnostics (43.7 s and 30.6 s). The new existing-node
signature matches the published structure verbatim. Compared with current main,
the item differs only in lean and added stmt_deps; statement, proof and proof_deps
are unchanged. Compared with the returned packet, only the comparison ownership
and delivery date change. The dry run additionally checks the existing structure
by a server-side #check, without modifying its module.

## Second reading by Q96

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
