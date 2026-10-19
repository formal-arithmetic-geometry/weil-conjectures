## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison` states
`AlgebraicGeometry.Scheme.sfProperOpenSheafComparison_isIso`, with its sole proof `sorry`.
All six supporting definitions have actual data. They specify the canonical map rather
than asking for an arbitrary isomorphism. No other DAG node is stated in this delivery.

Hypothesis and conclusion correspondence:

- A finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`, declared as an
  explicit section variable and included in every declaration that uses it.
- Schemes `V,W,T : Scheme.{u}` and the proper map are the theorem binders
  `(p : V ⟶ T) [IsProper p]`.
- The arbitrary open immersion is `(i : W ⟶ T) [IsOpenImmersion i]`. There is no
  `QuasiCompact i`, Noetherianity, or restriction on the open's image.
- The chosen fibre product is `pullback p i`; `k` is `pullback.fst p i`, `r` is
  `pullback.snd p i`. Its Cartesian-square witness is
  `(IsPullback.of_hasPullback p i).flip`. The first projection's open-immersion
  instance comes from base-change stability, without an added assumption.
- All module categories are the dependency's `proEtaleRingModules H
  (proEtaleConstantRing H A)`. These are `ringedSiteModules`, hence Mathlib
  `SheafOfModules`, over the underlying constant commutative ring sheaf.
  Schemes and rings have universe `u`; site objects have universe `u+1`, site
  morphisms universe `u`, modules and the canonical `ULift A` have universe `u+1`.
- `p_*` and `r_*` are the recorded `proEtaleConstantModuleDirectImage`, with
  the canonical scalar map from constant sections. The coordinate helper uses
  `sfIntrinsicDirectImageComparison`, uniquely normalized on scalar-unit sections.
- Open inverse images are the recorded `sfIntrinsicOpenRestriction i A` and
  `sfIntrinsicOpenRestriction k A`. They compute sectionwise restriction and are
  the right adjoints in the recorded extension-by-zero adjunctions.
- `i_!` and `k_!` are the recorded `sfIntrinsicExtensionByZero`.
- The first arrow in lambda is `sfProperOpenRestrictionIso`: the fixed-scalar
  helper applies `Functor.sheafPushforwardContinuousNatTrans` to the canonical
  `MorphismProperty.Over.pullbackMapComparison`. At `Q → W` this is evaluation
  on `Q ×_W U → Q ×_T V`, an isomorphism by the given Cartesian square.
  Its map on sheaf sections has the stated direction by contravariance.
  `sfIntrinsicTransportComp` and the canonical scalar-normalized direct-image
  comparisons give precisely the same map in intrinsic module coefficients.
- The second arrow in lambda is the inverse of `sfProperOpenUnitIso`, namely the
  recorded unit of `sfIntrinsicExtensionByZeroAdjunction k A` made invertible
  using the already stated `sfIntrinsicOpenUnit_isIso`.
  `sfProperOpenLambda` composes open restriction with direct image of this inverse.
- `sfProperOpenSheafComparison` is `whiskerRight lambda.inv i_!` followed by
  `whiskerLeft (k_! ⋙ p_*)` of the recorded open counit. Its component at `M`
  is exactly `i_!(lambda_M⁻¹) ≫ epsilon_i`. This is the node's gamma.
- The conclusion `IsIso (sfProperOpenSheafComparison ...)` concerns the whole
  natural transformation, equivalently every component is invertible. Naturality
  in every module map is part of the constructed natural transformation itself.
  No boundedness, constructibility or etale-origin subcategory occurs.

The node's proof list and proof-dependency list are empty. The theorem docstring
records the intended degree-zero support argument and explicitly requires verifying it
on the pro-etale site; it does not claim the etale analogue proves this stronger input.
All statements remain postponed. No statement correction or disputed statement is recorded.
The node is currently `unsplit` in the shared snapshot; this delivery preserves its status,
as required by the stage-2 field ownership rules.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, whose intrinsic module
  category and universe convention are retained (no derived objects are needed here).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  through the recorded `proEtaleConstantRing`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  through the dependency's `proEtaleRingModules` abbreviation.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`:
  `sfIntrinsicTransport`, `sfIntrinsicTransportIso`, `sfIntrinsicTransportComp`;
  it reexports the recorded ordinary operations and coefficient categories.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicModuleEquivalence`, `sfIntrinsicExtensionByZero`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`:
  `sfIntrinsicOpenRestriction`, `sfIntrinsicExtensionByZeroAdjunction`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicDirectImageComparison` and its uniqueness characterization.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit`: `sfIntrinsicOpenUnit_isIso`.

The last two existing, stated nodes `def-weil-proetale-inverse-image` and
`lem-exc-proetale-open-unit` are added to `stmt_deps` under brief-stage2 section 5's
permission to cite landed nodes. Their declarations are used, not repeated. The helper
maps belong to this node's own specified lambda and gamma and are listed in
`lean.declarations`; no independent notion or new node is introduced.

Edge cases checked: the zero ring is admitted (`CommRing`, not `Nontrivial`); the zero
module, empty open, empty schemes and identity open are not excluded. At an identity
open the unit/counit and section identification yield the usual identity normalization.
A non-quasi-compact open is allowed because none of the constructions requires its
quasi-compactness. There is no assumption that ordinary geometric stalks detect sheaves.
All universes and object variables are explicitly bound (`autoImplicit false`).

Sources opened: the node's current main-20261015 blueprint proof, Steps 3–4;
Stacks `more-etale.tex`, lemma-shriek-proper-and-open (Tag 0F7B), which is only the
etale derived analogue; `proetale.tex`, definition-extension-zero (09AE) and
lemma-open-immersion (09BN). The upstream weakly-etale base-change source was read
for the canonical section comparison. Its ordinary module imports overlap the finite
framework, so this module imports only the existing shared site-map construction,
through the recorded dependency closure, and specializes it in its own lambda helper.

Existing-declaration searches (performed with `msearch.py Q57` for this item):

- LeanFinder: "Proper direct image commutes with extension by zero along open
  immersions of schemes on proetale module sheaves". Eight hits, on structure-sheaf
  restrictions and adjunctions; no statement about all pro-etale module sheaves.
- Loogle: `IsProper, IsOpenImmersion, IsIso`. Zero hits; unknown identifier `IsProper`.
- Mathlib grep: `proper.*[Oo]pen|[Oo]pen.*proper`, subdirectory AlgebraicGeometry.
  Twenty-five displayed generic geometry hits; no proper/open module-sheaf comparison.
- LeanSearch: "Proper direct image commutes with extension by zero along an arbitrary
  open immersion on the small proetale site". Eight hits, open-immersion and structure
  sheaf results; no matching statement.
- `rg` on source `WeilConjectures/SixFunctors/ProEtale` and project `lean/Sheaf`,
  including searches for `properOpen|ProperOpen|proper_open`: the project
  `Sheaf.Paper.ProEtaleProperOpenComparison` only transports bounded-below etale-origin
  objects for a different compactification diagram. It is not this all-module-sheaves
  degree-zero theorem. `ProEtaleOpenSquareExchange` concerns pullback/shriek, not
  proper pushforward/shriek. The upstream weakly-etale base-change map supplies the
  open-restriction calculation only, not the proper-support conclusion.
- Exact item-id search in upstream `WeilConjectures` and helper-name searches in
  Mathlib, upstream sources, project sources and `dag/lean_names_upstream.json`:
  no existing declaration for this node, no name collisions.

Validation: `scompile.py Q57 lem-exc-proetale-proper-open-sheaf-comparison` compiled
this delivered module cleanly as both the sandbox module and final library module
(13.4 s and 8.7 s respectively). One elaboration correction made the naturality
lambda of `NatIso.ofComponents` explicit. No warnings remain.

## Second reading by Q57

I independently opened the node, its source blueprint proof, Stacks
`more-etale.tex` lines 2450–2615 (lemma-shriek-proper-and-open, 0F7B), and
`proetale.tex` lines 5040–5130 (definition-extension-zero, 09AE, and
lemma-open-immersion, 09BN). The blueprint Steps 3–4 concern the dual comparison;
this node explicitly extracts a degree-zero pro-etale obligation rather than
asserting that 0F7B already proves it. The Stacks open-functor definitions and
open-unit assertion have no quasi-compactness assumption. The following
quasi-compactness assumption in lemma-ses-associated-to-open belongs to that
different assertion and must not be imported here.

Object/hypothesis/conclusion inventory, matched against the Lean:

1. Finite commutative ring A: the explicit section variable `(A : Type u)
   `[CommRing A] [Finite A]` is used in the theorem and each helper. Verdict:
   exact, including the zero ring, without a field or nontriviality assumption.
2. Schemes V, W, T: `{V W T : Scheme.{u}}`. I read the Scheme node and
   Mathlib's `Scheme` definition, not a category of schemes over a fixed base.
   Verdict: exact; no base field, Noetherianity, or separatedness of T is assumed.
3. Proper p: `(p : V ⟶ T) [IsProper p]`. I checked the proper-morphism node
   and Mathlib's class extending separated, universally closed and locally
   finite type; universal closedness also supplies quasi-compactness.
   Verdict: the node's proper morphism, with no stronger hypothesis.
4. Arbitrary open immersion i: `(i : W ⟶ T) [IsOpenImmersion i]`, using the
   recorded Mathlib abbreviation. Verdict: exact; there is no `QuasiCompact i`.
5. U and its projections: the theorem specializes the helpers to
   `U = pullback p i`, `r = pullback.snd p i`, `k = pullback.fst p i`, and
   `(IsPullback.of_hasPullback p i).flip`. I checked the fibre-product node.
   Verdict: the chosen fibre product in the correct orientation; the required
   open-immersion instance on k follows by base change, rather than a binder.
6. Module sheaves on all four small sites with coefficients A_H:
   `proEtaleRingModules H (proEtaleConstantRing H A)`. I opened
   `ProEtaleDerivedCategory`, `ProEtaleOperations`, `ProEtaleInverseImage`, and
   `RingedSiteModules`. These unfold to Mathlib `SheafOfModules.{u+1}` over the
   underlying ring of the sheafification of the constant commutative-ring
   presheaf on `H.ProEt`. Verdict: the dependency's intrinsic constant-ring
   module category, not an etale, condensed, or constructible category.
7. Ordinary p_* and r_*: `proEtaleConstantModuleDirectImage p A` and its r
   version. In `ProEtaleInverseImage` this is `SheafOfModules.pushforward`
   along the actual base-change functor, with scalar action through the
   constant-section map. I also read `sfIntrinsicDirectImageComparison` and
   its `existsUnique` normalization. Verdict: the recorded direct images;
   the coordinate helper cannot substitute an arbitrary isomorphism.
8. Exact open inverse images i^*, k^*: `sfIntrinsicOpenRestriction i A` and
   its k version. I read their definitions and the fixed-scalar
   `openImmersionRestriction` in the shared 51-module framework, as directed
   by `coord/pefw-upstream-framework.md`. They restrict sections by composition
   with the open immersion, transported through the canonical coefficient
   realization. Verdict: the specified open restriction, with no additional
   exactness assumption or choice of coefficient identification.
9. Extension by zero i_!, k_!: `sfIntrinsicExtensionByZero`. I read the
   recorded definition, canonical realization equivalence, and fixed-scalar
   localization construction. Its data are Kan extension followed by
   sheafification and canonical realization. Verdict: the existing dependency
   construction; no private definition or hollow data are introduced.
10. First arrow of lambda: `sfProperOpenRestrictionIso`. I followed it through
    `sfProperOpenFixedRestrictionIso`, `sfIntrinsicTransportComp`, and the
    scalar-normalized direct-image comparisons. I opened
    `MorphismProperty.Over.pullbackMapComparison` and its Cartesian-square
    isomorphism lemma: its component is the universal map
    `Q ×_W U → Q ×_T V`. Mathlib's
    `sheafPushforwardContinuousNatTrans` applies the presheaf to its opposite,
    so the resulting section map goes from i^*p_* to r_*k^*, as required.
    Verdict: exactly the node's evaluation identification, including arrows.
11. Second arrow of lambda: `sfProperOpenUnitIso A k` has hom equal to the
    recorded unit of `sfIntrinsicExtensionByZeroAdjunction k A`.
    `sfProperOpenLambda` whisks its inverse with r_* after the first arrow.
    I opened `sfIntrinsicOpenUnit_isIso` and the transported adjunction.
    Verdict: r_* applied to the inverse open unit, in the specified order.
12. Gamma: `sfProperOpenSheafComparison` whisks `sfProperOpenLambda.inv`
    with i_! and then uses the counit of the recorded i-adjunction, at the
    functor `k_! ⋙ p_*`. Verdict: its component is precisely
    `i_!(lambda_M⁻¹) ≫ epsilon_(i,p_*k_!M)`, not an arbitrary comparison.
13. Invertibility for every M, naturally in M: the theorem asserts
    `IsIso (sfProperOpenSheafComparison ...)`. This is invertibility of the
    natural transformation on the entire module category, equivalently of
    every component. The explicitly constructed natural transformation
    supplies naturality. Verdict: every clause is present; no boundedness,
    injectivity, constructibility or etale-origin assumption occurs.

The functor composition convention is left-to-right, whereas the displayed
mathematical functors act right-to-left; the above checks take this into
account. All dependency nodes' recorded declarations were opened, including
the two added landed dependencies `def-weil-proetale-inverse-image` and
`lem-exc-proetale-open-unit`. Their inclusion is necessary for the normalized
ordinary direct image and invertible specified unit, respectively. No new
node or dependency repair module is delivered, and no `statement_change`
is present or needed. The only base-to-sandbox node changes are `lean` and
these two added statement dependencies.

Edge cases: the empty open and empty schemes are allowed by the binders and
base-change construction; the identity open is allowed and uses the same
unit/counit normalization. The zero ring and zero module are admitted, with
no `Nontrivial` or nonzero-section assumption. Non-quasi-compact opens are
included. There is no index set or degree n in this degree-zero statement,
so no nonemptiness or positive-degree restriction is hidden. All finite
characteristics are allowed. The site object universe is u+1, its morphism
universe is u, and modules and `ULift A` live in u+1, exactly as the recorded
size convention specifies. There is no imposed equality of the site object
and morphism universes. All variables and universes are explicitly bound;
the section variable A is retained because the comparison uses it.

Independent searches used different terms from the worker's:

- LeanFinder, via `msearch.py`: "Universally closed pushforward sheaves
  commutes with open extension zero pro etale". Eight hits: generic
  structure-sheaf pushforward and `SheafOfModules.pushforwardNatIso`; no
  proper/open invertibility assertion for all pro-etale module sheaves.
- Loogle, via `msearch.py`: `"openImmersionLowerShriek"`. No hits.
- LeanSearch, via `msearch.py`: "Proper pushforward and extension by zero
  commute on sheaves of modules". Eight hits on ordinary module pushforward
  and its section formulas; no matching theorem.
- `rg` on Mathlib, upstream `WeilConjectures`, the shared framework and
  `lean/Sheaf`: `proper.{0,45}(extension.?by.?zero|lower.?shriek)` and its
  reverse, as well as `properOpen|ProperOpen|proper_open`. I opened the closest
  `properOpenProEtaleIsoPlus` and `properOpenProEtaleIso` declarations: they
  require a bounded-below etale-origin object and concern a different
  compactification diagram. The upstream weakly-etale base-change module
  supplies the section-identification construction, not proper/open
  invertibility. Its construction is already reused here through the
  recorded site comparison; importing that older ordinary-operation closure
  would overlap the finite framework. Exact helper-name and item-id searches
  in the upstream name index, Mathlib, upstream source and shared framework
  found no collision. Verdict: no existing declaration replaces this module.

H5/H6/H8/H9 checks: all six helpers have real data; the sole theorem has
exactly `by sorry`. The selected direct-image comparison is determined by
its unique section normalization, and the realization inverse is determined
up to its adjoint equality; neither chooses data from mere undetermined
existence. All seven declarations and the module carry source/blueprint
docstrings. The initial local node had an empty proof list; the final dry run
revealed a newer server node with a reviewed twelve-step proof. I retrieved
that node read-only, kept the statement unchanged, and replaced the old
support sketch with all twelve steps, including their dependency citations.
No proof has been supplied in Lean by this statement review.
There are no file-local aliases, private definitions, unbound variables,
or lines over 100 characters. The node's `lean.statement` was checked
programmatically to equal the theorem signature verbatim.

Mismatches and repairs: no mismatch in the theorem signature or the six map
constructions. The first dry run passed at `0d3223022f`, but reported newer
server proof metadata than the worker's snapshot. I read the complete current
node: its statement is identical and its twelve steps prove precisely this
map. I refreshed the sandbox node from that base, preserving only the
authorized `lean` record and added statement dependencies. This retains the
server's reviewed stage-1 split rather than delivering stale proof metadata.

The old docstring's informal claim about closed supports was replaced by the
actual node proof: (1) normalize lambda and gamma; (2) show the counit and
smaller-open inclusions monic using exact sheafification; (3) localize on
affine test objects; (4) cover a quasi-compact open complement by principal
opens and closed localization; (5) vanish source sections on that localization;
(6) lift specializations by proper closedness; (7) form a finite affine
localization cover of the proper source; (8) vanish target sections and glue,
also after every affine site base change; (9) choose finitely many local
representatives for an arbitrary-open section and a quasi-compact subopen;
(10) glue lifts to the smaller zero extension by monicity; (11) use the
quasi-compact case and the adjunction-normalized inclusion square; (12) prove
naturality, including inverses, by the unit/counit formulas. This includes
empty finite covers and the all-zero-representative case. It does not identify
vanishing of sections on the closed localization with vanishing of a sheaf.

I opened the available proof modules and added ordinary, non-public proof
imports for `ProEtaleWeaklyEtaleLocalization`, `FiniteOpenBaseChangeNormalized`,
`WContractibleClosedLocalization`, `AffineClosedSpecializationLocalization`,
`ProEtaleShriekSpecializationZero`, and the recorded Mathlib finite-type,
closed-immersion and module-sheafification modules. In particular the closed
localization cover is an unconditional conjunct of its theorem; only the
separate retraction assertion assumes w-contractibility. The arbitrary-ideal
localization theorem supplies exactly the specialization clause, and the
09AG theorem is for arbitrary abelian sheaves, with no etale-origin restriction.
The normalized open-base-change module supplies its underived isomorphism
before descending to derived categories. No new node or dependency module
is required for these proof imports, and no target statement is changed.

Initial revalidation with `scompile.py` compiled the sandbox module in 7.4
seconds and the library module in 9.1 seconds, without errors or warnings.
The final docstring and proof imports passed `scompile.py` in 4.7 seconds
(sandbox) and 5.0 seconds (library), with no errors or warnings.
