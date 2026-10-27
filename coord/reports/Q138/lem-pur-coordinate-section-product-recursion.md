## Worker report

This delivery states the identities of the actual ordered coordinate Cartier products and their exceptional adjuncts. It reuses `AffineZeroPurity.product`, `supportedClass` and `thom`; it does not introduce another orientation, change coefficients, assert relative supported Kunneth, or assume exceptional base change invertible.

The source read is blueprint main-20261015, `sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md`, the ordered Cartier-map iteration and arbitrary-base-change paragraphs (old Steps 5 and 7). The node's ten proof steps are retained verbatim. All theorem proofs are postponed; all definitions contain real constructions or choice from a uniquely specified canonical map.

The Lean clauses are distributed across the recorded declarations:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Algebraic closure of the finite field, ell different from characteristic, finite extension E and its valuation quotient | `P : PurityFiniteSetting.{u}`; the recorded coefficient datum and its instances |
| Every positive coefficient level | `n : Nat` and `setting P n`, whose level is `n+1`; this includes level one and every ramification degree |
| Separated finite-type base B | `aB : B ⟶ Spec (.of P.field.k)` with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` |
| Affine tower, projection, zero sections | Existing `iteratedAffineLine`, `lastProjection`, `zero`; `lastSection` is `zero (iteratedAffineLine B r) 1` |
| Ordered shifted Tate object W_r | Existing `target P n X r`, the tensor power of the compared shifted finite Tate line |
| Actual C_c and theta_c, canonical total-support identification | Existing `supportedClass` and `thom`; `compactProduct` recovers that same proper direct-image presentation by the inverse of the Hom bijection defining `thom` |
| Canonical proper projection and shifted target multiplication | `sectionProjectionRaw`, `sectionProjection`, `sectionProjection_isIso`, `sectionTargetIso` |
| Section arrow and its adjunct u_r | `sectionArrow`, uniquely fixed by its commuting square with the actual projection, and `sectionAdjunct`, using the existing exceptional Hom bijection |
| Same compact-support composition, conjugate d_r | `coordinateComposition`, `coordinateExceptionalComposition`, and its `IsIso` theorem; the latter uses the existing pasted-counit `compositionInverse` |
| C_0=1 and theta_0=1 | First two conjuncts of `coordinate_section_product_recursion`, using the canonical identity comparisons `coordinateIdentity` and `coordinateIdentityAdjunct` |
| Explicit supported recursion | Third conjunct of `coordinate_section_product_recursion`, with the same `coordinateComposition`, pushforward of `compactProduct`, and `sectionArrow` |
| Exceptional recursion | Last conjunct, `thom r` followed by the image of `sectionAdjunct` and the inverse conjugate compositor |
| Arbitrary g between the stated bases | `g : B' ⟶ B`, no flatness instance; both `aB` and `g ≫ aB` have the three base geometry instances |
| Canonical g_c and closed direct-image/Tate exchange | `coordinateMap`, `coordinateSquare`, `coordinateChosenSquare`, `coordinateSourcePullback`, and `targetPullbackIso` |
| Specified exceptional base-change mate | `coordinateExceptionalExchange` transposes inverse closed exchange followed by the actual pulled-back exceptional counit |
| Equality g_c^* C_c=C'_c and Ex! g^*theta=theta' | Both conjuncts of `coordinate_section_product_baseChange`, with explicit coefficient and target endpoint comparisons |
| Ordinary etale witnesses and exact site comparison | `ordinaryWitness` is the inverse of the existing bounded-target comparison Hom bijection, with specified endpoint isomorphisms. `ordinaryWitness_compare` records its normalization. `coordinate_section_product_ordinary` and `coordinate_section_product_ordinary_baseChange` state the same equations in every ordinary witness presentation. Cartier witnesses are the existing `ordinaryBoundary`; cup, projection, and adjunction comparisons identify the unique lifts of those constructions. Only bounded-target full faithfulness is used. |
| Independence of annihilating Kummer exponent | `boundaryAtExponent` uses the existing Cartier family at arbitrary `r,hA`, then the two normalized `twistDerived` comparisons to the common inverse-limit Tate line. `coordinate_section_product_exponent` says that factor is exactly the original `boundary`. Substituting these factor equalities in the existing recursive product and its fixed adjunctions leaves all products and displayed identities unchanged. |
| Coordinate permutation and sign (-1)^(2*2)=1 | `permutedClass` uses the existing `product` on the permuted `finRange`, with the unique total-support identification over the zero section. `coordinate_section_product_permutation` states equality of the actual arrows. `coordinate_section_product_ordinary_invariance` gives both invariances in every ordinary witness presentation. |

The ordinary equations quantify over bounded ordinary target presentations and their endpoint isomorphisms, rather than selecting an arbitrary ordinary model. The lift is the unique inverse image under the published comparison Hom bijection. All endpoints here have etale-origin presentations: constants, finite Tate tensor powers, proper closed direct images and the bounded exceptional targets. Thus these equations are not assertions about an empty class of witnesses. Their proof docstrings identify the actual ordinary Cartier, cup, projection and counit constructions with these unique lifts. This also avoids asserting full faithfulness on arbitrary unbounded objects.

The equality/HEq transports used to cache tensor endpoints specify the complete actual maps, not merely existence of an isomorphism. `oneTargetIso_existsUnique`, `sectionTargetIso_existsUnique` and `sectionArrow_existsUnique` determine their chosen data uniquely. The last uses the commuting square with the invertible, counit-defined proper projection, so determines precisely its inverse followed by Cartier orientation tensor identity and the normalized target map.

Dependency declarations read and reused:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, `WeilConjectures.sfQbarTwistingFunctor`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `def-weil-pbc-composite-adjunction`: `{'declaration': 'CategoryTheory.Adjunction.comp', 'file': 'Mathlib/CategoryTheory/Adjunction/Basic.lean', 'how': 'exact: Adjunction.comp adj₁ adj₂ : F ⋙ H ⊣ I ⋙ G (line 567), unit and counit by comp_unit_app / comp_counit_app (lines 575, 580), hom bijection by comp_homEquiv; identity clause CategoryTheory.Adjunction.id : 𝟭 C ⊣ 𝟭 C (line 475)'}`.
- `def-weil-pbc-adjunction-conjugate`: `{'declaration': 'CategoryTheory.conjugateEquiv', 'file': 'Mathlib/CategoryTheory/Adjunction/Mates.lean', 'how': 'exact: conjugateEquiv adj₁ adj₂ : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂) for adj₁ : L₁ ⊣ R₁, adj₂ : L₂ ⊣ R₂, with the component formula of the statement (conjugateEquiv_apply_app); composition clause conjugateEquiv_comp, identity clause conjugateEquiv_id, isomorphism clause conjugateIsoEquiv (and conjugateEquiv_of_iso / conjugateEquiv_iso)'}`.
- `def-sbc-affine-space`: `{'declaration': 'AlgebraicGeometry.AffineSpace', 'file': 'Mathlib/AlgebraicGeometry/AffineSpace.lean', 'line': 44, 'how': 'specializes in one line: take coordinate type ULift (Fin n). AffineSpace (line 44) is exactly the alternative base-change definition in Stacks 01M0/01LZ; over (line 66) is the first projection. SpecIso (line 228) and SpecIso_inv_over (line 255) give the polynomial spectrum and constants inclusion on affine bases; isPullback_map (line 325) applies to each affine-open inclusion to identify its restriction. The instance at line 442 (AlgebraicGeometry.AffineSpace.instIsIsoSchemeOverInferInstanceOverClassOfIsEmpty) makes the projection an isomorphism for an empty coordinate type, including ULift (Fin 0). No affineness assumption on S is required.'}`.
- `lem-amb-cartier-kummer-map`: `Sheaf.AlgebraicGeometry.CartierKummerMap`, `AlgebraicGeometry.Etale.cartier_kummer_map`.
- `def-pur-affine-space-coordinate-boundaries`: `Sheaf.Paper.AffineSpaceCoordinateBoundaries`, `AlgebraicGeometry.ProEtale.AffineZeroPurity.boundary`.
- `def-pur-supported-cup`: `Sheaf.Paper.SupportedCup`, `AlgebraicGeometry.ProEtale.supportedCup`.
- `def-pur-supported-class-operations`: `Sheaf.Paper.SupportedCupFunctoriality`, `WeilConjectures.PurityFiniteSetting.FunctorialCupH`.
- `def-pur-affine-space-thom-map`: `Sheaf.Paper.AffineSpaceThomMap`, `AlgebraicGeometry.ProEtale.AffineZeroPurity.thom`.
- `lem-weil-finite-compact-projection-formula`: `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`, `AlgebraicGeometry.Etale.isIso_finiteCompactProjection`.

Additional published interfaces used are `AffineSpacePurity.inverseImageComp`, `inverseImageId`, `actionPullbackIso`, `shiftedLinePullback`, `tower_geometry`, `tower_noetherian`, and `compositionInverse`; `originCompositionAmbient`, `originCompactSupportId`; the proper direct-image identification and proper derived base-change map; `bijective_comparisonUpperStar_mapDerivedCategory_map`; the normalized `VectorIntegrationSite.twistDerived`; and `DerivedCategory.braidedCategory'`, the named canonical Koszul braiding. Their signatures and constructions were inspected. The modules of all recorded proof dependencies are imported.

Edge cases checked: c=0 gives the empty intersection, literal base and canonical identity comparisons; r=0 gives the first affine-line section; Fin 0 has no factors and only its empty permutation; n=0 means coefficient level one, not the zero quotient. Empty and nonreduced bases are allowed: each coordinate remains a nonzerodivisor in its polynomial chart and coordinate quotients commute with arbitrary base change. The arbitrary base morphism can be nonflat. Nothing excludes ell=2; all signs used are even. All scheme and coefficient universes are explicitly bound, with coefficients in Type (u+1). No equality of unrelated site universes is introduced.

Searches run (the sandbox search log preserves actual tool responses):

- msearch.py `leanfinder` query `The ordered supported Cartier Kummer coordinate product on affine space has recursive exceptional adjunct and commutes with arbitrary base change`: 8 hits; AlgebraicGeometry.AffineSpace.map_appTop_coord; AlgebraicGeometry.AffineSpace.reindex; WeierstrassCurve.Affine.Point.map_map; AlgebraicGeometry.AffineSpace.reindex_appTop_coord; WeierstrassCurve.Affine.Point.map_some; AlgebraicGeometry.AffineSpace.map_toSpecMvPoly; AlgebraicGeometry.AffineSpace.homOverEquiv_apply; WeierstrassCurve.Affine.Point.map. No exact match.
- msearch.py `grep` query `coordinate.*recursion|supportedClass.*(succ|baseChange)|thom.*recursion`: 0 hits; none. No exact match.
- msearch.py `loogle` query `CategoryTheory.Adjunction.comp_homEquiv, CategoryTheory.conjugateEquiv`: 0 hits; none. No exact match.
- msearch.py `leansearch` query `canonical projection formula zero section affine space supported Cartier product exceptional adjunct recursion`: 8 hits; Bundle.zeroSection_proj; Bundle.zeroSection; Algebra.Extension.Cotangent.val_zero; AffineMap.pi_zero; AlgebraicGeometry.AffineSpace.toSpecMvPoly; AffineMap.pi_eq_zero; AffineMap.coe_zero; AffineMap.proj_pi. No exact match.

`rg` searched Mathlib, `lean/WeilConjectures` and `lean/Sheaf` for the item identifier and for coordinate recursion, supportedClass succession/base change and Thom recursion. The upstream isomorphism theorem for the coordinate product does not state these identities. DAG searches for the canonical section projection/adjunct/base-change data and `tools/blueprint_refs.py search 'coordinate section'` found no definition of these particular maps (the blueprint search returned one unrelated symmetric-product-surjectivity node). Existing finite-site coordinates, affine tensor coordinates, and composition-comparison nodes were inspected and reused where applicable rather than copied.

No statement correction or mathematical dispute is claimed.

## New nodes

- `def-pur-coordinate-section-projection` / `CoordinateSectionProjection.lean`: the counit-defined proper section projection, with the coefficient-unit and factorwise Tate pullback endpoints.
- `def-pur-coordinate-section-arrows` / `CoordinateSectionArrows.lean`: the uniquely normalized last-coordinate supported arrow, its exceptional adjunct, and the compact-support/composite-adjunction identifications and identity normalization.
- `def-pur-coordinate-zero-base-change` / `CoordinateZeroBaseChange.lean`: canonical affine zero squares, closed exchange on constants and etale-origin inputs, and its specified exceptional mate.

These are missing canonical maps needed to express the item, not replacements for its assertions. Their definitions use the recorded product, twists, projection and adjunction constructions.

- `def-pur-coordinate-product-presentations` / `CoordinateProductPresentations.lean`: the actual reordered coordinate product and arbitrary-exponent factor, normalized by the unique support and common Tate comparisons; both reuse the published product and Cartier family. The same source, DAG and logged Mathlib searches found no declaration supplying these particular presentations.

The new definition records include their normalization and domain properties, each named theorem has its source and proof docstring, and the item cites all four. The modules are kept separate so that their individual elaborations fit the prescribed 60-second per-file compile limit. The first combined statement presentation passed server confirmation at 59.3 seconds; the product-presentation definitions were subsequently separated to give a wider margin.

Validation: `scompile.py Q138 lem-pur-coordinate-section-product-recursion` compiled all five delivered modules individually, in dependency order, in both sandbox and library presentations, with no errors or unexpected warnings. Library times: projection 7.8 s, arrows 15.8 s, product presentations 37.9 s, base change 9.4 s, main statements 23.9 s. All are within the prescribed 60 s limit. The first delivery dry run passed all server compilation checks and found eight citation-format issues in new node records (grouped citations were not recognized as individual `[id]` citations). Each citation was separated into its own brackets; no statement or dependency content changed. The repeated `deliver2.py --no-push` passed both preflight and server compilation and printed OK.

## Returned delivery repair

Return L on immutable head f82c71bc4041 identified the duplicate
`AlgebraicGeometry.ProEtale.AffineZeroPurity.targetPullbackIso`.
Removed that definition from `CoordinateSectionProjection.lean` and from its
node's `lean.declarations`; the module now publicly imports
`Sheaf.Paper.AffineSpaceZeroSectionPurity` and every use resolves to its existing
`targetPullbackIso`. The existing signature has the same scheme universes,
coefficient level, arbitrary scheme morphism, structural map and tensor exponent.
Its construction is the same factorwise monoidal shifted-Tate pullback.
Also removed the redundant `coefficientPullbackIso`; its two uses now reuse
that module's `unitPullback`, the canonical pullback of the same coefficient unit.
No replacement comparison or renamed duplicate is introduced.

The existing module's definitions suffice; none of its purity conclusions is
used. The corollary's future proof import of the recursion module must remain
omitted under stages/2-statements.md §3(7), since it would close an import cycle.
This is an import-plan constraint, not a mathematical dependency on the corollary.

The required initial dry run of the retained packet was performed before editing.
It encountered 60-second timeouts in product presentations (private overlay) and
section arrows (server confirmation), rather than a name-clash diagnostic.
The duplicate repair is still required by the immutable-head return.

The retained packet's current-source dry run confirmed a timeout in
`CoordinateSectionArrows`. A scoped lower-heartbeat diagnostic localized the
expensive kernel conversion to `compactProduct`: its original body composed the
canonical `closedSingleIso` with `supportedClass`, crossing the two definitionally
equal degree-zero embedding presentations. The repaired body instead applies
`rightDerivedUpperShriekHomEquiv(...).symm` to the existing `thom`. This is exactly
the original composite by `thom`'s definition and the inverse law of that same
Hom bijection; it adds no axiom or postponed theorem and changes no signature or
mathematical construction. The definitions still reuse the existing product,
proper closed comparison and exceptional adjunction. Diagnostic probes remain
outside the delivered `lean/` directory.

Self-check of the retained repair: all five `lean.statement` records match the
module signatures verbatim, every source line is within 100 characters, and all
modules explicitly disable auto-implicit variables. Against the current local
DAG the item changes only `lean` and the four new-node additions to `stmt_deps`;
all other fields agree. Current server source for
`Sheaf.Paper.AffineSpaceZeroSectionPurity` was read through `scompile.py --source`
and matches the local declaration text (apart from a trailing blank line).

The remaining product-presentation conversion was repaired at sheaf level.
`coordinateRootComparison_existsUnique` fixes the degree-one comparison by HEq
with the published `twistComparison`; `coordinateRootDerived` realizes that
same map using the exact single-functor comparison and shift. The two realizations
are composed through their common inverse-limit Tate line.
`coordinateRealizeRootBoundary` applies this to the actual ordinary Cartier
family. `coordinateBoundaryRaw` retains its literal endpoints, and
`coordinateBoundaryType_eq` identifies those endpoints with the recorded
coordinate-boundary type. `boundaryAtExponent` transports the actual map along
this equality. Thus the construction contains real data and no unspecified map
choice. All helper names in the definition node were updated to match the file.

The repaired product module passed server confirmation in 58.0 seconds; the
sandbox presentation took 58.4 seconds. The complete packet is checked again by
the final dry run below. Diagnostic scratch files are outside `lean/` and are not
delivered. The item statement and proof remain unchanged.

Final repair validation (2026-10-23): the full five-module
`deliver2.py Q138 lem-pur-coordinate-section-product-recursion --no-push`
passed preflight and every per-file compile, printing
`OK (dry run): commit acba05a16eb passes the preflight and compiles; nothing pushed`.
The retained duplicate repair reuses the published declaration without renaming
or restating it. All module declaration lists and primary signature records were
checked against the final source, with auto-implicit variables disabled and no
source line over 100 characters.

## Returned delivery repair: zero-section composition

Return L on immutable head d0d19682387e identified that
`AffineZeroPurity.zero_succ` restated the existing
`CoordinateTowerNormalization.zero_successor`. The retained packet's required
initial dry run passed (`d660a7fb635`), but the independent return still required
this source repair. Removed the duplicate theorem and its declaration-list entry.
`CoordinateSectionArrows.lean` now publicly imports
`Sheaf.Paper.CoordinateTowerNormalizationInduction`; both
`coordinateComposition` and `coordinateExceptionalComposition` use
`CoordinateTowerNormalization.zero_successor B r` directly. The new definition
node cites its owning DAG node, and its Lean note records the reuse.

Read the existing theorem and its docstring from both the local source and the
current server source (`scompile.py --source`). Its only binders are
`(B : Scheme.{u}) (r : ℕ)`, exactly the removed theorem's binders; no field,
coefficient or finite-type hypothesis is hidden. The existing last section is
`AffineSpace.zeroSection PUnit.{u + 1} (iteratedAffineLine B r)`; the section used
here is `zero (iteratedAffineLine B r) 1`, the same morphism by the definitions
of `zero` and the ordered affine tower. Consequently both equality transports
have the original endpoints, including r=0 and an empty or nonreduced base.
No theorem alias or replacement proof is introduced. A read-only traversal of
the existing statement/proof dependencies found no path from the normalization
node to this item or its section-arrows node, so the added citation is acyclic.

The item statement, proof and all its mathematical clauses are retained.
Compilation and the final dry run below validate the existing theorem in both
actual consumers and the complete five-module packet.

Retained-packet retry (2026-10-23): the required first dry run exposed two
compactification inference errors at the equality transports. The imported
theorem's native last-section expression was inferred before the local endpoint
instances. Both congruence calls now specify their actual `f` and `g` morphisms
explicitly and still use `CoordinateTowerNormalization.zero_successor` directly.
This changes only elaboration, with no new theorem or altered signature.
`scompile.py` then compiled the projection and arrows modules in both sandbox
and library presentations with no errors or unexpected warnings.

The final self-check matched every primary `lean.statement` verbatim against
its source signature and checked every declaration-list entry, module header,
explicit autoImplicit setting and 100-character line limit. The item differs
from the read clone only in `lean` and the four added definition dependencies.
The current server source again confirms the exact existing `zero_successor`
binders and conclusion, including rank zero and arbitrary bases.

## Second reading by Q138

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
