## Worker report

Q21 states `AlgebraicGeometry.ProEtale.CoordinateSectionNormalization.twistedCoordinateSectionNormalization`
in `Sheaf.Paper.TwistedCoordinateSectionNormalization`. Its only theorem proof is
`sorry`. All auxiliary definitions have real data: supported classes come from the
existing *unique normalized* Kummer family; comparison maps come from existing
adjunction units/counits, compact-support compositors, proper projection, and normalized
root maps. No arbitrary purity isomorphism, scalar, or inverse is selected.

The eight modules separate elaboration work so that each compilation uses the prescribed
60-second limit. Every module is owned by one DAG node. Seven new definition nodes name
the previously missing canonical composites and their explicit normalization predicates.
They introduce no mathematical premise to the main theorem.

Hypotheses and clauses, in the order of the item:

| Node text | Lean rendering |
| --- | --- |
| Finite field, ell distinct from characteristic, finite E/Qell, positive n and A | `P : WeilConjectures.PurityFiniteSetting.{u}`. `AffineLinePurity.Ring P` is the existing quotient at predecessor index `P.level - 1`; `AffineLinePurity.ringEquiv P` is the canonical reindexing to `P.Coefficient`. No ramification condition is imposed. |
| Separated finite-type k-base T | `T : Scheme.{u}`, `aT : T ⟶ Spec (.of P.field.k)`, `[LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]`. |
| X=A1_T, p, s, j, P1_T, q | Literal `AffineSpace PUnit.{u+1} T`, its structural projection, `sectionMap T`, `ProjectiveLine.affineChart T`, `ProjectiveLine T` and its projection. These are the same singleton-coordinate model used by the existing gamma. |
| D0, O(D0)=O(1) | `projectiveZero T = sectionMap T ≫ ProjectiveLine.affineChart T`; the conclusion supplies its closed-immersion instance and `ProjectiveNormalization` supplies the Cartier ideal and `Nonempty ((projectiveZero T).ker.toModules.dual ≅ ProjectiveSpace.twist (ULift (Fin 2)) T 1)`. |
| Every a>=1 killing A | `NormalizationAt` quantifies `b : ℕ` and `hA : ((ell^(b+1):ℕ):Ring P)=0`, with invertibility `hT` produced in the conclusion. This covers precisely all positive a. |
| L_U=mu_(ell^a) tensor A | Existing `Scheme.finiteEtaleTateLine`; all tensor constructions use its ordinary scalar-extended root sheaf. |
| Actual ordinary supported c_D0 and Chern h | `projectiveSupported` uses `ordinary_supported_kummer_uniqueBoundary`; `ProjectiveNormalization` asserts `supportedDerivedUnit ≫ projectiveSupported = projectiveLineTraceDatum.chern`. `ordinaryFiniteP1ChernPushforward` is its q-adjoint h. |
| I_p is restriction of trace by the open counit | Existing `CoordinateLine.integration`, defined by Rq* of `affineTraceOpenAdjunction.counit`, then `projectiveLineTrace`. |
| Identity-normalized Rp!s*A=A | `sectionComposition` is the actual compact-support comparison via the proper/closed comparison, the chosen affine-chart compactification, composition, ps=id, and the identity comparison. It is used in every ordinary equation, never replaced by an existential object isomorphism. |
| Forgetting support gives h; I_p Rp!c=t_q h=1 | The first three conjuncts of `OrdinaryNormalization`: the open-counit equation, the equality of the two traced arrows, and equality to identity. |
| Pro-etale c_s is the published Cartier map | `CartierRealization` compares the ordinary class at *every* annihilating exponent to `Etale.cartierKummerMap`. The source alpha is fixed by the supported constant unit; the target is the canonical `twistDerived` root-projection comparison. |
| u_s is its actual exceptional adjunct | `proOrientation` is comparison of `ordinaryOrientation` followed by the actual right-adjoint comparison-unit map `boundedSiteRho`. The untwisted adjunct is separately named `unitOrientation`. `CoprojectionNormalization` includes the coefficient-unit input as well as every Tate input, fixing the unit tensor presentation. |
| u_s iso and Rs!gamma composite is identity | `ProNormalization` produces the finite-Tor/boundedness witnesses, invertibility of the actual unit needed for the composition map, `IsIso proOrientation`, `IsIso gammaCoordinates`, and the displayed equality `proOrientation ≫ proClosed.map gammaCoordinates ≫ proComposition = 𝟙 _`. |
| Actual gamma, not a selected purity iso | `gammaCoordinates` uses `CoordinateLine.sourceCoordinates`, `AffineLinePurity.sourceComparison`, and the existing `affineLinePurityComparison`. Its retained representative is the literal comparison image of the ordinary Tate input. |
| Composition identification transports the ordinary one | `exceptionalComposition` is `conjugateIsoEquiv ((closedAdjunction).comp compactAdjunction) Adjunction.id sectionComposition.symm`; `proComposition` applies the specified comparison unit inverse and the actual comparison counit. No ambient pro-etale exceptional adjunction is assumed. |
| On the affine-line datum's domain, u_s=-pur_s | `P.CoordinateCartierSign T aT` quantifies the divisibility witness only here. `coordinateCartierAdjunct` is the same uniquely normalized positive Cartier class written directly in that datum's `ULift (Fin 1)` coordinate and `P.Coefficient` presentation. It equals `-pur`, where the published normalized support chart sends `pur` to its positive `coordinateBoundary`. |
| Signed cone and localization convention | Imported `PurityRelativeCone` and `PrincipalTorsorYonedaSign`; the sign predicate uses the *actual* `OrientationSupportData` boundary with its `boundary_normalized` and `support_spec` fields, not an unconstrained support chart. Its docstring specifies D(a,b)=(da,r(a)-db) and boundary (0,-b). |
| M_r=A_T(r)[2r], every r>=0 | Existing `Etale.SectionLocalDualizingComparisons.tateObject A N hA T r`, all `r : ℕ`. `IsTateInput` includes these and the literal unit, so no shift-zero edge case is discarded. |
| u_s,M is u_s tensor identity under canonical coprojection | `CoprojectionNormalization` gives the explicit equality of `ordinaryOrientation` with the unit-orientation tensor and `coprojectionMate`; this mate is *defined* by inverse proper projection and the actual closed counit. Its invertibility is concluded. The pro-etale arrow is the specified image of this entire ordinary arrow. |
| Supported adjoint is c_s tensor identity via proper projection | `closedProjection` is `ordinaryFiniteProjection`, inverse-image composition for ps=id and the right unitor. `tensorSupported` is its inverse followed by `1 ⊗ restrictedSupported`; `ordinaryOrientation` is exactly its adjunct. Coefficient-first ordering is the two-symmetry convention of gamma. |
| Target A_X(r+1)[2r+2] | Real construction `twistedTarget` uses `tatePullback`, `ordinaryFiniteShiftedLinePullback`, `derivedTensorShiftIso`, the degree-zero tensor comparison using flatness of the Tate line, the recorded root-normalized Tate product, and shift addition. |
| Twisted u_s,M iso and twisted identity | `OrdinaryNormalization` asserts isomorphy of each adjunct and its exceptional composite; `ProNormalization` asserts the same for every compared Tate input and the actual gamma. |
| Transpose is 1_M tensor I_p(c_s) | The penultimate clause of `OrdinaryNormalization` writes the literal equality between the normalized compact composite and `ordinaryFiniteTensor.obj M` of the untwisted integral, bracketed by right unitors. |
| Independence of a | `CartierRealization` compares every ordinary class to one fixed `cartierKummerMap` through the same source alpha and the root-normalized target. The normalization theorem quantifies over *all* a. No isomorphism or scalar is reselected with a. |
| No flatness of A over Z/ell^a or e divides n | Neither appears as a hypothesis. Flatness used by `twistedTarget` is solely the existing rank-one Tate sheaf flatness. The divisibility premise occurs only under the sign predicate for the old affine-line datum. |

Dependency declarations read and reused:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its actual
  finite coefficient quotient, constant sheaves and ordinary root twists.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.Proper`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`; Mathlib `AffineSpace` and its zero section.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`, `ProjectiveLine`,
  `ProjectiveLine.affineChart` and its compactification.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules` and its dual-ideal convention.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the specified finite Tate twists,
  realized here by `FiniteSiteCoordinates.twistDerived` and the existing root tensor sheaf.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`; its literal finite ordinary-origin functor
  is `ProEtale.sfFiniteExceptionalAt`, and closed equivalent coordinates are retained explicitly.
- `Mathlib.CategoryTheory.Adjunction.Basic` / `.Mates`:
  `Adjunction.comp`, `Adjunction.homEquiv`, `Adjunction.id`, `conjugateIsoEquiv`.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`:
  `ordinary_supported_kummer`, `ordinary_supported_kummer_uniqueBoundary`;
  `supportedExactDerivedMap`, `supportedDerivedUnit` and `SupportedKummerBoundary`.
- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`:
  `projectiveLineTrace`, `projectiveLineTraceDatum`, `projectiveLineTraceTransport`.
- `Sheaf.AlgebraicGeometry.CartierKummerMap`: `cartier_kummer_map`, `cartierKummerMap`.
- `Sheaf.Paper.AffineLinePurityComparison`: `affineLinePurityComparison`, `Ring`, `primeUnit`;
  `Sheaf.Paper.CoordinateLineAdjunctionMaps`: `right`, `rightCoordinates`, `sourceCoordinates`,
  `integration`, `adjunction`, `comparison` (the landed canonical API is reused).
- `Sheaf.Paper.VectorIntegrationSiteComparison` / `.FiniteSiteCoordinates`:
  `finiteTypeSiteComparison`, `comparison`, `sourceComparison`, `twistDerived`, `boundedSiteRho`.
- `Sheaf.Paper.PurityAffineLineDatum` / `.PurityAffineLineOrientation`:
  `coordinateKummer`, `OrientationSupportData`, `coordinateBoundary`, `gysinHomToSections`,
  `affineLine_orientation`; the sign is stated directly in these recorded coordinates.
- `WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection` and
  `Sheaf.Paper.PurityCoprojection`: the recorded closed coprojection and its counit-mate
  characterization. The generic finite-coefficient mate is constructed explicitly here,
  avoiding a new HasTateTwist or ramification hypothesis.
- `Sheaf.AlgebraicGeometry.PurityRelativeCone`: `relativeConeSupportComparison`;
  `Sheaf.AlgebraicGeometry.PrincipalTorsorYonedaSign`: `principal_torsor_yoneda_sign`.
- The proof imports retain line-zero geometry, ordinary/open/proper tensor comparisons,
  closed-section compact origin, closed finite counit transport, compact-support site
  coherence, and composition-projection mate as in the ten DAG proof steps.

Edge cases checked before the final statement: the empty base (all categories/identities
have their usual zero-object interpretation); nonreduced base (t is still a nonzerodivisor
in R[t]); positive level 1; ramified quotients whose level is not divisible by e;
annihilating exponents larger than necessary; r=0 and all positive r. The coefficient
universe is u+1 and the scheme universe u throughout. The only numerical equality used
for coefficient indexing is positivity, `(level-1)+1=level`.

Searches: prescribed `msearch.py leanfinder` with “supported Kummer class of the zero
section of the affine line integrates to one and exceptional adjunction purity with Tate
twists” returned eight unrelated Mathlib algebraic-geometry/elliptic-point hits. Loogle
`CategoryTheory.Adjunction.homEquiv, CategoryTheory.Adjunction.comp` returned generic
adjunction composition only. Mathlib grep `Kummer|kummer` in AlgebraicGeometry returned
no hits. The additional LeanSearch and exact-name Mathlib grep are recorded verbatim in
the new nodes' search metadata and `searches.jsonl`; no matching construction was found.
`rg` of the upstream project, `lean/Sheaf`, and DAG declarations found no coordinate-section
normalization declaration; it did find the landed CoordinateLine API, which is imported.
`blueprint_refs.py search 'coordinate section'` returned one unrelated symmetric-product
node. No missing component is replaced by a private copy.

No statement correction and no STATEMENT-DISPUTED flag. The already accepted DAG sign
correction is preserved. The item node is changed only in lean and permitted additions
to stmt_deps. No dependency record is repaired.

## New nodes

`def-pur-coordinate-section-ordinary-arrows` owns TwistedCoordinateSectionOrdinary:
the actual ordinary supported class, closed and compact adjunctions, identity-normalized
composition and its conjugate, proper projection, twisted supported adjunct and explicit
ordinary normalization proposition. Source: rank-one coordinate paragraphs, Steps 1--4,
6, 8--9. Existing CoordinateLine integration and comparison are reused.

`def-pur-coordinate-section-site-arrows` owns TwistedCoordinateSectionMaps:
the transported closed exceptional functor, actual comparison-unit cancellation and
counit composition, Tate input predicate, gamma source coordinates, transported adjunct
and literal pro-etale normalization proposition. Source: finite-site transport, Steps 5--6.

`def-pur-coordinate-section-cartier-sign` owns TwistedCoordinateSectionSign:
the same Cartier adjunct constructed in the orientation datum's literal coordinates,
with canonical ordinary/site/shift maps, and the precise negative-boundary predicate.
Source: DAG Step 7 and its signed relative-cone audit.

`def-pur-coordinate-section-coprojection-arrows` owns TwistedCoordinateSectionCoprojection:
closed tensor projection and its counit-defined exceptional mate, the tensor equality
with the unit orientation, and the actual root-normalized twisted-target comparison.
Source: even twists/shifts paragraph, Steps 8--9.

`def-pur-coordinate-section-projective-arrows` owns TwistedCoordinateSectionProjective:
projective zero inclusion, its ordinary supported class and the dual-ideal/O(1) plus
forgetting-support normalization predicate. Source: rank-one compactification, Steps 1--3.

`def-pur-coordinate-section-core-arrows` owns TwistedCoordinateSectionCore: the
untwisted supported map and the two canonical composition comparisons, separated from
the ordinary tensor equations to bound per-file elaboration. Source: Steps 1--3 and 6.

`def-pur-coordinate-section-cartier-realization` owns TwistedCoordinateSectionCartier:
the exact supported source comparison and exponent-universal equality to the one
published pro-etale Cartier map. Source: Steps 5 and 10.

For each new node, LeanSearch, LeanFinder/Loogle, Mathlib grep, upstream/project grep and
DAG/blueprint searches were made before recording it. The component notions exist and
are reused; these *composites and predicates* had no owning declaration or node. The
module split is needed to respect the per-file compiler limit. Every new node is reached
from the item and carries import_flags=[] with its own lean.file and declaration list.

## Second reading by Q21

(Written by the maintainer's reviewer, NT-cc second reader, 2026-10-25. The delivered
section was a self-audit by the worker, which is H11. This section replaces it. The worker
report above is kept verbatim.)

Read: the item node; every statement dependency it uses in Lean; the eight delivered
modules; the seven new definition nodes; the landed declarations they call
(`sfFiniteExceptionalAt`, `boundedSiteRho`, `CoordinateLine.integration` / `comparison` /
`exceptionalAdjunction`, `OrientationSupportData`, `affineLine_orientation`, `tateObject`,
`projectiveLineTraceDatum.chern_spec`, `unboundedEtaleLowerShriekId`).

### Clause by clause

| Node clause | Lean | Verdict |
| --- | --- | --- |
| Finite datum k, ℓ, E, n ≥ 1, A | `P : PurityFiniteSetting`; `Ring P` = level-1 quotient (the landed reindexing, as in def-pur-affine-line-purity-comparison) | ok, no e ∣ n |
| Separated finite-type k-base T | `aT` with `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` | ok, nothing stronger |
| X = A¹_T, s, j, P = P¹_T, q | `AffineSpace PUnit T`, `sectionMap = zeroSection`, `affineTraceLineCompactification` (ProjectiveLine.affineChart) | ok |
| D₀ and O(D₀) = O(1) | `projectiveZero = s ≫ affineChart`; `ProjectiveNormalization`: ideal invertible and `Nonempty (dual ideal ≅ twist 1)` | ok (iso of line bundles) |
| Every a ≥ 1 with ℓ^a A = 0 | `∀ b, ((ℓ^(b+1)) : Ring P) = 0 → …`, with `hT` concluded | ok, covers all a |
| c^e_{D₀}: forgetting support gives h | `supportedDerivedUnit ≫ projectiveSupported = (projectiveLineTraceDatum …).chern`; `chern_spec` is the Kummer class of O(1) | ok |
| Identity-normalized Rp_!s_*A ≅ A | `sectionComposition`: closed comparison, compactification iso, compositor, congruence along ps = id, identity comparison | ok, canonical |
| I_p ∘ Rp_!(c^e_s) = t_q h = 1 | `OrdinaryNormalization` conjuncts 1–3 (open-counit image = h; traces agree; = 𝟙). `CoordinateLine.integration` = Rq_*(open counit) ≫ t_q | ok; conjunct 1 is Step 3's aτ = h, implied by the display |
| c_{s,A} = lem-amb-cartier-kummer-map | `CartierRealization`: one α, pinned by the supported constant unit (an epimorphism, so α is unique), and at every b the transported ordinary arrow ≫ twistDerived equals α ≫ `cartierKummerMap` | ok; also gives independence of a |
| u_s = exceptional adjunct, an isomorphism; Rs^!γ composite = 1 | `ProNormalization` for M = unit: `IsIso proOrientation`, `IsIso gammaCoordinates`, `proOrientation ≫ proClosed.map γ ≫ proComposition = 𝟙` | ok |
| All arrows are transports of étale arrows; equality of derived morphisms | `proClosed` = C ∘ s^! ∘ Rν_* (same shape as `sfFiniteExceptionalAt`); `proOrientation` = C(ordinary adjunct) ≫ ρ; `proComposition` uses the ordinary conjugate compositor with the actual unit and counit | ok |
| Actual γ of def-pur-affine-line-purity-comparison | `gammaCoordinates` = source coordinates ≫ `sourceComparison` ≫ `affineLinePurityComparison` (Iso.refl witnesses) | ok |
| u_s = −pur_s on the affine-line datum's domain | `CoordinateCartierSign`: for every e ∣ n, `∃ D pur` with the same defining equation as `affineLine_orientation` (`D.support.hom (gysinHomToSections pur) = D.coordinateBoundary`), and `coordinateCartierAdjunct = -pur` | ok; same ∃ D form as the landed theorem; sign matches the accepted DAG correction |
| M_r = A_T(r)[2r], every r ≥ 0 | `tateObject A N hA T r`, all `r : ℕ`; unit kept separately in `IsTateInput` | ok |
| u_{s,M} = u_s ⊗ 1 under the canonical coprojection | `CoprojectionNormalization`: `ordinaryOrientation M = λ⁻¹ ≫ (M ◁ unitOrientation) ≫ coprojectionMate`. The mate is defined by inverse proper projection and the closed counit; its invertibility is a conclusion | ok. The recorded lem-pur-immersion-twist declaration is only `Nonempty`, so a canonical mate had to be built |
| Supported adjoint = s_*M ≅ s_*A ⊗ p^*M → (c ⊗ 1) | `ordinaryOrientation := homEquiv (tensorSupported)`, `tensorSupported = inv closedProjection ≫ (p^*M ◁ c)` | ok, definitional |
| Target A_X(r+1)[2r+2] | `twistedTarget`: right.obj M_r ≅ tateObject (r+1) through the root-normalized product and shift addition | ok (coordinates) |
| Twisted identity and transpose 1 ⊗ I_p(c) | Ordinary: last two conjuncts of `OrdinaryNormalization`. Pro-étale: `ProNormalization` for every M_r | ok |
| Independent of a; no flatness, no e ∣ n | the hypotheses contain neither; `CartierRealization` uses one Cartier arrow for all b | ok |

The quantifiers are in the node's order. `IsNoetherian T` and `IsClosedImmersion` of
the projective zero section are conclusions; the conjuncts under `∀ [IsNoetherian T]` are
therefore not vacuous. The universes are scheme `u` and coefficient `u+1` throughout.

### Edge cases
- The empty T: every category is zero, and all the equalities and isomorphisms hold.
- A non-reduced base: t is still a nonzerodivisor, so `hI` is a conclusion and not assumed.
- r = 0 against the literal unit: both are kept.
- a larger than needed: covered by `∀ b`.
- Ramified E with e ∤ n: no hypothesis excludes it, and the sign clause is restricted
  to e ∣ n, as the node says.

### Records and owners (H2/H12)
I checked every project declaration in the eight modules against the stmt_dep closure of
the node that owns its module. The fix repairs the new node records:

- core-arrows: `unboundedEtaleLowerShriekCompIso` (owner def-sf-etale-support-compositor)
  and `unboundedEtaleLowerShriekCongr` (def-pur-compact-support-morphism-congruence) were not
  cited; both are now cited. `unboundedEtaleLowerShriekId` has no definition owner. It is
  the identity comparison constructed by lem-amb-unbounded-compact-support-comparisons, so
  that node is cited (the landed precedent; no cycle).
- site-arrows and cartier-sign: `boundedSiteRho` is now cited through its existing:true
  owner def-pur-bounded-site-transpose-arrows. In site-arrows, lem-pur-vector-integration-site-comparison
  owned nothing used there and is replaced by def-pur-finite-site-coordinates (owner of
  `VectorIntegrationSite.comparison` and `twistDerived`). The `tateObject` owner,
  def-trf-section-local-comparison-data, is now cited.
- cartier-realization: lem-pur-vector-integration-site-comparison is replaced by
  def-pur-finite-site-coordinates. def-amb-cartier-kummer-data (`cartierConstantComparison`)
  and def-amb-proetale-supported-coefficient-reduction (`cartierSupported*`) are added.
- ordinary-arrows: six theorem stmt_deps owned no declaration of the module and are
  dropped (supported-kummer, cartier-kummer-map, vector-integration, affine-line-orientation,
  immersion-twist, divisor-relative-cone). def-trf-section-local-comparison-data is added.
- coprojection-arrows: lem-pur-immersion-twist and lem-pur-coprojection owned nothing used
  and are dropped. cartier-sign: lem-pur-divisor-relative-cone is dropped, and its
  convention is stated in words.

All added nodes are on the delivery base, and none has the item or a new node in its
closure. The item record itself changes only by `lean` and the new-node stmt_deps, and its
proof_deps are unchanged. Each `lean.statement` is verbatim in its file.

### Advisories (not faults)
- `compactAdjunction` has the same body (`Adjunction.ofIsLeftAdjoint`) as the landed
  `CoordinateLine.exceptionalAdjunction`.
- `proClosed` is the closed-adjunction form of `sfFiniteExceptionalAt`. It is canonically
  isomorphic to it through `rightDerivedLowerShriekIsoRightDerivedLowerStar`, and not a new
  notion.
- The theorem docstring's Step 4 summarises the node's Step 4 under one cited name
  (lem-pur-coordinate-line-adjunction). The mathematics is the same.
- The sign clause is stated in the orientation datum's own ULift (Fin 1) / P.Coefficient
  model, built from the same unique ordinary class and the same transport recipe.

### Compilation
No Lean file is changed by this second reading. The worker compiled the eight modules
separately, and the landing compiles them again.
