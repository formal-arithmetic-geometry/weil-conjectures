## Worker report

Module: `Sheaf.Paper.PuritySectionEtaleRestriction`.
Namespace: `WeilConjectures.PurityFiniteSetting.SectionRestriction`.
Main declaration: `coherence`. This delivery states the item without changing its
natural-language statement, split, or dependencies. All five theorem proofs are `sorry`.
All definitions have real data; each postponed proposition has this item's blueprint
identifier and a source/proof docstring. No additional DAG notion or dependency repair
is needed: the structures only bundle this item's geometric inputs and its squares.

Sources read: the current `literature/blueprint/latest/blueprint/sec-smooth-purity/`
orientation chart proof (`sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md`,
Steps 1--3), and `sk-prop-sp-composition/thm-pur-composition-coherence.proof.md`, Step 1;
the complete accepted eight-step node proof; the recorded dependency declarations and
source definitions, including the extended-Rees etale/base-change implementation.

The finite normalizing and DNC dependencies expose ordinary-etale coordinates and
fixed-scalar pro-etale section objects, whereas the later intrinsic coefficient interface
exposes the equivalent modules-over-the-constant-ring presentation. The delivery uses
the recorded `Dnc.sourceSection`/`sourceComparison` objects and maps, rather than creating
a copy of the intrinsic section invariant. `sourceSection` is literally the existing
`P.sectionInvariant`, namely the actual `Ls* Rg! Lambda` on the small pro-etale site.
`P.Coefficient = ULift P.Ring` is the published size lift of the same positive finite
coefficient quotient. Every statement uses this single coefficient ring. This is the
same finite realization used by the recorded normalization and DNC invariance theorems;
there is no independent exceptional adjoint, abstract invertible object, or chosen frame.
The intrinsic dependency modules are publicly imported unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed finite-field/coefficient conventions, arbitrary finite E, ell distinct from char k, n >= 1 | `P : PurityFiniteSetting.{u}`; its `field`, `coefficients`, `extension`, `finiteExtension`, `level`, `level_pos`; `P.Coefficient` is the standard size lift of `P.Ring = O_E/(varpi^n)` |
| Separated finite-type k-schemes | In all six law predicates: `aB : B ⟶ Spec (.of P.field.k)` with `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`; the same for every changed base. The source structure is `X.g ≫ aB`; separatedness and finite type follow by composition |
| Smooth pure dimension d >= 0, separated finite-type g | `d : ℕ`; `Pair.smooth : SmoothOfRelativeDimension d g`, `Pair.separated`, `Pair.quasiCompact`; smoothness supplies local finite type |
| Closed section s and g s = id | `Pair.closed : IsClosedImmersion s`, `Pair.section_eq : s ≫ g = 𝟙 B` |
| Etale separated finite-type a over B, with g' = g a | `EtaleMap.map`, `.etale`, `.separated`, `.quasiCompact`, `.over_eq : map ≫ X.g = X'.g`; etaleness supplies local finite type |
| a s' = s and Cartesian centres over id_B | `EtaleMap.section_eq` and `.centres : IsPullback X'.s (𝟙 B) map X.s` |
| Actual C(g,s) | `invariant P aB X := Dnc.sourceSection P d X.g aB X.s`; this unfolds to the published section invariant |
| Specified counit-normalized rho and conjugate compositor, not an arbitrary comparison | `restrictionEtale` uses `FiniteEtaleNormalization.congr` to insert the equality g' = a g and then `.sourceEtale`; the latter is definitionally `.comp` at the coefficient unit followed by `.rho` at omega_g. These are the published conjugates of the specified compact-support compositor and proper-support/sum comparison. The final factor is inverse `Etale.leftDerivedUpperStarComp` using `a.section_eq` |
| R_a is an isomorphism of actual pro-etale section objects | `restriction` is typed as `invariant P aB X' ≅ invariant P aB X` and conjugates that formula by the actual `Dnc.sourceComparison` and the functor `comparisonUpperStar.mapDerivedCategory` |
| R_ab = R_a R_b and R_id = id, canonical constraints | `Composition`: `restriction (b.comp a) = restriction b ≪≫ restriction a` and `restriction (EtaleMap.id X) = Iso.refl _`; `EtaleMap.comp` actually pastes the centre squares |
| Arbitrary base change B_0 -> B, not assumed flat | `BaseChange` retains the actual Cartesian square and section equation; `BaseCompatibility` quantifies all b with only the k-linearity equation `b ≫ aB = aB₀`; `baseComparison` is the published canonical smooth adjunction-mate comparison transported through nu* |
| Induced normal-bundle map n | `normalPair` uses the actual associated-graded cone, `Scheme.Hom.normalConeProj`, and its zero section; `normalMap` takes the existing Rees theorem's map characterized by its composite through the closed zero-fibre inclusion; that composite determines it uniquely |
| n is an isomorphism, not an independent linear frame | `geometry` states `IsIso (normalMap ...)`, its projection and zero-section equations, and its equality through the actual zero-fibre inclusion; the construction is the source's quotient-by-t / conormal-class map |
| Canonical DNC map fixes t and sends f/t to a*(f)/t | `deformationMap` is exactly `SectionReesBaseChange.pairMap` on the specified centre square. Its definition calls the existing coefficientwise `Scheme.IdealSheafData.deformationSpaceMap`, so the affine generator formulas are retained as real data |
| DNC map is etale and preserves augmented sections | `geometry` states `Etale`, separatedness, quasi-compactness, its projection and augmentation identities and Cartesian augmentation centre square; `familyMap` uses precisely those facts |
| Family object F and same comparison over A1_B | `familyPair` is the actual extended-Rees deformation projection with augmentation. `familyRestriction` is exactly `restriction` on `familyMap`, over `(AffineSpace ... B ↘ B) ≫ aB` |
| Restrictions at 1 and 0 are R_a and R_n under canonical fibre comparisons | `endpointOne` and `endpointZero` use the recorded `Dnc.fibreOne`/`fibreZero`, their nu* comparison, and canonical pullback comparison. The first two conjuncts of `Endpoints` are exactly the two commuting endpoint squares |
| R_n delta' = delta R_a for the unique normalized deformation maps | `delta` is chosen from the already-recorded `existsUnique_dncInvariance`, with its uniqueness characterization retained. `Endpoints`' third conjunct is `delta X' ≪≫ restriction (normalEtaleMap a) = restriction a ≪≫ delta X` |
| Composition of family and endpoint restrictions | `Composition` also states actual Rees/normal map composition, family restriction composition, and normal restriction composition; the general identity law also applies to family and normal pairs |
| Compatibility with base restriction of the family and endpoints | `reesBaseMap` is the actual coefficientwise base-change map; `reesBaseGeometry` retains its Cartesian square and augmentation/one-fibre equations. `normalBaseMap` is the unique lift through the zero-fibre pullback; `normalBaseGeometry` retains its Cartesian square and zero-section equation. `NormalizedBase` spells out both endpoint base-change squares, inserting the actual `endpointPull` constraints, and the delta base-change square |
| Compatibility of base restriction and etale restriction | The remaining `BaseCompatibility` conjuncts state the commuting Rees and normal squares for every such tower; its first conjunct is the section restriction/base-change square |
| Successive and identity base restriction, and further opens | `BasePasting` states the identity and composite base-comparison equations. These laws quantify all section pairs, so apply also to their family/normal pairs and after every further allowed base restriction. Open immersions are the open-neighbourhood case of `EtaleMap`; no separate open-orientation choice is supplied |
| Rank-zero standard pair with identity comparisons | `standardZero B` is the identity pair, canonically A^0_B. `standardZeroGeometry` states that its actual Rees and normal projections are isomorphisms. `standardZeroNormalMap` is the canonical projection to the identity pair; `RankZero` states that delta followed by its normalized restriction is `Iso.refl`. `Composition` supplies identity restrictions also for this pair and its family |
| No Tate orientation / identification with a coefficient line | No twist, orientation, basis, arbitrary endpoint isomorphism, or coefficient-line identification occurs in any input or construction |

Dependency declarations used (module and names):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, `.noetherian`, and its actual field/coefficient data.
- `Sheaf.Paper.PurityDncFamilyIntrinsic`: the existing actual DNC construction and
  intrinsic family interface, imported unchanged. The fixed-scalar realization used
  by the DNC geometry/invariance interface is computed on the same constructed scheme.
- `Sheaf.Paper.PurityNormalProjection`: `Scheme.Hom.purityNormalProjection` and its
  equality with `normalConeProj`; the latter is the projection used by the recorded
  `normalConeData`, actual zero section, and normal-pair construction.
- `Sheaf.Paper.PuritySectionInvariantIntrinsic`: the recorded intrinsic section
  invariant interface, imported unchanged; the recorded `Dnc.sourceSection` uses the
  equivalent fixed-scalar actual `PurityFiniteSetting.sectionInvariant` definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`,
  `SmoothOfRelativeDimension`, `SmoothOfRelativeDimension.smooth`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded intrinsic derived operations,
  imported unchanged. The recorded finite normalization/DNC coordinates use their
  canonical fixed-scalar model `Etale`/`ProEtale.upperStar.leftDerivedFunctor`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the existing finite
  exceptional realization (including `sfFiniteExceptionalAt` via its public imports),
  retained through the recorded finite normalizing/DNC comparisons.
- `def-weil-scheme-morphism-properties` is a convention record; the actual classes
  used are Mathlib's `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsClosedImmersion`, and `Limits.IsPullback`.
- `Sheaf.Paper.PurityDncComparisons`: `Dnc.sourceSection`, `sourceEtale`,
  `normalSection`, `normalEtale`, `familyEtale`, `sectionBaseChange`, `fibreOne`,
  `fibreZero`, `compactifiable`, `normalCompactifiable`, `normalQuasiCompact`,
  `invertibleExponent`.
- `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`:
  `ProEtale.FiniteEtaleNormalization.sourceEtale`, `.comp`, `.congr`, `.rho`, `.pull`.
- `Sheaf.Paper.StandingExceptionalComposition`: the specified standing compositor is
  retained by the public import; `FiniteEtaleNormalization.comp` is its published
  etale-coordinate conjugate of the same compact-support compositor.
- `Sheaf.Paper.PurityDncInvariance`: `Dnc.sourceComparison`, `normalComparison`,
  `pullComparison`, `existsUnique_dncInvariance`.
- `Sheaf.Paper.SectionReesBaseChangeEtale`: `SectionReesBaseChange.pairMap`, `.etale`;
  the genuine coefficientwise Rees map and the determined normal map, not a second
  deformation construction. This existing proof dependency is publicly imported
  because the current statement's canonical maps use its definitions.
- The upstream `WeilConjectures.AlgebraicGeometry.DeformationToNormalCone` definitions
  supply `deformationSpaceProj`, `deformationSpaceSection`, `normalConeProj`,
  `normalConeZeroSection`, `normalConeData`, both fibre maps and their pullback squares.
  Upstream finite-coefficient pullback-composition/identity/congruence maps supply
  every displayed constraint. All recorded, stated proof-dependency modules are
  also imported, with proof-only imports private.

The five named postponed theorems are `geometry`, `reesBaseGeometry`,
`normalBaseGeometry`, `standardZeroGeometry`, and `coherence`. The first four are
exact geometric/base/rank-zero clauses of this same node, split out only because the
canonical subsequent maps require their proofs. Their definitions' data do not depend
on a bare existence of an unspecified object: `deformationMap` and `reesBaseMap` are
real coefficientwise maps, `normalMap` uses a uniquely determined existing zero-fibre
map, and `normalBaseMap` is the actual pullback lift. `delta` is fixed by the existing
uniqueness theorem, not a choice of orientation.

Edge cases checked:

- Empty B: all pair objects and Cartesian squares remain meaningful; no nonemptiness,
  rank cancellation, chosen point, or nonzero-dimensional hypothesis is present.
- Rank d = 0: an explicit standard identity pair and canonical normal/family
  projections are included, with the deformation map equal to identity after their
  prescribed comparisons.
- Identity a and identity b: real identity pair maps and real identity base squares
  are constructed; their maps are compared with the canonical identity constraints.
- Nonflat b: only the k-structure equality is required, with no Flat or Smooth binder
  on b; Rees base-change and endpoint equations quantify over it explicitly.
- Arbitrarily ramified E and n = 1: no divisibility of n by the ramification index,
  chosen Kummer level, or field coefficient assumption was added.
- Scheme universe u is unchanged; the small-site coefficient modules are the
  published `ModuleCat.{u+1} P.Coefficient`; there is no extra universe equality.
- All statements use `autoImplicit false`; every universe and input is explicit.

Searches made before writing:

1. `msearch.py ... leanfinder` with query
   `Counit normalized etale restriction of smooth section dualizing invariants is
   coherent with composition base change and deformation to the normal cone endpoints`:
   eight unrelated Mathlib results, including normalizationDiagramMap,
   StandardEtalePair.homEquiv_symm_apply, etale standard smooth charts, and differential
   base change. None states the node.
2. `msearch.py ... loogle` with query
   `Etale.leftDerivedUpperStarComp, IsPullback, Scheme.Hom.deformationSpaceMap`:
   no hits; the external index does not know the project's Etale declaration.
3. `msearch.py ... grep 'sectionInvariant|deformationSpace' AlgebraicGeometry`:
   no Mathlib hits. Mathlib provides the geometric smooth/etale classes, not this
   six-functor coherence statement.
4. `rg` in `lean/WeilConjectures` for the exact node id: no existing declaration.
   Searches there and in `lean/Sheaf` for section/etale/restriction coherence found
   the existing section invariants, finite normalization, Rees functoriality and DNC
   comparison primitives used here, with no existing complete coherence theorem.
5. Source searches for `deformationSpaceMap`, `normalConeMap`, Rees etale base change,
   and `sectionInvariant` located the actual constructions cited above. The upstream
   Lean-name index has no declaration carrying this item or its complete statement.

Validation: the complete 716-line module compiled cleanly with the prescribed
`scompile.py`, in both sandbox and library module modes, within the fixed 60-second
limit (latest run: 13.3 s and 11.4 s). No warnings or errors. No global build, direct
repository edit, direct Git command, or launcher-tool modification was performed.
The required delivery dry run and final delivery follow this report preparation.

No STATEMENT-DISPUTED flag, statement correction, or independent new definition node.

Required dry run: `deliver2.py Q154 lem-pur-section-etale-restriction-coherence
--no-push` returned `OK (dry run): commit fd4cb58ee1d passes the preflight and compiles;
nothing pushed`. The staged packet contains only this report, the item's lean-only
node record, and its one statement module.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
