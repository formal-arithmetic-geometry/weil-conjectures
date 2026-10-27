## Worker report

This delivery states `AlgebraicGeometry.AlgebraicSpace.spaceAffinePerfectHomBaseChange`
in `Sheaf.AlgebraicGeometry.SpaceAffinePerfectHomBaseChange`. Its proof is `sorry`.
The accepted stage-1 statement, source, proof and proof dependencies are preserved.
The inherited stage-1 superseded-dispatch message does not apply to this stage-2
assignment (brief-stage2 §0). The live item had no Lean record.

The canonical comparison needs an algebraic-space global-Hom interface, supplied by
one definition node described below. Every definition has actual data. Choices select
unique normalized comparisons, rather than a bare existence of an isomorphism. The
supporting proof obligations are named theorems with source and proof docstrings,
and are included in that definition node's statement and declaration list.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes and algebraic spaces with the small étale structure sheaf | `S : Scheme.{u}`, `X X' : AlgebraicSpace S`; `SmallModules` is the already published equivalent small affine model of the same module topos. |
| Module sheaves and unbounded derived categories | Existing `ringedSiteModules`, `DerivedModules`, `DerivedCategory` and explicit `HasDerivedCategory.{w}` binders; no truncation or bounded subcategory. |
| Size convention | Explicit `universe u w`; the small-model site has object and Hom universe `u`, coefficients remain in `u`, and localization uses `w`. No equality between `u` and `w` is imposed. The all-space instance family is the common localization convention used by the existing pullback comparisons. |
| Quasi-coherent cohomology | `P Q : X.DerivedQCoh`, the full subcategory given by `derivedQCohProperty`, which tests each cohomology module via the existing basis equivalence and `IsQuasicoherent`. |
| Perfect P, locally bounded summands of finite free modules | `hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w} X.smallStructureSheaf P.obj`, the existing local perfect-complex predicate. No global strictly perfect presentation is assumed. |
| Derived pushforward is K-injective; pullback is K-flat tensor pullback | Existing `derivedDirectImage` and `spaceDerivedPullback` (an abbreviation for the published `derivedTensorPullback`), with their fixed units/counits. The existing tensor comparison is normalized on flat-term K-flat representatives and ordinary scalar-insertion tensors. |
| Global Hom equals RΓ of internal RHom | `spaceGlobalHom Y e f := X.derivedHom ⋙ spaceAffineDerivedSections Y e f`. The latter is the actual right derived functor of A-valued sections. |
| A-action by restriction of scalars | `spaceAffineSections` uses the original direct-image sections at the identity chart of Y, then `ModuleCat.restrictScalars` along the actual `ΓSpecIso`/`e.hom.appTop` map. |
| H^j is Hom(P,Q[j]) | `spaceGlobalHom_cohomology`, with the class-of-cocycle proof description, states the additive equivalence for every integer `j`. No cohomology-only replacement of the main derived assertion is made. |
| Commutative rings A→B and their spectra | `A B : Type u` with `CommRing`; `e : Y.left ≅ Spec (.of A)` and `e' : Y'.left ≅ Spec (.of B)`; `g : Y' ⟶ Y`. The homomorphism is `spaceAffineRingMap e e' g`, using the canonical affine section identifications. This parametrizes exactly arbitrary homomorphisms A→B: take the spectrum morphism and identity affine identifications. Allowing named isomorphic affine representatives changes no hypothesis. |
| Flat f tested on étale charts | `hflat : MapIsFlat f`, the recorded étale scheme-chart flatness predicate. |
| X quasi-compact | `hqc : CompactSpace (Point X.obj.obj)`, using the existing point space and atlas topology. |
| X quasi-separated | `hqs` says the fibre product of any two affine scheme tests mapping to X has quasi-compact point space. This is the affine-test definition of quasi-compactness of the absolute diagonal; maps need not be étale, and there is no separatedness assumption. |
| X'=X×Y Y', with h and f' | `hp : IsPullback h.hom f'.hom f.hom ((Scheme.fppfTopology.over S).yoneda.map g)`. The algebraic-space category is full in these sheaves, so this is exactly its cartesian square. Any chosen presentation is allowed. |
| Canonical c is an isomorphism in D(B) | The first conjunct is `IsIso` of the actual component of `spaceAffineHomBaseChangeNat`, whose source is `moduleDerivedExtension` of `spaceGlobalHom` and target is the global Hom of the two actual derived pullbacks. |
| Natural in both arguments | `spaceAffineHomBaseChangeNat` is a natural transformation on `X.DerivedModulesᵒᵖ × X.DerivedModules`; its naturality proof obligation is `spaceAffineHomBaseChange_naturality`. Restricting the components to perfect P and quasi-coherent Q gives precisely the required naturality. |
| B-linear extension of A-linear pullback | `spaceAffineHomBaseChange` is literally the inverse Hom equivalence of the existing derived scalar extension/restriction adjunction, applied to `spaceGlobalHomPullback`. |
| Pullback-induced A-linear map | `spaceGlobalHomPullback` applies sections to the geometric h-unit, the normalized derived sections/direct-image composition, and then the internal-Hom comparison. `spaceInternalHomPullback` is defined by transposing the pulled evaluation using the existing representative-normalized tensor comparison. |
| Scalar-unit normalization | The second conjunct is the equality `η ≫ Res.map c = spaceGlobalHomPullback`, with precisely those objects and the same scalar adjunction. |
| No boundedness or Noetherian assumption | There are no such binders, no Tor-dimension condition on A→B, no flatness of g, and no finite-presentation or properness hypothesis. Q is arbitrary in unbounded D_QCoh. |

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its original étale site, structure sheaf and module category.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`; Mathlib `DerivedCategory` and `HasDerivedCategory` give unbounded categories.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the existing module quasi-coherence instances.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`: the recorded public interface for `derivedInternalHomOfUniverses`, used by the published space `derivedHom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`, `DerivedQCoh`, `derivedQCohProperty`, `derivedHom`, `derivedDualityModel`, `smallModuleDirectImage`, `derivedDirectImage`, and the K-injective-resolution instance.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback` and `spaceDerivedPullbackCounit`, which reuse `derivedTensorPullback` of `SpaceDerivedTensorPullback`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePullbackTensorComparison`: `SingleComplex.derivedTensorComparison`, with its ordinary pure-tensor and K-flat-counit normalization. No replacement pullback or tensor comparison is delivered.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`, `moduleDirectImageModel`, its chart projections, and `moduleTensorAdjunction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`: `representable_etale_scheme_tests`, making the identity affine chart étale.
- `Sheaf.AlgebraicGeometry.RingDerivedScalarExtension`: `moduleDerivedRestriction` and `moduleDerivedExtension`; the right-adjoint instance supplies their specified adjunction.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`: `IsPerfectOnRingedSiteOfUniverses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat`; `Point` and its topology come from the existing geometric definitions.

Published proof dependencies are plain imports: `AlgebraicSpacePseudoCoherentRHomQuasiCoherent`,
`SmallEnlargedEtaleModules`, `RingedPerfectInternalHomPullback`,
`WeilConjectures.AlgebraicGeometry.MixedExtensionSectionsUnit`,
`RingedToposDerivedPushforwardComposition`, and Mathlib `Adjunction.Mates` (the
`mathlib_match` of mate pasting). The other proof prerequisites currently lack a Lean
record; they are not used as unidentified objects in the statement. Their accepted
DAG proof and dependency edges are retained for stage 3.

Edge cases checked mathematically: empty X or empty affine schemes (zero rings), zero P
or Q, identity and nonflat base-ring change, non-Noetherian rings, unbounded Q in both
directions, negative cohomological degrees, and nonseparated but quasi-separated X.
Neither a global finite-free model for P nor an affine/representable-scheme hypothesis
on X appears. The cartesian presentation and affine identifications are bookkeeping
choices, not additional geometric restrictions. Flat f supplies Tor independence.
No statement is disputed and no statement correction is needed.

Searches: `msearch.py` LeanFinder for the full flat affine perfect-global-Hom assertion
returned eight scheme flatness/affine-space results, with no match. Loogle
`DerivedCategory, ModuleCat` returned zero matches. Mathlib grep
`affine.*perfect.*hom|perfect.*hom.*base` returned zero matches. For the supporting
notion, LeanSearch for canonical algebraic-space global-Hom pullback/scalar extension
returned eight ordinary presheaf or affine-scheme results; LeanFinder for canonical
algebraic-space tensor pullback/global-Hom comparison returned eight scheme/presheaf
results; Mathlib grep `globalHom|derivedPullback|tensorPullback` in AlgebraicGeometry
returned zero matches. The new node records the actual outputs of these three calls.
Project `rg` searches found and reused the recently landed space pullback and normalized
tensor comparison. `GlobalDerivedHom` and `AffineGlobalHomBaseChangeMap` upstream accept
schemes only. Searches for `spaceGlobalHom`, `spaceAffineSections`,
`SpaceDerivedAdjunctionNormalized` and `spaceAffineHomBaseChange` in both Lean trees
returned no hits. The item-id grep in `WeilConjectures` returned no hits.
`blueprint_refs.py search 'global Hom'` returned zero blueprint nodes. DAG searches
found the scheme-only comparison and the constituent space definitions, but no node
introducing this algebraic-space global-Hom arrow.

Validation: both modules compiled separately, in dependency order through `scompile.py`,
against the live library with no errors or warnings. All proof obligations are `sorry`;
no definition contains `sorry`. Delivery preflight and compilation are run by
`deliver2.py --no-push` before the final push.

## New nodes

`def-sfb-space-affine-hom-comparison` defines A-valued global sections and global derived
Hom on the existing equivalent small étale module model, the normalized ordinary and
derived sections/direct-image comparisons, the ordinary-unit-normalized derived
adjunction, the pulled-evaluation internal-Hom comparison, and the scalar-adjoint
natural global-Hom base-change map. Its source is the canonical-map construction and
first proof paragraph of Stacks 0E4S, together with 07A6, 08JA and 0D6E. The supporting
existence/uniqueness and naturality statements are explicitly included in its statement.
It is independent of perfectness and of the isomorphism assertion of the item, so it
does not introduce a cycle. The searches above distinguish it from the scheme-only
upstream global-Hom node. It reuses the landed space derived pullback, internal Hom,
normalized tensor comparison, module direct image, and derived scalar extension.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
