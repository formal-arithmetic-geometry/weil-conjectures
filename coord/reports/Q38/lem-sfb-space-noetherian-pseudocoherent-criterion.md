## Worker report

Delivered one theorem statement, with its entire proof `sorry`, in
`Sheaf.AlgebraicGeometry.SpaceNoetherianPseudoCoherentCriterion`:
`AlgebraicGeometry.AlgebraicSpace.isMPseudoCoherent_forall_iff_coherent_boundedAbove`.
No definitions, helper theorems, dependency repairs, or statement corrections are introduced.
The original statement and proof are preserved. Five existing landed definition nodes
are added to stmt_deps to name the interfaces the statement actually uses.

Hypotheses and clauses, matched individually:

- Size convention: explicit `universe u w`, `S : Scheme.{u}` and
  `[HasDerivedCategory.{w} Y.SmallModules]`. The localization universe is independent
  of the scheme/section universe; there is no new size equality or bound on K.
- Scheme base and algebraic space: `{S : Scheme.{u}} (Y : AlgebraicSpace S)`.
  There is no Noetherianity or separation hypothesis on S.
- The small etale structure sheaf and module category are the existing
  `Y.smallStructureRings` and `Y.SmallModules`, obtained from the actual structure
  sheaf by restriction to a small affine etale basis. The specified
  `Y.smallModuleEquivalence : Y.Modules ≌ Y.SmallModules` identifies its module
  category with the original topos without a coefficient lift or an arbitrary map.
- Unbounded K: `(K : Y.DerivedModules)`; no boundedness is imposed in a binder.
- Noetherianity is expanded into exactly its three stated components:
  `(hqc : CompactSpace (Point Y.obj.obj))`,
  `(hqs : Y.IsAbsolutelyQuasiSeparated)`, and
  `(hln : ∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T))`.
  Absolute quasi-separatedness is the existing affine-pair fibre-product compactness
  test, equivalent to absolute diagonal quasi-compactness (Stacks 0AHR), so the base
  need not be quasi-separated.
- Quasi-coherent cohomology: `(hK : Y.derivedQCohProperty K)` uses the recorded
  predicate, which tests Mathlib IsQuasicoherent after the inverse of the fixed
  small-model equivalence in every cohomological degree.
- Strictly perfect means bounded complexes of finite-free retracts: this is exactly
  the existing `IsMPseudoCoherent` definition in SpaceSupportedPerfectApproximation.
  Its `StrictPerfectCoefficientPackageOnSite` gives a finite rank in each degree,
  an inclusion into the finite product of copies of the structure module, a
  retraction, and their splitting identity. It imposes no chain-map requirement on
  those degreewise splittings. The separate bound covers both ends of the complex.
- Pseudo-coherence is rendered as `(∀ m : ℤ, Y.IsMPseudoCoherent m K)`.
  Unfolding the existing predicate: choose a representative E of K, then for every
  site object a covering sieve, and on every member a bounded finite-free retract
  complex F and map F → E restricted there, with IsIso on cohomology above m and
  Epi at m. Covers, bounds and ranks can depend on m and the covering member.
  This uses precisely the approximation notion, not the distinct existing all-m
  predicate formulated via a single local bounded-above finite-free model.
  Stacks 08FU(1)-(3) identifies the representative/chain-map formulation with the
  derived-map formulation of this item, and the affine-basis comparison 039Z
  transfers the condition to every object of the original small etale site.
- Coherence of every H^i: the first right conjunct is `∀ i : ℤ,
  SheafOfModules.IsFinitePresentation (Y.smallModuleEquivalence.inverse.obj
  ((DerivedCategory.homologyFunctor Y.SmallModules i).obj K))`.
  Under hln, Stacks 07UB identifies this existing finite-presentation predicate
  with coherence, equivalently quasi-coherence and finitely generated modules on
  all Noetherian affine etale charts. It includes every integer degree.
- Eventual upper vanishing: the second conjunct is `∃ b : ℤ, ∀ i : ℤ, b < i →
  IsZero ((DerivedCategory.homologyFunctor Y.SmallModules i).obj K)`.
  There is one b for the whole space, not one bound per chart; equivalences
  preserve and reflect zero objects, so this is vanishing in the original topos.
- Both directions are the displayed `↔`; no lower bound, finite Tor amplitude,
  perfection, or finite cohomological dimension is assumed or asserted.
- K-flat tensor/pullback and K-injective direct image in the introductory convention
  introduce no operation in this criterion's actual signature. The recorded
  canonical module and derived-module calculus is imported unchanged.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, EtaleSite,
  structureSheaf, Modules, etalePullback, etalePullbackMap.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently Mathlib SheafOfModules.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and the slice
  sheafification instances, using Mathlib SheafOfModules.IsQuasicoherent.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: ModuleDirectImageModel,
  moduleDirectImage, moduleTensorPullback, moduleTensorAdjunction; preserved as
  the canonical functors, with the chart projections in their specification.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: SmallModules,
  SmallEtaleModel, smallModuleEquivalence; landed def-sfb-space-small-ringed-model.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: DerivedModules,
  derivedQCohProperty; landed def-sfb-space-derived-module-calculus.
- Sheaf.AlgebraicGeometry.SpaceSupportedPerfectApproximation: IsMPseudoCoherent;
  landed def-sfb-space-supported-perfect-approximation.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointTopologicalSpace;
  landed def-a1-space-point-topology.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated:
  IsAbsolutelyQuasiSeparated; landed def-sfb-space-absolute-quasi-separated.
- Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian, including its
  component_noetherian field, the Mathlib match of pqf-lem-affine-open-locnoeth.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:
  SheafOfModules.IsFinitePresentation; reused, not privately defined.

All already stated proof dependencies are plain imports, including
AffineEtaleDerivedModuleRealization.exists_affineEtaleDerivedModuleRealization
(in namespace AlgebraicGeometry.Scheme.Modules),
AlgebraicGeometry.isPseudoCoherent_affine_iff,
AlgebraicGeometry.Scheme.IsPseudoCoherent,
DerivedCategory.IsPseudoCoherent and
DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology.
The node lem-sfb-etale-pseudocoherence-descent and
lem-sfb-qc-space-affine-etale-atlas have no Lean record in the read clone;
they are proof inputs only, not missing statement prerequisites.
The module docstring carries the node's six proof steps and their cited inputs.

Source checks: read spaces-perfect.tex lemma-identify-pseudo-coherent-noetherian
(Tag 08IK), which explicitly states the final equivalence with D^-_Coh; read
sites-cohomology.tex definition-pseudo-coherent (08FT) and
lemma-pseudo-coherent-independent-representative (08FU); read the recorded
finite-presentation/coherence interface in AlgebraicSpaceCoherentAbelian (07UB).

Edge cases checked before writing: the empty algebraic space has only zero module
sheaves, admits rank-zero approximations, and any b is an upper bound; K = 0
similarly satisfies both sides. Negative m, negative upper bounds, and arbitrary
shifts are permitted. Cohomology may extend arbitrarily far downwards. A field
module of infinite rank concentrated in degree zero fails finite presentation
and the degree-zero approximation, so neither side is automatic. A complex with
nonzero coherent cohomology in arbitrarily large degrees fails the single upper
bound and cannot have the m-approximations. No assumption on the base scheme
silently restricts these examples.

Searches made (2026-10-24):

- msearch.py leanfinder: "Pseudo coherent complexes on a Noetherian algebraic space
  are exactly bounded above complexes with coherent cohomology". Eight hits:
  DerivedCategory.isGE_iff, instIsGEObjCochainComplexIntQOfIsGE, isGE_Q_obj_iff,
  instIsLEObjCochainComplexIntQOfIsLE, isLE_iff, isLE_Q_obj_iff,
  CochainComplex.isGE_iff, CochainComplex.isLE_iff. None is this criterion.
- msearch.py loogle: `"PseudoCoherent"`; zero hits.
- msearch.py grep: `PseudoCoherent|StrictlyPerfect|AlgebraicSpace`, subdirectory
  AlgebraicGeometry; zero Mathlib hits.
- rg over lean/WeilConjectures for the item id: no hit. Concept/name searches for
  IsPseudoCoherent, IsNoetherian, IsCoherent found scheme and ring criteria but
  no algebraic-space criterion with this signature.
- rg over lean/Sheaf for PseudoCoherent/IsMPseudoCoherent and algebraic-space
  definitions found the existing small-model fixed-degree approximation predicate,
  point topology and absolute quasi-separatedness used above. No duplicate theorem.
- DAG searches located the five landed definition nodes cited above; no new node
  or private copy is needed.

No STATEMENT-DISPUTED issue or node fault was found. The only item changes outside
lean are the five authorized additions of already landed definition nodes to stmt_deps.

Validation: scompile.py compiled the theorem as a sandbox module and as its library
module under the default 60-second per-file limit. No errors or non-sorry warnings.
The complete module is recompiled after finalizing its import list, then checked
by deliver2.py --no-push before delivery.

## Second reading by Q38

The worker reread the theorem against the node and the full existing predicate
signatures. This is a self-check, not an independent reading: the dispatcher brief
forbids starting other agents and assigns independent review to the maintainer.
The key check was to use forall-m IsMPseudoCoherent, since its bounded finite-free
retract approximations directly match this node; the existing all-m IsPseudoCoherent
uses a different equivalent characterization and was not substituted. The right
side has coherence in all degrees and one global upper bound. The three components
of Noetherianity are all present, and the localization universe remains independent.
No statement correction, extra mathematical hypothesis, or mismatch was found.
