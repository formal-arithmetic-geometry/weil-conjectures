## Worker report

Stage 2, Q109, lem-sfb-space-affine-pullback-perfect-detection. The inherited
BLOCKED concerned stage 1. The live node has no lean record, and the current
brief-stage2 section 0 explicitly authorizes this handoff. The accepted statement,
proof split, source and review are preserved. Nothing is proved.

The module Sheaf.AlgebraicGeometry.SpaceAffinePullbackPerfectDetection states
AlgebraicGeometry.AlgebraicSpace.affinePullbackPerfect_detectsIso.
Hypothesis and clause comparison:

- S is `{S : Scheme.{u}}`; `{Z' Z : AlgebraicSpace S}` and `h : Z' ⟶ Z`
  are precisely the spaces and morphism over S.
- Affineness is `haffine : MapIsAffine h`: every affine scheme test has an
  affine representing scheme, with its cartesian square and both projections.
- Quasi-compactness is `CompactSpace (Point Z.obj.obj)` and the same for Z'.
  Point carries the existing atlas topology, so this is finite-subcover compactness.
- Quasi-separatedness is `hqs`, respectively `hqs'`: every pair of affine
  scheme maps into the space has quasi-compact fibre product. This is the
  scheme-test form of quasi-compactness of the absolute diagonal. It does not
  assume the base S is separated or quasi-separated. In particular we do not
  silently substitute quasi-separatedness relative to an arbitrary S.
- The ambient unbounded category is the recorded `DerivedModules` on the small
  ringed model. `{C D : Z'.DerivedQCoh}` includes exactly the quasi-coherent
  cohomology hypotheses, and `v : C ⟶ D` is their full-subcategory morphism.
- Every perfect P in D_QCoh is `∀ P : Z.DerivedQCoh` followed by the recorded
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u}` predicate on
  `Z.smallStructureSheaf`. This means locally bounded complexes of retracts of
  finite free structure-sheaf modules, with bounds/ranks varying on the cover.
  The small affine ringed site is equivalent to the original etale module topos;
  it retains the same regular-function rings and section universe.
- Derived tensor pullback is `(derivedTensorPullback h).obj P.obj`, defined in
  the now-landed def-sfb-space-derived-tensor-pullback by Mathlib totalLeftDerived
  applied to the canonical ordinary module tensor pullback on cochain complexes.
  Its universal counit comes from the right Kan extension; K-flat resolutions of
  flat modules compute it as in Stacks 06YS and 06YY. It is not an arbitrary functor
  or extra hypothesis.
- Every integer is `∀ j : ℤ`, including negative j and zero. The actual function
  `fun a => a ≫ (shiftFunctor Z'.DerivedModules j).map v.hom` is postcomposition
  by v[j]. `Function.Bijective` is the exact Hom-set bijection assumption.
- The conclusion is `IsIso v`, in the full subcategory D_QCoh, equivalently in
  its ambient derived category. There is no boundedness hypothesis.
- `u` and independent localization morphism universes `w` on Z and `w'` on Z'
  are explicit; `HasDerivedCategory` is the chosen localization-size convention, not a
  geometric condition or restriction on coefficients. autoImplicit is false.

Dependency declarations read and reused:
Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom;
Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, Modules, structureSheaf,
EtaleSite and IsRepresentableWith;
Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules;
Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory and HasDerivedCategory;
Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and the slice
sheafification obligations, retaining Mathlib SheafOfModules.IsQuasicoherent;
Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: SmallModules,
DerivedModules, DerivedQCoh, derivedQCohProperty and smallModuleEquivalence;
Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite: MapIsAffine;
Sheaf.AlgebraicGeometry.ProperCurveModuli: MapIsQuasiCompact and mapPoint;
Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses:
SheafOfModules.IsPerfectOnRingedSiteOfUniverses;
WeilConjectures.Algebra.Homology.KFlat: CochainComplex.IsKFlatTensor;
Mathlib.CategoryTheory.Functor.Derived.LeftDerived: HasLeftDerivedFunctor,
totalLeftDerived and totalLeftDerivedCounit.
The size-convention node is metatheoretic and has no module.

Proof dependency Mathlib.CategoryTheory.Triangulated.Pretriangulated is imported
without public: its comp_distTriang_mor_zero₁₂, Triangle.coyoneda_exact₂ and
Triangle.coyoneda_exact₁ give the recorded exactness clauses. The other named
proof dependencies have no lean binding and hence no proof import yet. Their
full statements and the complete accepted four-step proof are reflected in the
main theorem docstring; no unavailable proof theorem is fabricated.

Source checked: literature/stacks-project/spaces-perfect.tex, lines 3674ff
(09IY) and 3747ff (0E4R); the latter explicitly includes affine morphisms.
Edge cases: identity on Spec k reduces to ordinary perfect detection; empty
source has zero derived category and all its arrows invertible; zero objects
and zero morphisms satisfy exactly the expected detection criterion. A non-flat
affine closed immersion is included because pullback is derived. The complexes
C,D may be unbounded in both directions. Local perfect bounds may vary on the
cover. No nonempty, finite-type, Noetherian or flat assumption was added.
No statement dispute or source correction is required.

Searches: msearch.py leanfinder with the full affine perfect-detection statement
returned only ordinary scheme morphism properties. Loogle query
`"Functor.ReflectsIsomorphisms", "Adjunction"` returned zero hits. Mathlib grep
`[Pp]erfect.*[Gg]enerator|[Aa]ffine.*[Cc]onservative|[Pp]ullback.*[Gg]enerator`
in AlgebraicGeometry returned zero. Exact node-id search in WeilConjectures and
Sheaf returned no existing declaration. Project searches for IsPerfect,
derivedTensorPullback, smallModuleTensorPullback and derived pullback located
the reused general-site perfectness, ordinary module operations, derived direct
image and scheme-only derived pullback, but no algebraic-space derived pullback
or this detection theorem. Actual msearch receipts are in searches.jsonl.

The delivered theorem compiles using scompile.py against the live library. No
local/global build was run. A concurrent O3 landing supplied exactly the missing
derived pullback during this task: its full node and module were re-read, and the
private overlapping module and new-node copy were removed. The final delivery
uses O3's reviewed SpaceDerivedTensorPullback unchanged, with independent source
and target localization universes. No dependency record is changed.

## Second reading by Q109

Self-check only: no independent worker was started, as explicitly prohibited by
the dispatched brief. Independent maintainer review remains required. Re-read
the node, final theorem and the newly landed dependency side by side. The first compile caught an invalid
attempt to pass an object to pullback.diagonal. Replaced that ill-typed term by
the full affine-pair criterion for the absolute diagonal, used elsewhere in the
library; this also avoids an accidental relative separatedness condition on S.
Rechecked every hypothesis and the postcomposition function above. The landed
dependency explicitly preserves the original tensor pullback and its total left
derived universal property. Its proof docstring uses K-flat complexes of flat
modules, exactly as Stacks sites-cohomology 06YS and 06YY. No hypothesis, conclusion or case changed.

Final dependency update: Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback,
AlgebraicGeometry.AlgebraicSpace.derivedTensorPullback (O3, landed during task),
is reused unchanged. Read smallTensorPullbackComplex and its named derivability
theorem: the former is degreewise canonical tensor pullback followed by Q, and
the latter supplies the Kan-extension existence property. Mathlib totalLeftDerived
therefore gives actual data determined by a universal property. The initial
private homotopy-level construction is not delivered. Searches are receipts of
the earlier state; they are not claims that the concurrently landed node is absent.
No new node, dependency repair, statement correction or source change is delivered.
