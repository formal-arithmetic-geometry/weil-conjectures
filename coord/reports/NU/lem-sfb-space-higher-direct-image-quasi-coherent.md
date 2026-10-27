## Worker report

Stage 2, group NU, item lem-sfb-space-higher-direct-image-quasi-coherent.
This repairs returned immutable head 34fa30573515, retaining the saved theorem,
source investigation, proof docstring and search log. The initial repair dry run
passed at fc75aa1949c, so no reconstruction of the statement was needed. I compared
the saved packet with the current shared base node: the base still has no Lean record
and lists the five original statement dependencies; its statement, proof and other
non-Lean fields agree with the saved packet. This repair preserves them.

H2 repair: following the explicit return instruction, replace the saved packet's
lem-sfb-space-quasicompact-affine-tests statement dependency with the two owning
nodes def-sfb-space-quasi-compact-presheaf-map and
def-sfb-presheaf-map-separated-diagonal. Their existing declarations are
IsQuasiCompactPresheafMap and diagonalPresheafMap in
Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal, now public-imported. The affine-test
theorem stays in proof_deps and its module is imported privately. The saved
statement dependency def-sfb-space-derived-module-calculus is retained. This is the
specific dependency correction requested in the return; the mathematical statement,
Lean signature and accepted proof are unchanged. No new nodes or dependency modules
are introduced.

H11 repair: the section “Second reading by NU” below now records an actual reading
of the node, module, source and dependency definitions, clause by clause, by this
worker. It describes the findings and the exact import/dependency corrections.
The source read was literature/stacks-project/spaces-cohomology.tex, Tag 0720,
lemma-higher-direct-image, including its preceding comparison and relative Čech
paragraphs. Its hypothesis is exactly a quasi-compact quasi-separated map of algebraic
spaces over any scheme, and its conclusion covers every nonnegative higher image.
I found no statement dispute or source correction.

Hypothesis and clause correspondence:

- `{S : Scheme.{u}}` and `{X Y : AlgebraicSpace S}` use the recorded scheme and
  algebraic-space definitions. `f : X ⟶ Y` is the original space morphism.
- `hqc : IsQuasiCompactPresheafMap f.hom.hom` is the existing affine-scheme-test
  atlas predicate. The recorded quasiCompact_iff_quasiCompact_scheme_tests theorem
  identifies this with inverse images of quasi-compact schemes being quasi-compact;
  it is the node's quasi-compactness, with no representability hypothesis on f.
- `hqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom)` states precisely
  quasi-compactness of the relative diagonal. It does not impose separatedness or
  absolute quasi-separatedness of either space.
- `F : X.Modules` and `[F.IsQuasicoherent]` use the original structure sheaf and
  Mathlib's local free-presentation predicate, through the already-recorded slice
  sheafification instances. There is no finite presentation assumption.
- `i : ℕ` covers exactly i >= 0, including i = 0. `(i : ℤ)` selects cohomological
  degree i, without a sign reversal or boundedness assumption.
- The conclusion places F in degree zero by DerivedCategory.singleFunctor, applies
  the fixed derivedDirectImage, takes DerivedCategory.homologyFunctor in degree i,
  then applies Y.smallModuleEquivalence.inverse. Thus its IsQuasicoherent is on
  Y's original small étale module category, not an arbitrarily chosen replacement.
  derivedDirectImage is definitionally the rightDerivedFunctor of
  X.smallModuleEquivalence.inverse ⋙ moduleDirectImage f ⋙ Y.smallModuleRestriction.
  Equivalences of abelian categories are exact and preserve injective resolutions;
  a bounded-below complex of injectives is K-injective. Consequently this is the
  ordinary R^i f_* computed in all module sheaves, as required by the item. It is
  not a derived functor taken only in QCoh.
- `[HasDerivedCategory.{w} X.SmallModules]` and its Y counterpart provide the
  localization interfaces required by the recorded derived calculus. The localization
  universe w is arbitrary; these binders impose no geometric or coefficient condition.
  No Noetherian, finite-type, coherent or separated hypothesis appears.

Dependency sources opened and used: Sheaf.AlgebraicGeometry.AlgebraicSpace
(AlgebraicSpace, EtaleSite, structureSheaf, Modules); AlgebraicSpaceQuasiCoherentModule
(QCoh and the two slice sheafification instances using SheafOfModules.IsQuasicoherent);
AlgebraicSpaceModuleOperations (the chart-limit ModuleDirectImageModel, its uniqueness,
moduleDirectImage, moduleDirectImage_isRightAdjoint and tensor adjunction);
SpaceQuasiCompactAffineTests (the affine-test/scheme-test equivalence);
Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal (IsQuasiCompactPresheafMap and
its actual diagonalPresheafMap); AlgebraicSpaceSmallRingedModel (SmallModules,
smallModuleRestriction, smallModuleEquivalence); AlgebraicSpaceDerivedModules
(smallModuleDirectImage, its additivity, smallModules_hasKInjectiveResolutions,
derivedDirectImage); and the upstream RightDerivedFunctor.Defs (the actual
K-injective right-derived construction). Mathlib's InjectiveResolution and
IsQuasicoherent declarations were read, including their defining fields. No private
copy or arbitrary direct-image functor is introduced.

Every accepted proof step is transcribed in the theorem docstring, with its cited
node IDs kept intact. The modules of all recorded proof dependencies are imported
privately; the affine-scheme Mathlib leaf imports AffineScheme and QuasiSeparated.
Proof prerequisites which have no Lean declaration yet are not restated. Public
imports provide statement dependencies. All commands use module mode.

Edge cases checked from the statement and constructions: empty X or Y is not
excluded; the zero module is allowed; i = 0 really selects degree zero; an identity
map is allowed without assuming the base scheme qcqs; nonseparated qcqs maps are
allowed because the diagonal need only be quasi-compact; arbitrary characteristic
and non-Noetherian bases are allowed. The module-carrier universe is unchanged by
the actual small-site equivalence. The additional localization universe is independent
of it, as in the recorded derived-calculus interface.

Searches for an existing statement were made using the mandated msearch.py wrapper.
The exact commands and actual results are recorded in searches.jsonl. LeanFinder
was tried with both the higher-image formulation and the injective-resolution
cohomology formulation; it found local quasi-coherence predicates and scheme notions,
not this algebraic-space higher-image theorem. LeanSearch found Functor.rightDerived,
right-adjoint pushforwards and generic derived-functor universal properties, not the
quasi-coherence conclusion. Loogle SheafOfModules.IsQuasicoherent found the local
predicate and pushforwards with extra continuous/cocontinuous and colimit-preservation
hypotheses. I read Quasicoherent.lean lines 295-345: those describe an underived,
colimit-preserving site pushforward, not general R^i f_* for qcqs maps. The source
grep for rightDerived.*[Qq]uasi|[Qq]uasi.*rightDerived|higher.*[Qq]uasi found only
derivability-structure results. Whole-project searches under WeilConjectures and
Sheaf found no declaration tagged with this item or stating the full space theorem.
The existing AlgebraicSpaceQuasiCoherentPushforward theorem covers only i=0 and
assumes separatedness, and its proof is sorry. It is not an attachment for this item.
No Mathlib match is claimed and no search record is fabricated.

The initial server compile completed in both sandbox and library modes (15.7 s and
7.8 s). The final delivery dry run will validate the final imports and report, using
the same single-file server compiler. No Lake or global build is run.

## Review by NU

I compared the current accepted node, Tag 0720 and the written declaration clause
by clause. In particular I checked that hqs refers to the relative diagonal of f
rather than of X over S, and that no separatedness assumption was substituted for
quasi-separatedness. I unfolded the recorded derivedDirectImage and checked the
order of both equivalences: F restricts into X.SmallModules before the single
functor, and the degree-i result returns through Y's inverse equivalence. This
retains the same canonical chart-limit f_* and structure-ring action. The degree
cast is positive i, not -i. The theorem is quantified over arbitrary derived-category
interfaces and does not choose a second abelian category structure.

The initial docstring wrapping split some hyphenated DAG IDs across lines; I repaired
the wrapping so each citation remains intact. I removed resolution-only imports
that the final signature does not use, and added the two source modules of the
already-existing affine-scheme qcqs Mathlib leaf as private proof imports. The
accepted natural-language split and its sources remain unchanged. The only proof
left is the item's single named sorry, with the full accepted proof in its docstring.

## Second reading by NU

I reopened the saved node and the complete theorem module, then read
spaces-cohomology.tex, lemma-higher-direct-image (Tag 0720), lines 113–168.
The source quantifies over a scheme S, a map of algebraic spaces over S, a
quasi-coherent O_X-module and each nonnegative higher direct image, assuming only
that the map is quasi-compact and quasi-separated. The theorem has exactly those
geometric hypotheses and conclusion. The following is this worker's second reading;
no other reader or agent is claimed.

1. Base and map. `{S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)`
   renders the first two clauses. I read AlgebraicSpace.lean: AlgebraicSpace is the
   full subcategory of fppf sheaves with representable diagonal and étale surjective
   atlas; its morphisms are natural transformations. `X.Modules` uses the original
   small étale site and its regular-functions structure sheaf. Neither X nor Y is
   assumed to be a scheme, affine, Noetherian or absolutely quasi-separated.

2. Quasi-compactness. `hqc : IsQuasiCompactPresheafMap f.hom.hom` uses the
   definition at SpaceQCSeparatedEtaleLocal.lean:38–45: every affine scheme test
   admits a quasi-compact scheme atlas of the fibre product that is étale and
   surjective. The recorded affine-test/scheme-test equivalence in
   SpaceQuasiCompactAffineTests identifies this with the node's inverse-image
   formulation; it is proof support, not a definition used in the signature. I found
   the returned dependency-ownership error and replaced that theorem statement
   dependency by def-sfb-space-quasi-compact-presheaf-map. The theorem remains a
   proof dependency and now has a private import.

3. Quasi-separatedness. `hqs : IsQuasiCompactPresheafMap
   (diagonalPresheafMap f.hom.hom)` is quasi-compactness of the relative diagonal
   X → X ×_Y X. I read diagonalPresheafMap: its data are pullback.lift of the two
   identity maps of the source. It is the diagonal of f, not the absolute diagonal
   over S. The signature never asks for IsSeparatedPresheafMap or a closed
   immersion. I added its owning def-sfb-presheaf-map-separated-diagonal statement
   dependency and public-imported SpaceQCSeparatedEtaleLocal. No additional
   separation hypothesis appears.

4. Input module. `(F : X.Modules) [F.IsQuasicoherent]` renders every
   quasi-coherent O_X-module on the small étale ringed site. I read the recorded
   AlgebraicSpaceQuasiCoherentModule interface and Mathlib's QuasicoherentData and
   IsQuasicoherent: the witnesses are local presentations by coproducts of copies
   of the ring; there is no finiteness requirement on the presentation. The
   existing slice instances supply its specialization, with no duplicate predicate.

5. Degree and derived image. `(i : ℕ)` covers every i ≥ 0. The expression first
   applies `X.smallModuleRestriction.obj F`, places this module in degree zero by
   `DerivedCategory.singleFunctor X.SmallModules 0`, then applies
   `derivedDirectImage f`. I reopened AlgebraicSpaceDerivedModules.lean:
   smallModuleDirectImage is precisely X.smallModuleEquivalence.inverse ⋙
   moduleDirectImage f ⋙ Y.smallModuleRestriction, and derivedDirectImage is its
   rightDerivedFunctor. ModuleDirectImageModel fixes moduleDirectImage by the
   compatible-chart limit universal property and its projections. Thus the
   expression derives the specified canonical all-module f_*, not a functor on
   QCoh. A bounded-below injective resolution of F computes this same K-injective
   right-derived value. `homologyFunctor ... (i : ℤ)` takes positive cohomological
   degree i, with no sign reversal.

6. Output and universes. `Y.smallModuleEquivalence.inverse.obj` returns that
   homology module to Y.Modules before `.IsQuasicoherent` is asserted. I read
   AlgebraicSpaceSmallRingedModel.lean: smallModuleRestriction is actual affine
   chart restriction, smallModuleEquivalence is its asEquivalence, and SmallModules
   keeps the original module universe u. The conclusion is therefore on the
   original Y_et and its structure sheaf. `universe u w` and the two explicit
   `HasDerivedCategory.{w}` binders leave the localization universe arbitrary;
   neither introduces a geometric restriction or equates site universes.

7. Edge cases and exclusions. i = 0 gives ordinary degree-zero higher image. The
   zero module and empty spaces are allowed by all binders. Identity morphisms
   require no qcqs hypothesis on S. Non-separated qcqs maps remain allowed because
   hqs asks only for quasi-compactness of the relative diagonal. The source's lack
   of Noetherian, finite-type, coherence and additional separatedness hypotheses is
   preserved. No counterexample or statement dispute was found.

8. Proof and scope. I matched all five accepted node proof steps to the declaration
   docstring: affine étale localization, qcqs atlas nerve, relative Čech spectral
   sequence and scheme comparison, kernel/image/cokernel page induction, and the
   finite extension filtration. The cited IDs remain intact, including the affine
   tests in steps 1 and 2. The only proof body is the named theorem's `sorry`;
   no definition or helper was added. Only the returned dependency ownership,
   public/private imports and this reading/report were corrected; the signature
   and all five proof steps remain unchanged.

## Search log and validation

- grep: `rightDerived.*[Qq]uasi|[Qq]uasi.*rightDerived|higher.*[Qq]uasi` — 3 hits; no match for this item.
- leansearch: `Right derived direct image preserves quasi coherence for qcqs algebraic spaces` — 8 hits; no match for this item.
- loogle: `SheafOfModules.IsQuasicoherent` — 12 hits; no match for this item.
- leanfinder: `Higher direct images of quasi coherent modules for quasi compact quasi separated morphisms of algebraic spaces are quasi coherent` — 8 hits; no match for this item.
- leanfinder: `Cohomology of the direct image of an injective resolution of a quasicoherent sheaf on an algebraic space under a qcqs morphism is quasicoherent` — 8 hits; no match for this item.

The initial repair dry run passed at fc75aa1949c. After the H2 and H11 repairs,
scompile.py compiled the sandbox module in 7.7 s and the library module in 1.6 s,
with no errors or warnings. The repaired delivery dry run exited 0 and printed
`OK (dry run): commit abe13ec91b0 passes the preflight and compiles; nothing pushed`.
The final submission repeats preflight and compilation through deliver2.py. Only
the item record, its single Lean module and this report are delivered.
