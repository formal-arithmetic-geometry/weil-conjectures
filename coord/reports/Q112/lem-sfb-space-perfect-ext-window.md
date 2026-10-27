## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePerfectExtWindow` states
`AlgebraicGeometry.AlgebraicSpace.perfect_ext_window`, with proof `sorry`.
It is Stacks Project `spaces-perfect.tex`, Tag 09MB,
`lemma-ext-from-perfect-into-bounded-QCoh`, assertion (1), read at lines 4110–4180
of the local source. Assertion (2) is outside this node. No definition is added,
no theorem is proved, and no statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The size convention is explicit `universe u w`; schemes and section modules
  use `u`, while `[HasDerivedCategory.{w} X.SmallModules]` chooses the independent
  localization morphism universe `w`.
- The scheme is `{S : Scheme.{u}}`. No separatedness, quasi-compactness or
  Noetherian assumption is imposed on S.
- The algebraic space over S is `(X : AlgebraicSpace S)`, the existing full
  subcategory of fppf sheaves with representable diagonal and étale scheme atlas.
- Quasi-compactness is `[CompactSpace (Point X.obj.obj)]` for the recorded
  algebraic-space point topology: every open cover has a finite subcover.
- Absolute quasi-separatedness is `(hqs : X.IsAbsolutelyQuasiSeparated)`.
  This uses the landed affine-test formulation of Tag 0AHR, equivalent to
  quasi-compactness of the absolute diagonal, including over arbitrary S.
  It does not use the weaker property of a relative diagonal over S.
- The small étale structure sheaf is `X.smallStructureSheaf` on the existing
  small affine model. `X.SmallModules` is `ringedSiteModules` on its underlying
  ring sheaf. The recorded equivalence `X.smallModuleEquivalence` is the actual
  affine-chart restriction equivalence with the original small étale modules,
  in the same section universe. This changes the presentation, not the objects
  quantified over in the mathematical assertion.
- The unbounded category D(O_X) is `X.DerivedModules`, definitionally
  `DerivedCategory X.SmallModules`. The object is `(P : X.DerivedModules)`;
  it is not required separately to be quasi-coherent.
- Perfectness is `(hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.
  {u, u, u, w} X.smallStructureSheaf P)`. This is represented locally on
  covering sieves by bounded complexes of degreewise finite-free retracts.
  It does not require a global strict-perfect model or a uniform rank.
- The conclusion begins `∃ a b : ℤ, a ≤ b ∧`: the interval is nonempty and
  integral. These quantifiers precede F, so the bounds are independent of F.
- Every target in C_X is `∀ F : X.DerivedQCoh`. This is the full subcategory
  of the ambient unbounded derived category whose cohomology, transported back
  along the module equivalence, is quasi-coherent. It is not D(QCoh(X)).
- The premise is `∀ q : ℤ, a ≤ q → q ≤ b → IsZero
  ((DerivedCategory.homologyFunctor X.SmallModules q).obj F.obj)`.
  Both endpoints are included and no vanishing outside the interval is assumed.
- The conclusion is `Subsingleton (P ⟶ F.obj)`, using Hom in the ambient
  derived category. Since it is preadditive, this says precisely that its Hom
  group is zero. No `IsZero` predicate is applied to a bare type.

Dependency declarations used (all full signatures and relevant docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `structureSheaf`, `Modules` and the actual
  representability/étale/atlas definitions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; the cohomology functor is
  `DerivedCategory.homologyFunctor` in `DerivedCategory.HomologySequence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`, using the existing Mathlib
  `SheafOfModules.IsQuasicoherent` / `isQuasicoherent`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and its defining predicate
  `IsLocallyStrictPerfectComplexOfUniverses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallEtaleModel`, `smallEtaleModelTopology`, `smallStructureSheaf`,
  `SmallModules`, `smallModuleRestriction`, `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`:
  `DerivedModules`, `derivedQCohProperty`, `DerivedQCoh`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace` on the already recorded `Point`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.

The last four definition nodes are already landed and are added to stmt_deps
under the rule permitting existing landed notion dependencies. All original
statement dependencies remain. Every statement dependency is publicly imported;
all fourteen proof dependencies have their recorded modules imported privately,
with the two Tor-bound nodes sharing `DerivedCategory.FlatModel`. The truncation
node uses its recorded Mathlib match `TStructure.TruncLEGT`. No import-cycle
omission was needed. The theorem docstring reproduces all five proof steps:
perfect dual and Tor interval, truncation tails, tensor bounds and quasi-coherence,
triangulated tensor and derived global sections, and the RHom/Hom identification.

Edge cases checked before writing:

- Empty X: no nonemptiness assumption; zero modules and the empty chart are
  admitted. The proof's uniform-bound argument can choose the interval [0,0].
- P = 0 or F = 0: zero Hom is represented by Subsingleton, consistent with the
  zero morphism in the derived category.
- Singleton interval a = b: allowed by `a ≤ b`; q is tested inclusively.
- F unbounded in either or both directions: no boundedness instance or premise
  is imposed. Only the finitely many cohomology degrees in [a,b] are tested.
- Non-quasi-separated base: hqs is absolute for X, with no extra condition on S.
- Locally varying perfect bounds/ranks: the existing site-perfect predicate
  allows them; global uniformity is in the proof, not an added hypothesis.
- Universes: independent u and w; the model site is small in u and so its
  object/Hom/coefficient universes are all u. No equality is imposed on the
  original large étale site's object and Hom universes.

Searches for an existing statement:

- `msearch.py ... leanfinder "A perfect complex on a quasi compact quasi
  separated algebraic space has a finite cohomology window detecting vanishing
  of Hom"`: eight hits, headed by `DerivedCategory.isLE_iff`, `isGE_iff` and
  `subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`; no space-perfect Hom window.
- `msearch.py ... loogle '"IsPerfect", "Hom"'`: two unrelated
  `IsPerfectClosure.equiv_toRingHom` / `equiv_symm_toRingHom` hits.
- `msearch.py ... grep 'IsPerfect|PerfectComplex|ext.*[Ww]indow' CategoryTheory`:
  zero hits.
- `msearch.py ... leansearch "There exist integers a b such that Hom from a
  perfect complex to L is zero whenever its cohomology vanishes between a and b"`:
  eight generic cochain Hom, Ext and cohomology-vanishing hits; no exact result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `perfect.*[Ww]indow|[Ww]indow.*perfect` found only tensor/Tor-window material,
  not this Hom statement. The prescribed upstream `grep -rn` of the node id
  found no existing declaration.
- A broader search of `Perfect*.lean` found the scheme-only analogue
  `AlgebraicGeometry.Scheme.exists_subsingleton_hom_of_isPerfect` in upstream
  `PerfectHomGap.lean` (Tag 09M4); its signature/docstring were read. It is about
  the Zariski module category of schemes, so does not state this algebraic-space
  étale assertion. The new full name was checked against Mathlib, upstream and
  project sources, with no clash.

Validation: `scompile.py Q112 lem-sfb-space-perfect-ext-window <module>`
compiled both the sandbox module and its actual library module, in 9.3 s and
3.8 s respectively, with no errors or warnings. The dry-run and delivery results
are recorded below after they run. No disputed statement or dependency fault.

## Second reading by Q112

A separate pass through the node and finished module checked every binder and
conclusion after compilation. No second agent was used, as the dispatch brief
forbids starting agents; the maintainer performs the independent review.

The pass checked S and X without base restrictions, point-compactness, absolute
quasi-separatedness, site-perfect P, unbounded ambient D(O_X), full D_QCoh
membership of F, existence and order of integer endpoints before quantifying F,
inclusive vanishing at both endpoints, and Subsingleton of the ambient Hom type.
All match the node and Tag 09MB(1). It also unfolded the small-model module
abbreviations and the quasi-coherent predicate to check that the cohomology is
transported by the specified equivalence, and read the local-perfect definition
to check finite-free retracts and locally varying bounds. No missing clause or
added mathematical hypothesis was found. Four already landed owning definition
nodes were added to stmt_deps to record the interfaces used; no replacement
notion, new node, dependency module or statement correction was required.

Dry run: `deliver2.py Q112 lem-sfb-space-perfect-ext-window --no-push`
returned `OK (dry run): commit e0a0d373947 passes the preflight and compiles;
nothing pushed`. The staged set was exactly the module, the item node, and this
report. The accepted split and source statement were preserved.
