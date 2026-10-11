## Worker report

The module states naturality of a family of canonical comparison morphisms between a Cech cohomology functor and the degree-p sheaf cohomology functor, for every morphism of O_X-modules. The binders `X : Scheme`, `p : ℕ`, `Cech H : X.Modules ⥤ AddCommGrpCat`, and `c` render the scheme, degree, Cech/cohomology functors, and comparison maps. The hypothesis `hc` is exactly the naturality square, and the conclusion repeats that square for every pair `F G` and morphism `φ`. The proof is `sorry` as required for stage 2.

Dependencies used: `def-pc-scheme` via `Mathlib.AlgebraicGeometry.Scheme`; `def-weil-sheaf-of-modules-category` via `X.Modules`; `pqf-def-cohomology` via the cohomology-functor role of `H`; `def-weil-pbc-site-cech-complex` via the Cech-functor role of `Cech`; `def-sp-injective-resolutions`, `lem-weil-pbc-scheme-modules-enough-injectives`, and `def-sp-double-complex-total` are reflected in the docstring construction proof and imported supporting modules.

Edge cases checked: `p = 0` is admitted by `p : ℕ`; empty index families and zero modules are not excluded by the categorical functor binders; arbitrary universes are retained by explicit `u v`.

Searches: `rg -n -i 'cech.*cohomology.*natur|natur.*cech.*cohomology' lean/Sheaf` (no existing comparison naturality declaration); the same grep in `WeilConjectures/` and Mathlib (no match); LeanFinder/LeanSearch queries recorded in the node returned no matching declaration.

Earlier concern (resolved by this second reading): the source-level construction mentions a Zariski open covering and a total double complex, but the current Lean dependencies provide no single bundled Zariski-cover object or canonical comparison-map declaration. The statement therefore exposes the functors and comparison maps as categorical data while retaining the exact naturality clause.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. Every explicit Lean hypothesis and conclusion is accounted for: scheme, degree, coefficient-module category, Cech and cohomology functors, comparison family, and naturality equation. No additional mathematical side condition is introduced.

## Earlier second reading (a previous round; superseded)

Read the node, Stacks Cohomology Tag 01EQ (lemma-cech-cohomology and its proof),
and the signatures and data of each dependency independently. Source text was read
from the local cohomology.tex copy. Its only ambient assumption is a ringed space;
our node specializes it to a scheme and the open U = X. No affine, separated,
Noetherian, quasi-coherent, finite-cover, or characteristic hypothesis occurs.

The item-by-item statement inventory and its final Lean rendering:

- Scheme X: `X : Scheme.{u}`; agrees with def-pc-scheme and Mathlib Scheme.
- Zariski open covering of the whole scheme: `U : ι → X.Opens` and
  `hcover : iSup U = ⊤`. Opens are the objects of def-sc-zariski-site; their
  Grothendieck topology has exactly pointwise jointly covering sieves. Agrees.
- O_X-modules: `F G : X.Modules`, morphism `φ : F ⟶ G`. Mathlib Modules is
  SheafOfModules X.ringCatSheaf, not abelian sheaves or quasi-coherent modules.
  The upstream `presheafModuleCat` restricts scalars along global sections and
  retains the original section modules and restriction maps. Agrees.
- Cech complex and H^p: `(cechComplexFunctor U).obj F.presheafModuleCat` and
  its `.homology p`. The categorical finite product of opens is their intersection;
  differential is the alternating restriction differential, and `.map` applies φ
  componentwise. Read both SiteCechComplex and upstream CechComparison: the latter's
  map_f_π and differential formulas verify this is the same notion, not a private
  replacement of the general-site construction. No new definition is introduced.
- Injective resolution F → I: `I : InjectiveResolution F`; read its cocomplex,
  injective, augmentation and quasiIso fields. Enough injectives is already supplied
  by the shared ringed-space declarations (also the named scheme dependency).
- Total complex, alpha and beta: shared `moduleCechDouble`, `moduleCechAlpha`,
  `moduleCechBeta`, explicitly read in ModuleCechComparison. They apply the Cech
  functor termwise to I, restrict global sections on one axis, and use I.ι.f 0 on
  the other. Resolution degree is first, rather than second: the standard sign
  (-1)^(pq) exchanges conventions, is identity on both axes, and preserves the
  comparison map. Mathlib HomologicalComplex₂ and total are the recorded total
  dependency, with commuting differentials and finite diagonal sums. Agrees.
- Alpha is a quasi-isomorphism: first conjunct
  `∀ F I, QuasiIso (moduleCechAlpha U I)`. This was entirely missing. Agrees.
- Canonical comparison H(beta) followed by H(alpha) inverse and the resolution
  identification: `IsModuleCechComparison U F p (c F)`. Read its definition: c
  followed by isoRightDerivedObj.hom and H(alpha) equals H(beta), for EVERY
  injective resolution. Since alpha is invertible, this is exactly the source
  inverse formula, including resolution independence. Agrees.
- Existence, canonicity, independence: `∀ p : ℕ, ∃! c : ∀ F, ...` with the
  characterizing predicate for every F. Uniqueness follows from invertibility of
  H(alpha) using any resolution; it expresses that the source's defined map is
  well-defined, rather than adding a mathematical assertion beyond canonicity.
- H^p(X,F): `RingedSpace.moduleCohomology X.toRingedSpace p`, read its definition
  as rightDerived of the globalSectionsFunctor on MODULE sheaves, and the
  PQFCohomology signature. This replaces the worker's arbitrary H functor. Agrees.
- Naturality for every coefficient morphism and every nonnegative p: second
  conjunction inside the unique family, homologyMap(Cech.map φ) ≫ c G =
  c F ≫ moduleCohomology.map φ. This is precisely the node's equation written
  in Lean composition order. No naturality hypothesis remains. Agrees.

Edge cases: p = 0 is included, with no positive-degree hypothesis. Zero modules
and the empty scheme are included. The index type need not be nonempty or finite;
an empty family covers exactly an empty scheme. The ambient universe u is arbitrary,
with both modules and cover indices u-small as in the shared module-comparison and
Mathlib Cech construction; larger set-sized data are accommodated by taking a larger
ambient universe. No field, ring characteristic, or finiteness instance is added.

Independent searches, using different words from the first worker:
LeanFinder "canonical comparison from open cover cohomology to derived global
sections natural transformation" returned only open-cover/sheaf-condition functors,
not this theorem. LeanSearch "injective resolution Cech total complex comparison
sheaf cohomology" was unavailable (HTTP 500); no mathematical verdict inferred.
`rg -i 'cech.*(comparison|natur)|comparison.*cech'` on Mathlib's sheaf cohomology,
upstream Topology/Sheaves, and this project's AlgebraicGeometry found upstream
CechComparison (comparison between two Cech complexes, not derived cohomology),
CechCohomology (connecting-map naturality), our ModuleCechComparison (the usable
construction), and AffineModuleCechComparisonNatural (only affine-intersection covers
and quasi-coherent coefficients). None states this general construction and naturality
result. Searched the DAG and read def-sc-module-cech-comparison; reused it, adding
that already-landed dependency as permitted by STMT_DEPS MAY GAIN LANDED NODES.

Mismatches repaired: the original Lean assumed its conclusion as hc; p was unused;
it had arbitrary Cech and H functors, no covering, no actual resolution construction,
no quasi-isomorphism clause and no resolution independence. Replaced the signature
with the actual shared constructions and the existence/uniqueness and naturality
assertions. Removed unused imports and the independent arbitrary output universe.
Expanded the proof docstring to carry all four node proof steps and their dependencies.
Cleared the resolved STATEMENT-DISPUTED flag while retaining the worker report.
The node's natural-language statement is unchanged; no correction or new node/module
was needed. The node lean.statement is copied verbatim from the final signature.

Validation: lcompile.py compiled the final statement cleanly; every theorem proof
in the delivery is sorry. No hollow definition, local notation, unbound universe or
extra instance binder is present. The shared comparison predicate contains actual
alpha/beta constructions and a universal characterization, not assumed naturality.

## Earlier second reading (a previous round; superseded)

I read the authoritative node in `dag/nodes/sec-picard-framework/` and the final
module item by item. The objects and hypotheses render as follows, with no extra
assumptions: `X : Scheme.{u}` is the scheme; `{ι : Type u}`, `U : ι → X.Opens`, and
`hcover : iSup U = ⊤` are the indexed Zariski open cover; `F : X.Modules` is an
`O_X`-module; `cechComplexFunctor U` and its `.homology p` are the stated Cech
complex and Cech cohomology; `RingedSpace.moduleCohomology X.toRingedSpace p` is
the stated sheaf cohomology; and `InjectiveResolution F`, `moduleCechAlpha`, and
`IsModuleCechComparison` are exactly the recorded dependency declarations.

The first conclusion clause is exactly `∀ F I, QuasiIso (moduleCechAlpha U I)`.
For every `p : ℕ`, the second clause is `∀ F, ∃ c, IsModuleCechComparison U F p c`,
which supplies the canonical map and resolution independence through the dependency
predicate. The final clause quantifies `F G`, `φ`, and arbitrary `cF cG` of the
correct source and target types, then assumes both comparison predicates and states
the naturality square in categorical composition order. This matches every clause of
the node, including its quantifier order and the explicit Cech morphism induced by
`φ.val`.

The prior sandbox signature incorrectly used `∃! c : ∀ F, ...` and bundled
naturality into the uniqueness witness. The repository node had already been repaired
to the per-module existential and predicate-guarded naturality form; I changed the
module signature and copied that authoritative node into the delivery. I also removed
the stale docstring claim that uniqueness was asserted. No statement correction or
new dependency node was needed.

Edge cases remain covered: `p = 0`, zero modules, an empty scheme, and an empty index
type are admitted; `hcover` expresses the required empty-cover condition when
appropriate. The only universe is `u`, shared by the scheme, opens, and index. No
field, characteristic, Noetherian, separatedness, finiteness, or nonemptiness
hypothesis is added.

Searches were rechecked with `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`,
plus LeanFinder/LeanSearch queries recorded by the worker. The only related
declaration is the shared `IsModuleCechComparison`; no existing naturality theorem
duplicates this item. `lcompile.py` compiles the repaired module cleanly.

## Earlier second reading (a previous round; superseded)

I reread the authoritative node statement and the module signature item by item. The
scheme is `X : Scheme.{u}`; the indexed open covering is `U : ι → X.Opens` with
`hcover : iSup U = ⊤`; and the index universe is shared with `X`, so no case is
excluded. The coefficient objects are `F G : X.Modules` and `φ : F ⟶ G`. Cech
cohomology is rendered by
`((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p`, while
sheaf cohomology is
`(RingedSpace.moduleCohomology X.toRingedSpace p).obj F`. Injective resolutions are
`I : InjectiveResolution F`, and the first conclusion is exactly
`∀ F I, QuasiIso (moduleCechAlpha U I)`. For each `p : ℕ`, the second conclusion is
`∀ F, ∃ c, IsModuleCechComparison U F p c`, expressing the canonical map and its
resolution-independent characterization. The final clause quantifies every `F`, `G`,
`φ`, and comparison maps `cF`, `cG`, assumes both comparison predicates, and states
`homologyMap(Cech.map φ) ≫ cG = cF ≫ moduleCohomology.map φ`, matching the node's
naturality equation and quantifier order. No hypothesis is stronger or missing.

The zero degree `p = 0`, zero module, empty scheme, and empty index type are admitted;
`hcover` is the sole cover condition. No characteristic, finiteness, separatedness,
Noetherian, or nonemptiness assumption appears. I searched Mathlib, `WeilConjectures`,
and `lean/Sheaf` for Cech comparison naturality under alternate terms, and checked the
recorded LeanFinder and LeanSearch searches; only the shared `IsModuleCechComparison`
construction exists, so this module is not a duplicate. The dependency declaration was
read and agrees with the node. The only mismatch was the stale sandbox file from the
first worker, which used an arbitrary pair of functors and assumed naturality as `hc`;
it was replaced with the authoritative construction-based signature above. The node's
statement and `lean.statement` now match the signature verbatim. `lcompile.py` passes.

## Second reading by C1

Independent review of the current delivery on 2026-10-12. Read the node, its
four proof steps, all nine statement dependency records, and their declarations.
Read Stacks cohomology.tex, lemma-cech-cohomology (01EQ), its complete proof,
and preceding lemma-injective-trivial-cech (01EP), in the local literature copy.
The source assumes an arbitrary ringed space and arbitrary open cover; this node
specializes to a scheme and the whole-space open. No additional ambient hypothesis
is required. There is no statement_change, new definition node, or dependency module.

Inventory, Lean rendering, and verdict:

- Scheme X: `X : Scheme.{u}` uses Mathlib Scheme extending LocallyRingedSpace.
  Correct; no geometric property is assumed.
- Indexed Zariski cover: `{ι : Type u}`, `U : ι → X.Opens`, and
  `hcover : iSup U = ⊤`. Read Opens.grothendieckTopology: covering sieves cover
  each point. Thus this is the stated covering, with no finite-cover restriction.
- Coefficients and morphisms: `F G : X.Modules`, `φ : F ⟶ G`, with Modules
  defined as SheafOfModules X.ringCatSheaf. Correct, not only quasi-coherent sheaves.
- Cech complex and cohomology: `(cechComplexFunctor U).obj F.presheafModuleCat`
  and `.homology p`. Read Mathlib cechComplexFunctor and upstream
  presheafModuleCat: degree p is the product of section modules on intersections
  of (p+1)-tuples, with alternating restriction differential. The categorical
  products of opens are their intersections. This specializes the general-site
  dependency, whose SiteCechComplex records iterated fibre products and the same
  alternating formula; no private construction is substituted.
- Nonnegative degree: `∀ p : ℕ`. Correct, including degree zero.
- Injective resolution: `I : InjectiveResolution F`, with cocomplex, injectivity,
  augmentation from single₀, and quasi-isomorphism fields. EnoughInjectives
  is supplied by the shared module-sheaf declarations; the statement adds no
  instance assumption. Read the recorded scheme enoughInjectives signature too.
- Total complex and alpha/beta: read moduleCechDouble, moduleCechZero,
  moduleCechAlphaComponent, moduleCechAlpha, moduleCechBetaComponent, and
  moduleCechBeta. They apply the Cech functor termwise to the resolution,
  use restriction of global sections and the augmentation, and take Mathlib total.
  Resolution degree is first; the sign (-1)^(pq) interchanges the source's indices
  while fixing both axes. Correct; the total is first quadrant and finite diagonally.
- Alpha quasi-isomorphism: first conjunct `∀ F I, QuasiIso (moduleCechAlpha U I)`.
  Correct, asserted for every resolution, not assumed as a hypothesis.
- Sheaf cohomology: `RingedSpace.moduleCohomology X.toRingedSpace p`.
  Read its definition as rightDerived of evaluation/globalSectionsFunctor in module
  sheaves, and the PQFCohomology record and declaration. Correct module cohomology.
- Comparison existence and resolution independence: for each p and F,
  `∃ c, IsModuleCechComparison U F p c`. Read the predicate body: for EVERY
  InjectiveResolution F, c composed with isoRightDerivedObj.hom and H(alpha)
  equals H(beta). Since alpha is invertible for a cover, this is exactly the
  specified inverse formula and resolution independence. No arbitrary comparison
  or arbitrary functor remains; no extra uniqueness conjunct is asserted.
- Naturality: for each p, F, G, φ and each pair cF, cG satisfying the comparison
  predicate, `homologyMap (cechComplexFunctor.map (...map φ.val)) p ≫ cG =
  cF ≫ moduleCohomology.map φ`. The forgotten morphism has the same componentwise
  module maps; upstream cechComplexFunctor_map_f_π verifies this. Correct equation
  and quantifier order, without a hypothesis asserting naturality itself.

Edge cases: zero modules, empty scheme, p = 0, and an empty index set are admitted.
For an empty index set the cover equality requires the whole space to be empty,
as in the source. There are no characteristic, field, Noetherian, separatedness,
nonemptiness, or finiteness binders. All universe variables are explicitly bound;
u is arbitrary and shared by Scheme, its module category, and the cover index as
in the established comparison construction. Larger set-sized data use a larger
ambient universe; no fixed small universe is selected.

Independent searches: LeanFinder query "open covering derived global sections
comparison morphism functorial in coefficients" returned eight unrelated open-cover
and global-section declarations. LeanSearch query "injective resolution total complex
canonical map from Cech cohomology to sheaf cohomology" was unavailable (HTTP 500),
recorded as unavailable, not as evidence of absence. Grep with
`cech.*(comparison|natur)|comparison.*cech` in Mathlib, WeilConjectures and lean/Sheaf
found the shared ModuleCechComparison predicate, CechH1MapNatural (only degree one),
AffineModuleCechComparisonNatural (only affine-intersection/quasi-coherent case), and
upstream CechComparison. Read upstream cechComplexFunctorHomologyIso_hom_naturality:
it compares two models of Cech cohomology, not Cech with derived module cohomology.
None replaces this full theorem. No duplicate definition is needed.

No mathematical mismatch remains in the current module, and its correct signature
was retained. Checked the node lean.statement against the authoritative signature
reader and synchronized that field verbatim. The earlier arbitrary-functor/hc issue
belongs to superseded versions, not this file. All four node proof steps are in the
docstring, including acyclicity, finite spectral-sequence filtration comparison,
resolution independence through a lift of identity, and naturality through a lift of φ.
There are no hollow definitions, extra declarations, local notation, or unbound names.
The sole theorem proof is sorry. lcompile.py compiled cleanly (exit 0, 2.5 seconds).
The latest return was a landing-lock failure after reviewer acceptance; this delivery
uses deliver2.py to rebase, preflight and compile on the server as requested there.
