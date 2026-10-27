## Worker report

Item: det-thm-groth-ss. Existing attachment; no Lean module is added. Only the
item's `lean` field changes. Its statement, statement dependencies, proof and
proof dependencies remain verbatim.

The current blueprint explicitly names the following three declarations, all
present in the live source and checked together on the server:

- `CategoryTheory.Functor.exists_grothendieckSpectralSequence`, defined in
  `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`, lines 754–785.
- `CategoryTheory.Adjunction.isAcyclicComposablePair`, in the same module,
  lines 117–129.
- `AlgebraicGeometry.Scheme.Modules.exists_leraySpectralSequence`, defined in
  `WeilConjectures.AlgebraicGeometry.Cohomology.Leray`, lines 83–103.

The recorded import module is `WeilConjectures.AlgebraicGeometry.Cohomology.Leray`.
It publicly imports the Grothendieck module, so all three declarations are
available from this one import. The primary record names
`AlgebraicGeometry.Scheme.Modules.exists_leraySpectralSequence`, which is declared
in this module. `lean.statement` is its exact signature, extracted from its
source before `:= by`, with its original newlines. The abstract theorem and
adjunction criterion are also listed in `lean.declarations`. Below, "primary
abstract declaration" refers to Functor.exists_grothendieckSpectralSequence.

Sources read: the statement and proof of det-thm-groth-ss in
`literature/blueprint/latest/blueprint/sec-picard-framework/sk-thm-picard-perfect/`;
`derived.tex`, lemma-grothendieck-spectral-sequence (015N);
`sites-cohomology.tex`, lemma-Leray (0732) and lemma-relative-Leray (0734);
`cohomology.tex`, lemma-Leray (01F2). The primary theorem's docstring explicitly
includes the relative site sequence and its punctual-site specialization. The
module Leray theorem identifies its sequence as the Grothendieck sequence of
module direct image followed by global sections. The old sk-thm-groth-ss node,
whose mathematical statement is identical after the definition-node rename,
already has the primary declaration in its closed upstream audit.

### Hypotheses and conclusions

1. Categories A and B are independently universe-polymorphic categories with
   `[Abelian A]`, `[Abelian B]`, and `[IsGrothendieckAbelian.{v₁} A]`,
   `[IsGrothendieckAbelian.{v₂} B]`. These are the surrounding variables of the
   abstract declaration. They supply injective resolutions. C has its own object
   and morphism universes and only `[Abelian C]`; no Grothendieck, injective or
   derived-category hypothesis on C is imposed. The theorem chooses standard
   derived categories internally.
2. `F : A ⥤ B`, `G : B ⥤ C` render Phi and Psi, with `[F.Additive]`,
   `[G.Additive]` and `[PreservesFiniteLimits F]`, `[PreservesFiniteLimits G]`.
   These are exactly additive left exact functors between abelian categories,
   as recorded by def-sp-left-exact-additive.
3. `hFG : F.IsAcyclicComposablePair G` is precisely det-def-groth-ss:
   for every injective I and every positive natural q,
   `IsZero ((G.rightDerived q).obj (F.obj I))`. No acyclicity assumption is
   placed on the particular input object.
4. `(X : A)` is arbitrary. The existential
   `∃ E : E₂CohomologicalSpectralSequenceNat C` gives the first-quadrant
   cohomological sequence starting at page two. Natural-number bidegrees encode
   the first quadrant. Its pages, differentials and successive homology
   isomorphisms are supplied by the existing spectral-sequence type.
5. The clause for every `p q : ℕ` is exactly
   `Nonempty ((E.page 2).X (p, q) ≅
     (G.rightDerived p).obj ((F.rightDerived q).obj X))`.
   Thus the second-page indices and functor order match the displayed formula.
6. `E.AbutsTo (fun n ↦ ((F ⋙ G).rightDerived n).obj X)` is the displayed
   abutment in total degree n. The recorded `SpectralSequence.Abutment` has
   subobjects `filtration n p`, decreasing successor inclusions, top at zero,
   bottom at n+1, and quotient isomorphisms to `pageInfinity (p,q)` when
   p+q=n. `pageInfinity` is page p+q+2. This is the convergence notion required
   by det-def-groth-ss, with no degeneration assumption.
7. For the relative site clause, instantiate A, B, C by abelian sheaves on
   X, Y, Z, and F, G by their direct images f-star and h-star. The dependency
   convention makes these sectionwise precomposition functors
   `U.sheafPushforwardContinuous AddCommGrpCat J K`. They are additive and
   left exact. Their actual left adjunctions are
   `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`; exactness of
   inverse image supplies `PreservesFiniteLimits` of the left adjoint.
   The listed `Adjunction.isAcyclicComposablePair adj G` then supplies hFG.
   This is exactly the node's reason that f-star preserves injectives and hence
   sends injectives to h-star-acyclic objects. The abstract sequence now reads
   `R^p h_* (R^q f_* F)` with abutment `R^n(f_* ⋙ h_*) F`.
   Under the dependency's composition convention the composite site functor is
   `V ⋙ U`, and its direct image is this composite; the same object is therefore
   `R^n(hf)_* F`. This specializes the primary theorem, not an extra assumption
   that f-star itself be exact.
8. For the punctual-site clause, the target abelian-sheaf category is abelian
   groups. The functor h-star is evaluation at the image of its unique object,
   namely Gamma(Y,-) in the node; its composite with f-star is Gamma(X,-).
   Substituting these functors in clauses 5 and 6 gives
   `R^p Gamma(Y,-)(R^q f_* F) => R^n Gamma(X,-)(F)`.
   The cohomology convention of def-weil-pbc-sites-and-cohomology identifies
   these right derived functors with the displayed H^p and H^n. When a site
   lacks a final object, the notation here is the evaluation specified by the
   morphism to the punctual site, as in the node's accepted proof step 4;
   no final-object hypothesis is added to the relative site theorem.
9. For a scheme, use its recorded `smallEtaleTopology` or
   `Opens.grothendieckTopology` on the underlying space. Base change on etale
   objects and inverse image on opens give the site functors in clause 7.
   These are still abelian sheaves, and there is no torsion or fixed-ring
   restriction. Composition of the etale base-change functors has the canonical
   pullback-associativity isomorphism; on opens inverse images compose.
   Both sites have their stated final object, so clause 8 gives the scheme
   Leray formulas. The primary theorem and its adjunction criterion are
   polymorphic in these sheaf categories, including their distinct site
   object and morphism universes.
10. The last clause concerns modules on the small Zariski sites.
    `Scheme.Modules.exists_leraySpectralSequence f F` is exactly the existing
    module version named by the blueprint. Its input is `F : X.Modules`, the
    recorded `SheafOfModules (moduleRings X.toRingedSpace)` category. Its second
    page is the right derived global-sections functor on Y applied to
    `(Scheme.Modules.higherDirectImage f q).obj F`, and its abutment is derived
    global sections on X. `higherDirectImage f q` is, by definition,
    `(Scheme.Modules.pushforward f).rightDerived q`.
    `Scheme.Modules.pushforward_comp_globalSectionsFunctor f` is the equality
    of the composite with global sections on X, on objects and morphisms.
    The server checked by `rfl` that `Scheme.Modules.pushforward f` is the
    dependency's `RingedSpace.moduleDirectImage f.toLRSHom.toShHom`.
    Thus it uses exactly the module direct image already recorded in the DAG.
    Its `HasInjectiveResolutions` parameters are supplied by installing the
    existing `Scheme.Modules.isGrothendieckAbelian X` and Y, then instance
    synthesis; this was checked, without assuming resolutions, in a consumer
    probe. Restricting its arbitrary f and F to `[IsProper f]` and
    `RingedSpace.IsCoherent X.toRingedSpace F` gives precisely the final case
    in the node. Properness and coherence are not needed by the construction.
    This theorem views the result in abelian groups. If its natural
    Gamma(Y,O_Y)-module structure is retained, use the same primary theorem
    with C that module category and G the recorded
    `RingedSpace.globalSectionsFunctor Y.toRingedSpace`; its acyclicity is
    `Scheme.Modules.module_pushforward_injective_acyclic`. This retains the
    scalar restriction described in the node's proof step 6.

### Dependency declarations read and used

- det-def-groth-ss: `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`,
  `Functor.IsAcyclicComposablePair`; and
  `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic`,
  `SpectralSequence.pageInfinity`, `SpectralSequence.Abutment`, `AbutsTo`.
  The actual definition does not require C to be Grothendieck.
- def-weil-pbc-sites-and-cohomology:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `Precoverage.IsSiteForCoverings`; the retained `Precoverage.toGrothendieck`,
  `Sheaf`, `Sheaf.H'` and `cohomologyPresheafFunctor` convention. The site
  specializations use this existing notion; no precoverage structure is copied.
- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `Scheme` and `Scheme.Hom`.
- def-weil-sheaf-of-modules-category:
  `Sheaf.CategoryTheory.RingedSiteModules`, `ringedSiteModules`, transparently
  `SheafOfModules`; its sectionwise linear morphisms and abelian structure
  are Mathlib's.
- def-sc-ringed-space-module-cohomology:
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`,
  `RingedSpace.globalSectionsFunctor` and `moduleCohomology`.
- def-pc-ringed-spaces-derived-direct-image:
  `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`,
  `RingedSpace.moduleDirectImage` and `derivedModuleDirectImage`.
  For a degree-zero sheaf the higher direct images are the right derived
  functors of the former, as in pqf-def-cohomology.
- def-sp-grothendieck-abelian:
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`,
  `IsGrothendieckAbelian` (AB5 and separator, with its colimit instance).
- def-sp-left-exact-additive:
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`, `Functor.Additive`;
  `Mathlib.CategoryTheory.Limits.Preserves.Finite`, `PreservesFiniteLimits`;
  `Mathlib.CategoryTheory.Abelian.RightDerived`, `Functor.rightDerived` and
  `InjectiveResolution.isoRightDerivedObj`.
- def-sc-zariski-site: `Mathlib.CategoryTheory.Sites.Spaces`,
  `TopologicalSpace.Opens.grothendieckTopology`; `TopCat.Sheaf` is the
  corresponding sheaf category.
- def-weil-pbc-etale-site: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `Scheme.smallEtaleTopology`, with `Scheme.Etale` and its finite limits.
- pqf-def-cohomology: `WeilConjectures.AlgebraicGeometry.PQFCohomology`,
  `sheafCohomologyAndHigherDirectImages`; this relates the recorded unbounded
  derived direct image on a sheaf in degree zero to the same ordinary
  `Functor.rightDerived` higher direct images used here.
- pqf-def-coherent: `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly
  exposes `WeilConjectures.AlgebraicGeometry.Coherent`,
  `RingedSpace.IsCoherent`, the finite-type and finite-type-kernel condition.
  It also retains `IsQuasiCoherentFiniteType`, `IsQuasicoherent`, `IsFiniteType`.
  The final clause is the specialization to the actual coherence predicate.
- def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (separated, universally closed, locally of
  finite type, with quasi-compactness supplied by universally closed).

### Edge cases

Checked the first-quadrant boundary p=0, q=0 and total degree n=0: the recorded
abutment filtration is H^0=F^0 with F^1=0, so its only quotient is E-infinity
at (0,0); the stable-page index is 2, as required. Positive derived functors
are required to vanish only on images of injectives, not on arbitrary sheaves.
The zero object, zero functors, zero categories, empty scheme and arbitrary
nonproper/noncoherent inputs to the general clauses introduce no new condition.
The proper coherent sentence is an in-particular use of the module theorem,
not a properness condition on the abstract or site clauses. No nonempty space,
characteristic, torsion coefficient, bounded dimension or independent upper
cohomological bound is introduced. The target category C need not have enough
injectives. The abstract theorem keeps all six category universes independent.

### Searches and validation

All searches below were actually run for NY/det-thm-groth-ss; their wrapper log
is `searches.jsonl` in the sandbox.

- msearch leanfinder: "Grothendieck spectral sequence of composable left exact
  additive functors and Leray spectral sequence": 8 hits, including Ext maps
  and exact functors; no exact Mathlib spectral-sequence theorem.
- msearch loogle: "CategoryTheory.Functor.rightDerived,
  CategoryTheory.SpectralSequence": 0 hits.
- msearch grep: "grothendieckSpectralSequence|leraySpectralSequence": 0 hits
  in Mathlib.
- msearch leansearch: "Grothendieck spectral sequence composite left exact
  functors sending injectives to acyclic objects": 8 hits, including
  `Functor.preservesInjectiveObjects_comp` and
  `Functor.sheafPushforwardContinuousComp`; no exact Mathlib theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `exists_grothendieckSpectralSequence|exists_leraySpectralSequence|leraySpectralSequence`
  found the upstream declarations attached here, plus the stronger
  Cartan--Eilenberg theorem and other Leray consumers. Their full signatures
  and docstrings were read. The stronger Sheaf Cartan--Eilenberg declaration
  is not used: it requires Grothendieck C and asserts additional model data.
- `grep -rn det-thm-groth-ss lean/WeilConjectures` returned no id match;
  the reusable declarations retain the older sk-thm-groth-ss/pqf-lem-leray ids.
- DAG search found src-grothendieck-spectral-sequence-nat and the old
  sk-thm-groth-ss attachment to the primary theorem. This confirms reuse.
- scompile compiled `scratchpad/ExistingChecks.lean` in sandbox and module
  visibility, with one import of the recorded module. All three attached
  declarations, the acyclicity definition and abutment definitions were
  successfully checked with their full implicit parameters.
- The module-interface probe checked the direct-image equality by `rfl` and
  applied module Leray after supplying the intrinsic Grothendieck instances.
  An initial missing inferred resolution instance was repaired by explicitly
  installing `Scheme.Modules.isGrothendieckAbelian`; no hypothesis was added
  to the item. A scratch-probe letI style warning was repaired as suggested.

No new nodes, dependency repairs, statement correction or disputed statement.
The first dry run compiled all recorded names but required the primary
declaration to be physically declared in its recorded module. The record was
repaired to name the module Leray theorem as primary, with the abstract theorem
and adjunction criterion retained in `lean.declarations`; all three declarations
and all mathematical clauses are unchanged.

The prescribed delivery tool supplies the second-reading placeholder; this
worker makes no claim to an independent review.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
