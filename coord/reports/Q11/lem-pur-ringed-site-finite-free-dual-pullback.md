## Worker report

The module `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback` states
`SheafOfModules.finite_free_dual_pullback` with `sorry`. Two transparent helpers expose
Mathlib's module pullback with an explicit adjoint-existence witness and its adjunction-unit
map on sections. They contain real data and no postponed proof. No node statement changed;
no dependency record was repaired and no new node was needed.

Hypothesis and clause correspondence:

- Sites small relative to sheaves: `C D : Type u`, `Category.{v}`, with rings, module
  sections, Hom sections and cover indices in `max u v w`. The independent `v` permits
  different site object and morphism universes. Increasing `w` gives any larger common
  sheaf bound. Grothendieck topologies `J K` encode the sites and their covering sieves.
- Finite limits: `HasFiniteLimits C`, `HasFiniteLimits D`; their preservation is
  `PreservesFiniteLimits U`. Preservation of coverings is `CoverPreserving J K U`.
  `U.IsContinuous J K` supplies the associated sheaf pushforward interface; it follows
  from these hypotheses, rather than imposing a restriction on the morphism of sites.
- The associated geometric inverse image is represented by its adjoint module interface.
  `R S : Sheaf ... CommRingCat` are the coefficient ring sheaves. The map `a : R → u_* S`
  after forgetting only commutativity is exactly the adjunct of the stated `c : f⁻¹R → S`.
  A ring morphism between commutative rings is exactly a morphism in `RingCat` between
  their images; no coefficient action is omitted or chosen separately.
- The module inverse image is `SheafOfModules.pullback a`, exposed by
  `ringedSitePullbackFunctor a hAdj`. This is Mathlib's left adjoint to the specified
  module pushforward. Its sheafified presheaf construction represents the same relative
  tensor pullback. The theorem concludes `∃ hAdj` and does not assume existence of this
  module adjoint. The helper merely passes that witness to Mathlib's API explicitly.
- Modules use the dependency `CategoryTheory.ringedSiteModules`, which unfolds to Mathlib
  `SheafOfModules`. Hom uses the dependency's exact `SheafOfModules.homObj`; the dual is
  `homObj L (unit _)`, where `unit` has sections the coefficient ring itself.
- Finite local freeness is the displayed existential `I V r`: the arrows to `⊤_ C`
  form a covering sieve and every `L.over (V i)` is isomorphic to `free (ULift (Fin (r i)))`
  over the restricted ring. This is precisely the specified cover, with varying ranks.
  Slice sheafification hypotheses are size infrastructure, valid for these small sites;
  they are needed by Mathlib's `free` construction, not additional mathematical properties.
- The conclusion specifies a unique comparison family `δ`. Its source is the pullback
  of `homObj L R`, and its target is `homObj (pullback L) S`. These are morphisms in
  `SheafOfModules`, hence S-linear. Its first conjunct fixes the actual canonical map:
  for every local functional φ and local section m over V, evaluate δ on the two
  adjunction-unit images over U(V). The result equals `a_V (φ_V(m))`. This is the
  adjoint/evaluation construction of Stacks 0GMX, equivalently pulling evaluation through
  the canonical relative tensor comparison and the unit identification. Restricting φ
  and m is allowed because V ranges over every site object. Adjunction-unit images
  locally generate the scalar extension, so this characterization determines the map,
  rather than asserting that an unspecified isomorphism exists.
- Contravariant naturality is the second conjunct:
  `pullback.map (homObjMap b (𝟙 _)) ≫ δ L = δ M ≫ homObjMap (pullback.map b) (𝟙 _)`.
- Isomorphy under exactly the displayed finite-free-cover condition is `IsIso (δ L)`.
- The basis clause is included in the stronger, universally quantified evaluation
  normalization, without choosing or fixing a trivialization: on any cover member
  take φ = e_j^vee and m = e_k. The right side is `a_V (if j = k then 1 else 0)`, hence
  `if j = k then 1_S else 0_S`, exactly δ_jk · 1_S. This uses only that a_V is a ring
  map; there is no flatness hypothesis. Thus the theorem covers every local basis.

Dependency declarations read and used:

- `def-weil-size-convention` is a recorded metatheoretic convention; explicit universes
  implement it and there is intentionally no declaration to import.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: site convention, represented here by
  its associated Grothendieck topology and covering sieves.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`, `CategoryTheory.siteInverseImage_tensor`
  and its coherence declaration: associated exact geometric inverse image (proof import).
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`,
  `SheafOfModules.siteSheafTensorRight`: sheafified sectionwise tensor with separate sizes;
  the pullback is its equivalent adjoint interface, not another tensor definition.
- Mathlib `CategoryTheory.GrothendieckTopology.over`, `CategoryTheory.Sheaf.over`,
  `SheafOfModules.over`, `overFunctor`, `Hom.over`, `overMap`, `overFunctorMap`:
  the Mathlib match of `def-pur-localized-ringed-site`. No missing Lean record is a fault:
  this node is marked `mathlib`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`, `homObjMap`; underlying sections are actual linear maps of
  restricted module presheaves. Evaluation is their component at `Over.mk (𝟙 V)`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`,
  `SheafOfModules.module_pullback_tensor_iso`: canonical relative tensor comparison,
  including its generalized pure-tensor characterization (proof import).
- The further recorded proof declarations are imported: `SheafOfModules.tensorClosed`
  from `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`,
  `SheafOfModules.localize_ringed_site_morphism` from
  `Sheaf.Paper.LocalizeRingedSiteMorphism`, and
  `SheafOfModules.existsUnique_hom_of_cover` from
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.

Source checks: read Stacks `sites-modules.tex`, `remark-pullback-internal-hom` (0GMX),
including its localized morphism description; `example-dual` (0FNY), including the
finite-free local evaluation argument; and the current main-20261015 blueprint's
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, Powers and duals paragraph.

Edge cases: rank zero uses `Fin 0` with no nonempty-index condition; varying ranks need
not be bounded or constant; the zero coefficient ring is allowed; an empty covering
family is allowed whenever the topology admits it; no enough-points assumption is used;
identity and arbitrary coefficient ring maps are included, including nonflat quotients.
The source-site and target-site morphism universes need not equal their object universes.
No STATEMENT-DISPUTED or node fault was found.

Searches, all performed for this item with the prescribed tools:

- msearch LeanFinder, `finite locally free module sheaf dual pullback ringed site`:
  eight hits, principally `pullbackObjFreeIso`, `freeFunctorCompPullbackIso` and their
  normalization lemmas, plus finite presentation. No internal-dual pullback theorem.
- msearch Loogle, `SheafOfModules homObj pullback`: zero hits, unknown `homObj`.
- msearch grep, `dual|homObj|locally free`, `Algebra/Category/ModuleCat/Sheaf`:
  five documentation hits in `LocallyFree.lean`, no comparison.
- msearch LeanSearch, `The canonical pullback internal Hom comparison for finite locally
  free sheaves of modules is an isomorphism`: eight hits on ordinary pullback comparison,
  free-sheaf pullback and unit adjunction normalization; no exact match.
- rg over `WeilConjectures/` and `lean/Sheaf` for `dual.*Pullback`, `pullback.*Dual`,
  `homObj.*pullback`, `pullback.*homObj`, `finiteLocallyFree`, `IsFiniteLocallyFree`:
  internal Hom restriction and specialized scheme/étale dual theorems exist; none states
  this ringed-site result. Read upstream `InternalHom.lean`, presheaf `InternalHom.lean`,
  `Mathlib/.../Sheaf/LocallyFree.lean`, upstream finite-locally-free definitions, and
  Mathlib `PullbackContinuous.lean`, `PullbackFree.lean`, `PushforwardContinuous.lean`.
- rg for the exact item id in the upstream source: no attachment.
- rg in `dag/lean_names_upstream.json`, Mathlib, upstream and `lean/Sheaf` for
  `ringedSitePullbackSection`, `ringedSitePullbackFunctor`, `finiteFreeDualPullback`:
  no existing declaration with these names.

Validation: scompile.py compiled the entire delivered module cleanly, once for the initial
statement and again after moving adjoint existence into the conclusion. Final validation
and delivery use the same prescribed wrapper and server preflight.

## Second reading by Q11

Author self-check under the dispatcher brief; independent mathematical review is supplied
by the maintainer, and no other worker was spawned. Re-read the original node and the Lean
side by side. The first draft accidentally assumed the module pushforward was a right
adjoint. Changed this to an existential conclusion, exposed the exact Mathlib pullback
with an explicit witness, and retained the section map as real adjunction-unit data.
The evaluation equation fixes the comparison and includes the basis normalization; the
map is S-linear by its hom type. Naturality has the contravariant orientation, and
isomorphy is conditional on exactly a terminal covering family of finite free restrictions.
The statement uses no fixed rank, flatness, nonempty cover, nonzero ring or universe
identification of objects with morphisms. The helpers and theorem carry source/blueprint
docstrings, all universes and variables are explicit, and the theorem proof is only sorry.
