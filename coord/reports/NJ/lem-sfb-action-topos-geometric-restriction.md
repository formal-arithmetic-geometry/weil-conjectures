## Worker report

This is the stage-2 statement of `lem-sfb-action-topos-geometric-restriction`, in
`Sheaf.CategoryTheory.ActionToposGeometricRestriction`. The main declaration is
`CategoryTheory.InternalActionSite.geometricRestriction`. It asserts existence of the
fully specified `GeometricRestriction` data; no data is selected from this theorem.
All theorem proofs are `sorry`. Definitions contain actual data and refer to named
theorems only for proof obligations. All 21 declarations are listed in `lean.declarations`.

The earlier dispatcher blocker was mistaken: the NR merge at ledger line 23266 is
stage 1. Its report says explicitly that it delivered no Lean files, and the live node
has `reviewed` but no `lean` or `reviewed_lean`. This delivery supplies the still missing
stage-2 statement. It does not repeat or change NR's split.

Hypotheses and clauses, in the node's order:

* The fixed universe is `universe u`. The site is `C : Type u` with `[SmallCategory C]`,
  `J : Precoverage C`, `hJ : J.IsSiteForCoverings`, and `[HasFiniteLimits C]`. Both site
  objects and arrows, group sections, ring sections and module sections lie in `u`.
  The categories of sheaves and actions live in the corresponding larger universe.
* `K L : Cᵒᵖ ⥤ GrpCat.{u}` with the explicit underlying-set sheaf conditions `hK`, `hL`
  give exactly the group sheaves. A morphism `θ : L ⟶ K` is sectionwise a group homomorphism
  and is natural for all base restrictions.
* `groupSheaf` is the existing underlying set presheaf with the supplied sheaf proof.
  `groupOne` and `groupMul` are the actual sectionwise group operations; `groupMonoid`
  uses these operations and the named law theorem. `SetActions` is Mathlib's `Mod` in
  the cartesian monoidal category of sheaves. Thus its data are a sheaf action morphism
  with the unit and associativity diagrams, and its morphisms are equivariant sheaf maps.
  This reuses Mathlib's internal-action notion instead of introducing another category.
* The category `C_K`, arrows, composition, topology and `opArrow` are the dependency's
  actual `Object K`, `Arrow K`, `category`, `topology K J`, and `opArrow K`. They are not
  copied. `GeometricRestriction.equivalence` is the set-valued sheaf equivalence.
  `sections`, `action_restriction`, and `morphisms` say precisely that its sections and
  maps are unchanged and its restriction is `a · f* x`. `setAction` evaluates the actual
  internal action morphism. `topos` uses the recorded `IsGrothendieckTopos.{u}` predicate.
* `restrictionSite θ` sends `(f,a)` to `(f,θ(a))` and keeps the base object. `restriction`
  is actual precomposition along its opposite, lifted to the full category of sheaves.
  Under the displayed equivalence its section formula is restriction of the action.
  `restriction_adj` states that it has a right adjoint (`IsLeftAdjoint`);
  `restriction_limits` states finite-limit preservation. Together these are exactly the
  geometric morphism `q_θ` in the direction in the node.
* `inflation` is actual precomposition along the dependency's `projection K`, hence
  ignores labels. `inflation_adj`, `inflation_limits`, and `inflation_trivial` state the
  geometric morphism `p_K` and its trivial action. `over_base` is equality of the entire
  inverse-image functors on sheaves and maps, specifying the identity geometric
  comparison `p_K q_θ ≅ p_L`; its right-adjoint mate is unique. `identity_restriction`
  and `composition_restriction` are literal functor equalities, including their action
  on maps. Equality comparisons give the canonical coherent identifications.
* For arbitrary `R : Sheaf J.toGrothendieck CommRingCat.{u}`, `inflation_modules` and
  `restriction_modules` supply `PrecompositionPullback` data on the base/action sites.
  `pulledCoefficient` is the actual precomposed coefficient presheaf with its sheaf
  proof. For projection it is the dependency's `coefficientSheaf K J hJ R`; for label
  change applied to that coefficient it is `coefficientSheaf L J hJ R`, with identical
  section rings and restrictions (proof fields are irrelevant). `baseRing` is the
  dependency's existing commutative-ring-to-ring sheaf abbreviation.
* Each package contains the recorded `RingedToposMorphism`, its literal inverse-image
  equality, and `structural`, which makes the structural ring map the identity under
  that equality. It includes the actual induced module pullback: `ModulePullback`
  gives the adjunction to the ringed morphism's already specified induced module
  direct image, and `normalization` identifies its Hom correspondence with the given
  sheaf adjunction. Thus it cannot mean an arbitrary module functor or adjunction.
* `PrecompositionPullback.sections` gives sectionwise linear equivalences;
  `restrictions` and `morphisms` identify all restriction and component maps with the
  original ones along the specified site functor. For projection these are trivial
  inflation; for label change they are exactly restriction along `θ`. `additive`,
  `limits`, and `colimits` state additivity and preservation of finite limits and
  colimits, hence exactness on these abelian module-sheaf categories.
* `tensor` is an isomorphism for the recorded sheafified sectionwise tensor, using
  `siteSheafTensorRight`. `tensor_pure` specifies it on the actual sheafification-unit
  pure tensors `siteSheafTensorTmul`: `x ⊗ y` maps to `x ⊗ y` under the section
  identifications. The tensor's restrictions act on both factors, so this is the
  stated diagonal action. Its naturality is fixed by `morphisms` and these pure tensor
  equations: locally pure tensors generate, and the comparisons are sheaf maps.
  `unitComparison` and `unit_sections` make the comparison the identity on the regular
  coefficient module, with no unspecified unit scalar.
* A coefficient map `φ : R ⟶ R'` is sent to the same componentwise map by the actual
  `inflation ... CommRingCat` functor. `CoefficientChange` is the identity geometric
  morphism with structural map exactly `φ`, in direction `(E,R') → (E,R)`.
  `coefficient_base` and `coefficient_action` provide these vertical morphisms.
  `over_base_rings` and `coefficient_square` state their commutation with restriction,
  using the equality-induced identity comparison. For the square with `p_K`, its
  inverse image is literally inflation and its coefficient map is literally inflation
  of `φ`, so the same structural square is built into these definitions. Since every
  horizontal structural map is the identity, these equalities specify the commuting
  ringed squares, with identity comparison on the underlying sheaves.

Dependency declarations read and used:

* `def-weil-size-convention`: its `lean.convention` record is metatheoretic; explicit
  universe binders implement it, and no nonexistent Lean declaration is imported.
* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the base topology is Mathlib's
  `Precoverage.toGrothendieck` and sheaves are Mathlib's `Sheaf`.
* `Sheaf.CategoryTheory.InternalActionSitePresentation`:
  `CategoryTheory.InternalActionSite.Object`, `Arrow`, `category`, `projection`,
  `opArrow`, `topology`, `coefficientSheaf`, `baseRing`, and the `Presentation` /
  `presentation` interface (including its sectionwise module equivalence and
  kernel/cokernel and sheafification clauses). The recorded module also supplies
  `topology_mem_iff`, used in the natural-language proof.
* `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`,
  including its set adjunction, finite-limit preservation, structural ring map,
  induced additive module direct image and natural underlying-set comparison.
* `Sheaf.CategoryTheory.Sites.GrothendieckTopos`: `CategoryTheory.IsGrothendieckTopos`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  exact abbreviation for Mathlib `SheafOfModules` on a general site.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded tensor
  interface, whose public imports provide `SheafOfModules.siteSheafTensorRight` and
  `SheafOfModules.siteSheafTensorTmul` from `SiteTensorFunctoriality`. These use the
  existing sheafification tensor, rather than a second construction.
* Proof imports are the recorded `Sheaf.CategoryTheory.SetSheafCoverDescent` and
  `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`, plus Mathlib's
  `Sheaf.PushforwardContinuous` and `Presheaf.Sheafification`. The last two give the
  recorded localized-site restriction and module-sheafification notions.

Sources read: the full node and all statement-dependency records and their source
declarations; the current blueprint direct-images proof paragraph (3); Stacks
`sites.tex`, `lemma-glue-maps` (04TQ), and `proposition-sheaves-on-group` (00W0).
The blueprint paragraph does not itself state the internal-group infrastructure;
the node correctly labels it as agent-formulated. 00W0 is only the ordinary-group
special case and is not claimed as a reference for the internal-group theorem.
The inherited request for a full non-SGA internal-group reference remains as recorded.

Edge cases checked before completing the statement:

* On the point site the formula is ordinary restriction of group actions and the
  usual coinduction `F(θ(l)k)=lF(k)` with right-translation action.
* `θ = id` and successive restrictions use literal identity/composition functor
  equalities. Neither injectivity nor surjectivity of `θ` is assumed.
* If `L = 1`, restriction forgets the action; if `K = 1`, restriction and `p_K`
  give trivial actions. Empty action sheaves and empty section sets are permitted.
* Empty covers use the original generated topology, not an inhabited-cover variant.
  A base site with finite limits and a degenerate sheaf topos is permitted.
* Zero coefficient rings and zero modules are permitted. All tensor and unit section
  formulas still make sense; no faithful/nonzero coefficient hypothesis was added.
* The source's independent choices of site/group/ring inside the fixed universe
  remain unrestricted; `Type u` values and a genuinely small site are exactly the
  stated size bound. No large/small-site universe equality has been imposed on a
  statement that originally allowed different bounds.

Searches for an existing statement or notion:

* `msearch.py` LeanFinder, query “restriction along a morphism of internal sheaves of
  groups is inverse image of a geometric morphism of topoi of actions”: 8 unrelated
  restriction and sheaf-Hom hits; no match.
* `msearch.py` Loogle, query `CategoryTheory.Action, PreservesFiniteLimits,
  SheafOfModules`: no hits; `CategoryTheory.Action` is unknown.
* `msearch.py` grep, query `structure.*Action|def.*[Aa]ction|internal.*action` in
  `CategoryTheory/Monoidal`: 24 hits, including Mathlib `ModObj`, `Mod`, and trivial
  actions. These were read and reused for `SetActions`, rather than copied.
* `msearch.py` LeanSearch, query “Internal group sheaf actions restriction geometric
  morphism sheaf category”: 8 hits on general sheaves and scalar restriction, with no
  internal-group geometric restriction statement.
* `rg` in Mathlib's monoidal and site modules found the exact existing internal module
  object and cartesian sheaf machinery; it supplies the notion but not this theorem.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for internal actions,
  `InternalAction`, `ActionTopos`, and `geometricRestriction`, and the exact node id in
  the upstream source: no existing theorem. The action-site dependency and condensed
  module-only specializations were found and inspected. Neither states this general
  set-valued equivalence and ringed restriction result.
* Exact declaration-name searches in `dag/lean_names_upstream.json`, `WeilConjectures`
  and `Sheaf` found no collision for the declarations in this module.

No new nodes, dependency record changes, statement correction, or disputed statement.
The item's only changed field is `lean`.

Validation: compiled through the prescribed `scompile.py` wrapper in sandbox and final
module mode. The first dry run caught an unused implicit binder name in a definition;
it was renamed `_Y`, preserving the type and construction. The clean dry run passed
server compilation and maintainer preflight at commit `7445940a89a`; nothing was pushed
by that dry run. The delivery wrapper repeats these checks for the final packet.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
