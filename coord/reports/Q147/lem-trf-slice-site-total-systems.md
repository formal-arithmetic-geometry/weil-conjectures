## Worker report

The module `Sheaf.CategoryTheory.TotalSiteSheafSystems` states
`CategoryTheory.CoherentSitePseudofunctor.totalSite_sheaf_systems` with one postponed
proof. All definitions have real data, obtained from the recorded coherent total-site
interface and Mathlib's sheafified left Kan extension and adjunction-mate constructions.
No source statement, statement dependency, proof, or proof dependency was changed.
No independent missing notion or unusable dependency needed a new node or repair.
The system object, component morphisms, and presentation are helpers belonging to the
compatible-system equivalence itself, and are listed in `lean.declarations`.

The hypothesis and clause correspondence is as follows.

- A small category is `{I : Type u} [Category.{v} I]`. Universes `u`, `v`, and `w`
  are explicit; the statement imposes no equality between the base and fibre sizes.
  Fibres use exactly the dependency's `F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w,w}`.
- The coherent contravariant pseudofunctor of sites is
  `D : CoherentSitePseudofunctor I F`, with its actual `coverage`, `site`,
  `continuous`, and `preservesCoverPullbacks` fields, rather than a strict diagram.
  The total category and topology are exactly `Pseudofunctor.CoGrothendieck F`
  and `D.totalTopology` from the recorded dependency.
- The additional morphism-of-sites assumption is exactly
  `∀ (i j : I) (α : i ⟶ j), PreservesFiniteLimits (D.inverseImage α)`.
  No finite-limit preservation of the underlying site functor, global pullbacks,
  invertible transitions, or other extra hypotheses are imposed.
- `D.fibreSheaves i` is `Sheaf (D.coverage i).toGrothendieck (Type w)`.
  `D.directImage α` is Mathlib's `sheafPushforwardContinuous` for the supplied
  continuous site functor, so it is precomposition with `u_α`.
  `D.inverseImage α` is the recorded dependency's
  `Functor.sheafPullbackConstruction.sheafPullback`, the sheafified left Kan
  extension; `D.imageAdjunction α` is its actual adjunction.
- A system's sheaves `F_i` are `SheafSystem.obj`; its maps
  `t_α : f_α⁻¹ F_j ⟶ F_i` are `SheafSystem.transition`. There is deliberately
  no `IsIso` field or hypothesis on these maps.
- `SheafSystem.transition_id` inserts `D.inverseImageId i`.
  `SheafSystem.transition_comp` is exactly
  `a_αβ ≫ t_(α≫β) = L_α(t_β) ≫ t_α` at `F_k`.
  Here `inverseImageId` uses `Adjunction.leftAdjointIdIso`, and
  `inverseImageComp` uses `Adjunction.leftAdjointCompIso` on the explicit
  `imageAdjunction`s. The direct-image isomorphisms are induced from the
  actual `F.mapId` and `(F.mapComp β.op.toLoc α.op.toLoc).symm` by
  `sheafPushforwardContinuousId'` and `sheafPushforwardContinuousComp'`.
  Thus these are precisely the canonical adjunction-compatible comparisons,
  including their orientation, rather than unspecified comparison isomorphisms.
- The category of systems is specified by its actual objects `SheafSystem`
  and its actual Hom families `SheafSystemHom`: `app` gives one component map,
  and `comm` says `L_α(h_j) ≫ t^Y_α = t^X_α ≫ h_i`. Its usual identities and
  composition are componentwise. The statement uses the fully faithful and
  essentially surjective presentation criterion for equivalence, as in the
  already recorded `TotalSiteSystemData` interface, avoiding additional
  postponed category-law lemmas.
- `SheafSystemPresentation.system` sends each actual total sheaf to a system;
  `restriction` identifies its fibre presheaf with precomposition along the
  actual non-strict vertical embedding `CoGrothendieck.ι F i`.
  `map_restriction` fixes each component of `map` to the whiskered total-sheaf
  morphism. These equalities imply preservation of identities and composition:
  at every fibre they are the usual presheaf restriction functor equations,
  and a compatible Hom is determined by its component maps.
- `transition_restriction` fixes the adjoint of each transition at every
  object `V` to `X.obj.map (CoGrothendieck.cartesianLift V α).op`.
  This is the source's canonical arrow `(α,id)`, whose domain is `(i,u_α V)`.
  `HEq` compares the same restriction functions at the endpoints identified
  by `restriction`; it adds no mathematical condition beyond these formulas.
- `map_bijective` identifies each total-sheaf Hom with ALL compatible component
  families, not a selected subclass. `essentially_surjective` realizes EVERY
  compatible system up to component isomorphisms intertwining the transitions.
  Together with the fixed restriction formulas these are exactly the claimed
  equivalence, with fibre evaluation specified. A compatible component
  isomorphism has a compatible inverse by the displayed compatibility equation.

The main docstring records all seven proof steps of the node: direct images and
canonical mates; adjoint cocycles; restriction and the fibre sheaf condition;
Cartesian-lift transitions; reconstruction along arbitrary total arrows;
gluing on all pullbacks of generating vertical covers; and the inverse
object/morphism constructions. The sole `sorry` is the main theorem.

Dependencies read and used:

- `Sheaf.CategoryTheory.TotalSitePseudofunctor`:
  `CategoryTheory.CoherentSitePseudofunctor`, its `totalTopology`,
  `verticalArrows`, and `totalSite_of_coherent_pseudofunctor`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, imported publicly through
  the total-site module and retained in `D.site`.
- `def-weil-size-convention` is metatheoretic; the explicit universe binders
  implement it, as its recorded convention instructs.
- `Mathlib.CategoryTheory.Sites.Pullback`:
  `Functor.sheafPullbackConstruction.sheafPullback` and
  `sheafAdjunctionContinuous` (the exact recorded pullback-adjunction match).
- `Mathlib.CategoryTheory.Sites.Continuous`:
  `Functor.sheafPushforwardContinuous`, `sheafPushforwardContinuousId'`,
  `sheafPushforwardContinuousComp'` (available through `Pullback`).
- `Mathlib.CategoryTheory.Sites.LeftExact` supplies the standard sheafification
  existence instances for the chosen small fibre sites and set universe.
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`:
  `Adjunction.leftAdjointIdIso`, `leftAdjointCompIso`, and the recorded proof
  dependency `leftAdjointCompIso_assoc`; the same import exposes the recorded
  `unit_conjugateEquiv_symm` and `Adjunction.comp` proof interfaces.
- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`:
  `Precoverage.isSheaf_toGrothendieck_iff`, already imported publicly by the
  total-site module and used in the documented proof plan.
- `WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf`:
  `CategoryTheory.siteContinuous_pushforward_isSheaf`, imported only for the
  recorded proof dependency. Its full current source was read using
  `scompile.py --source`, since it was absent in the older local checkout.

The source was checked directly in `literature/stacks-project/spaces-simplicial.tex`,
Case A and Tags 09WC/09WF, including the pre-lemma description of adjoint maps
and morphisms. The node already explicitly assumes left exactness of inverse
images; the continuity-only issue mentioned in its stage-1 split report is
therefore addressed in the statement being formalized. No statement dispute remains.

Edge cases checked: an empty base category yields empty compatible families and
the unique empty-site sheaf; empty fibres and empty generating covers are not
excluded; fibre sheaf gluing handles empty covers. Identity arrows retain the
non-strict `F.mapId` comparison. Composite arrows use `F.mapComp β.op α.op`
with the contravariant order checked against the CoGrothendieck source.
No arbitrary pullbacks of the base or total category are assumed. A one-object
base with only the identity reduces to its fibre sheaves. Arbitrary noninvertible
transitions remain permitted. Base object and morphism universes remain independent
from the fibre universe inherited from the dependency.

Searches performed using the prescribed wrapper:

- `leanfinder`: "sheaves on total site equivalent to systems of sheaves
  transition maps" returned eight generic sheaf and sheaf-equivalence results;
  none describe compatible systems on a total pseudofunctor site.
- `loogle`: "Sheaf, GrothendieckTopology, Equivalence" returned no hits
  (`unknown identifier 'Sheaf'`).
- `grep` in Mathlib `CategoryTheory`: "totalSite|CoherentSitePseudofunctor|compatible"
  returned general compatibility results, not this theorem.
- `leansearch`: "sheaves on Grothendieck total site equivalence compatible
  systems arbitrary transition maps" returned general `Sheaf`, dense-subsite,
  and sheaf-congruence results; no total-site system equivalence.
- `grep` in Mathlib `CategoryTheory/Sites`: "total.site|totalSite|SheafSystem"
  returned zero hits.
- Direct `rg` in the upstream `WeilConjectures` source for the node id returned
  no hit; conceptual searches of that source, the upstream-name index, and
  `lean/Sheaf` found the existing total-site construction and the separate
  simplicial *abelian* `TotalSiteCompatibleSystem`/`TotalSiteSystemData` of
  `Sheaf.TraceFormula.TotalSiteComponentRestriction`. The latter fixes the
  index category to `SimplexCategoryᵒᵖ` and requires abelian/preadditive data,
  so it cannot encode systems of SET sheaves over arbitrary `I` here.
  No private copy of that specialization is introduced. The scheme-specific
  `compatiblePullbackSheafSystem` concerns a different notion.
- Direct exact-name searches in Mathlib, upstream `WeilConjectures`, and
  `lean/Sheaf` found no `SheafSystemPresentation`, `SheafSystemHom`, or
  `totalSite_sheaf_systems` declaration in this namespace.

Validation: the prescribed `scompile.py Q147 lem-trf-slice-site-total-systems`
compiled the module both as a sandbox file and under its library module path
without errors or unexpected warnings. The first drafts' instance-resolution
and whiskering-name errors were repaired before that clean check. The final
self-contained theorem binders are checked again by the delivery dry run.

## Second reading by Q147

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
