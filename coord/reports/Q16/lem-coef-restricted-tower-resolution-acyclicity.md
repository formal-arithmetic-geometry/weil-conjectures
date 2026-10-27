## Worker report

Stage 2 statement delivery for lem-coef-restricted-tower-resolution-acyclicity.
The live item is split and reviewed PASS (Q11, 2026-10-22), but has no Lean
record. The previous worker's stage-1 duplicate-split objection therefore does
not obstruct this statement delivery. There is no repair note. The statement,
statement dependencies, proof, proof dependencies and review are unchanged.

The module is Sheaf.CategoryTheory.RestrictedTowerResolutionAcyclicity, namespace
SheafOfModules.RestrictedTowerResolution. Its three postponed statements are
restrictionFunctor_exact, acyclicity and resolutionTransitions. Every theorem
has proof `sorry`; all other declarations have real data. The additional
public declarations are helpers belonging to the very U0, p_* and projection
maps introduced in this node, as authorized by the launcher brief's helper rule.
There are no new nodes and no dependency-node repairs.

Source read: literature/stacks-project/sites-cohomology.tex, lines 4010ff,
lemma-derived-pushforward-composition (0D6E), including its adjoint-uniqueness
proof; lines 5016ff, section-derived-limits (0940), including the product site,
vertical covers, constant inverse image and g_*=lim description. I also read the
live item's six proof steps and its Q11 mathematical review. The projection and
resolution-change clauses are the explicit consequences recorded in that node.

Hypotheses and objects, individually:

- The site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`.
  `[EssentiallySmall.{w} C]` and the sheafification/sheaf-composition instances
  are exactly the coefficient-universe presentation already used by the
  recorded system-ringed-sequence-site dependency. There is no equation between
  object, morphism and coefficient universes. Mathlib's sheaf categories use J;
  its presentation by coverings is the imported SiteCoveringAxioms interface.
- The varying commutative ring sheaves are
  `B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}`. Index n denotes the paper's positive
  index n+1, exactly as in SystemRingedSequenceSite.
- The base commutative ring sheaf is `A : Sheaf J CommRingCat.{w}`.
  The compatible homomorphisms are
  `α : (Functor.const ℕᵒᵖ).obj A ⟶ B`; its naturality is precisely their
  compatibility with all coefficient transitions.
- The systems are the recorded `StrictRingSystem B`. The recorded
  `strictSystemSequenceEquivalence B` identifies them with modules on the
  actual ringed sequence site. No new strict-system category is defined.
- `Modules A` abbreviates the existing `ringedSiteModules`/`SheafOfModules`
  category for the CommRingCat-to-RingCat composite of A. It is not a new
  module structure. Unbounded complexes are `CochainComplex ... ℤ`.
- U0 is `restrictionFunctor A B α`. Its object `tower ... N` has level
  `(restriction A B α n).obj (N.level n)`, with restriction the existing
  `SheafOfModules.restrictScalars` along α_n. Horizontal maps are the given
  `N.transition`, restricted and composed with the existing normalized
  `systemScalarRestrictionComposition` isomorphism. Objects, horizontal maps
  and morphisms are actual constructions, with no selected functor or
  existential comparison in their definition.
- The identity-topos coefficient morphism r and the sequence projection g are
  presented in the coordinates stipulated by the node: r_* is this U0 and g_*
  is Mathlib's limit functor. Consequently `directImage A B α` is the actual
  composite U0 ⋙ lim representing p_*=g_*r_*. Its sections are compatible
  families of sections with the induced componentwise A-action; this is the
  source's direct-image construction. No additional geometric morphism, chosen
  map or equality hypothesis is supplied to the theorem.
- The ordinary localization is Mathlib's `DerivedCategory` and its `Q`.
  The target uses `[HasDerivedCategory.{d} (Modules A)]`. The transition
  statement additionally uses source and tower localizations in independent
  universes s and t; these do not equate any site or coefficient universes.
- A resolution a is `(a : N ⟶ I) [QuasiIso a] [I.IsKInjective]`.
  The second resolution is
  `(j : (restrictionComplex A B α).obj I ⟶ T)` with `[QuasiIso j]` and
  `[T.IsKInjective]`. There is no assumption that the restricted I or any
  component of I is K-injective.

Clauses, individually:

1. Exactness of r_*=U0 is `restrictionFunctor_exact`: both
   `PreservesFiniteLimits` and `PreservesFiniteColimits` of the constructed U0.
   Its docstring gives step 1, using the unchanged underlying abelian sheaves.
2. `limitComplex A` is `lim.mapHomologicalComplex (.up ℤ)`. The first conjunct
   of `acyclicity` is exactly `QuasiIso ((limitComplex A).map j)`.
3. Ordinary p_*I=lim U0I is `directImageComplexIso`. This is a natural
   isomorphism of the two complex-valued functors, constructed by `Iso.refl`
   because the stipulated composite direct-image presentation is definitionally
   U0 followed by lim. Its degree maps and therefore its projection maps are
   identities. Being a natural isomorphism includes compatibility with maps of
   resolutions without an added tautological theorem conjunct.
4. `componentMap A ((restrictionComplex A B α).map a) n` is U0a_n, while
   `componentMap A j n` is j_n. Their quasi-isomorphism assertions are the
   next two conjuncts of `acyclicity`, separately for every n.
5. `projection A T n` is the existing `lim.π (op n)` mapped to complexes by
   `NatTrans.mapHomologicalComplex`. It is the degreewise ordinary projection,
   including the actual tower transitions.
6. The witnesses ea and ej in `acyclicity` are isomorphisms whose homs are
   required to equal Q(U0a_n) and Q(j_n). Hence their inverses are exactly the
   inverses in the displayed node equation, not arbitrary isomorphisms. Lean
   writes composition from left to right, so the equation is
   `Q(lim j) ≫ Q(pr_n^T) ≫ ej.inv ≫ ea.inv = Q(pr_n^(U0I)) ≫ ea.inv`.
   This is precisely the node's right-to-left displayed formula. The witnesses
   allow the inverse equation to be stated without assuming the component
   quasi-isomorphisms that the theorem is supposed to conclude.
7. `resolutionTransitions` treats any second pair a',j' of resolutions of the
   same N. It asserts existence of k:I→I' and l:T→T' with ak homotopic to a'
   and jl homotopic to (U0k)j'. For every such pair, it asserts uniqueness of
   their homotopy classes and identifies Q(k) and Q(l) with the canonical
   fractions Q(a)⁻¹Q(a') and Q(j)⁻¹Q(U0k)Q(j'). This specifies the canonical
   resolution transitions rather than merely quantifying over unrelated maps.
8. The same statement makes lim(U0k) and lim(l) quasi-isomorphisms, and states
   the actual comparison square
   `Q(lim j) ≫ Q(lim l) = Q(lim U0k) ≫ Q(lim j')`.
   The docstring identifies these maps with the canonical derived transitions
   using the recorded K-injective derived-map computation theorem.
9. For each n and every ea,ej,ea',ej' with the four specified homs, the final
   two equations transport the normalized projection from T' along lim(l) to
   that from T, and the normalized projection from U0I' along lim(U0k) to that
   from U0I. These are exactly the two sides of the node's projection equation.
   The acyclicity statement already ensures the four isomorphisms exist.
   Uniqueness of the homotopy classes includes identity, composition and inverse
   compatibility, and the case of changing j alone.

Dependency declarations read and used:

- Sheaf.CategoryTheory.SiteCoveringAxioms:
  CategoryTheory.Precoverage.IsSiteForCoverings (recorded site convention;
  imported transitively through the recorded sequence-site module).
- Sheaf.CategoryTheory.SystemRingedSequenceSite:
  SheafOfModules.strictSystemSequenceEquivalence, systemSequenceModules,
  systemSequenceRing, systemSequenceEvaluation. I read the full equivalence and
  its sectionwise vertical restriction. The StrictRingSystem, systemLevel,
  systemRestriction, systemEvaluation and exact evaluation instances are the
  public foundational declarations reexported by this module.
- Mathlib.Algebra.Homology.DerivedCategory.Basic:
  DerivedCategory, HasDerivedCategory and DerivedCategory.Q.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  SheafOfModules.restrictScalars, including its unchanged underlying sheaf
  definition and additive instance.
- Sheaf.CategoryTheory.RingedToposMorphism:
  CategoryTheory.RingedToposMorphism; I read the complete structural signature,
  its underlying-sheaf identification and induced-action normalization. The
  theorem here uses its stipulated direct-image coordinates rather than an
  arbitrary input of that structure.
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective:
  CochainComplex.IsKInjective (the full acyclic-source null-homotopy definition).
- Proof imports follow the node's existing proof dependencies:
  CategoryTheory.Functor.kInjectiveDerivedMapComputation and its transition
  computation in Sheaf.CategoryTheory.KInjectiveDerivedMapComputation;
  CategoryTheory.restrictionRingedToposModuleDirectImage_exists in
  Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage;
  CategoryTheory.ringedToposDerivedPushforwardComposition in
  Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition;
  CochainComplex.IsKInjective.Qh_map_bijective and quasiIso_iff in
  Mathlib.Algebra.Homology.DerivedCategory.KInjective;
  CategoryTheory.Abelian.functorCategoryAbelian in
  Mathlib.CategoryTheory.Abelian.FunctorCategory; and
  SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
  in Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses.

Edge cases checked before finalizing the signatures:

- The zero ring and zero complexes are allowed; neither nontriviality nor
  nonemptiness of the site is assumed.
- Constant B and identity structural maps recover the ordinary tower situation.
- Non-flat coefficient maps, for example Z→Z/2, are allowed. No preservation of
  K-injectivity by scalar restriction is stated or used as a hypothesis.
- The first positive level is n=0 in Lean; there is no lost initial projection.
- Arbitrarily unbounded complexes occur throughout. No termwise injectivity,
  boundedness, flatness or Mittag-Leffler condition is imposed.
- The site has independent object and morphism universes, and the coefficient
  universe agrees with the existing sequence-site encoding. The three chosen
  derived localizations in the transition statement also have independent
  universes.
- Taking a'=a, I'=I, k=identity gives a change of the second resolution alone.
  Taking both pairs equal includes identities; uniqueness of homotopy classes
  makes successive resolution changes agree with their composite.

Searches actually made:

- msearch.py leanfinder: "A K-injective complex of varying ring sheaf systems
  restricted to a constant ring is acyclic for inverse limit with normalized
  projection equations". Eight hits, beginning with CochainComplex.IsKInjective
  and bounded-below injective-complex results; none states this result.
- msearch.py loogle: "CochainComplex.IsKInjective, CategoryTheory.Limits.lim".
  Service returned OK with zero hits.
- msearch.py grep: "IsKInjective|restrictScalars" in
  CategoryTheory/Functor/Derived. Service returned OK with zero hits.
- msearch.py leansearch: "Restriction of scalars of a K-injective varying ring
  sheaf system is acyclic for inverse limit, with canonical inverse-limit
  projection comparison". Eight hits: restriction of scalars for presheaves,
  sheaves and modules, ordinary ModuleCat limit preservation, and unrelated
  restriction declarations. The existing SheafOfModules.restrictScalars hit is
  used; no theorem hit states the acyclicity or projection comparison.
- rg of the node id in lean/WeilConjectures: no declaration for this item.
- rg of restricted tower/resolution, system restriction and inverse-limit terms
  in lean/WeilConjectures and lean/Sheaf: related arithmetic-restriction and
  constant-coefficient comparison modules, but no exact statement of this node.
  In particular SequencePushforwardLimitProjections includes the acyclicity as
  part of a larger downstream result, so using that theorem would be circular.
- I read SequenceProjectionDerivedAdjunction's private restrictedDiagram and
  restrictedDiagrams implementation and its private directImage. These are not
  public declarations usable in this public statement; a module-mode probe
  confirmed that a public abbreviation cannot refer to restrictedDiagrams.
  The delivered helper therefore supplies the public real-data sectionwise
  interface using the existing coefficient-composition identification, rather
  than selecting a functor from the downstream derived-adjunction theorem.
  No private implementation or private imported name occurs in the delivery.
- The earlier probe also showed limit additivity is not an inferred instance in
  the available public API. The delivered limitAdditive uses the existing
  Functor.additive_of_preserves_binary_products construction. U0 additivity
  uses the existing exact systemEvaluation and scalar-restriction additivity;
  it does not assume component addition is definitionally the chosen system
  addition.

Validation: scompile.py compiled the completed module on the live server, both
as a sandbox module and at its library module name, with no errors or warnings
(12.1 s and 13.8 s respectively). Only the prescribed wrapper was used. The
final delivery dry run is performed after writing this report and node record.
No statement correction or STATEMENT-DISPUTED issue was found.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
