/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Finite coefficients on the small pro-etale site

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node def-weil-pbc-proetale-modules (blueprint: def-weil-pbc-proetale-modules).

## Main definitions

* `finiteCoefficientRingSheaf`: sheafified continuous functions on connected components.
* `FiniteCoefficientModules`: left modules over this ring sheaf.
* `FiniteCoefficientDerivedCategory` and `FiniteCoefficientDerivedCategoryPlus`: the
  unbounded localization and its strictly full bounded below subcategory.
* `finiteCoefficientEtaleRingSheaf` and `FiniteCoefficientEtaleDerivedCategory`: etale
  coefficients, using the canonical fixed-ring module-sheaf presentation.
* `finiteCoefficientDerivedComparison`: the exact module inverse image on complexes.
* `isBoundedConstructibleFiniteCoefficient`: the essential image of bounded constructible
  etale complexes, with its full subcategory `FiniteCoefficientBoundedConstructibleDerivedCategory`.
-/

@[expose] public section

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- A diagram of left modules is a module presheaf over the constant ring presheaf.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientModulePresheaf (C : Type uC) [Category.{vC} C]
    (Λ : Type (u + 1)) [Ring Λ] :
    (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ⥤
      PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj F :=
    { obj U := F.obj U
      map f := ModuleCat.ofHom (F.map f).hom
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map f :=
    { app U := f.app U
      naturality g := by ext x; exact ConcreteCategory.congr_hom (f.naturality g) x }
  map_id F := by ext U x; rfl
  map_comp f g := by ext U x; rfl

private noncomputable def coefficientModulePresheafFullyFaithful
    (C : Type uC) [Category.{vC} C] (Λ : Type (u + 1)) [Ring Λ] :
    (finiteCoefficientModulePresheaf C Λ).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private theorem coefficientRealization_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (Λ : Type (u + 1)) [Ring Λ] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
      finiteCoefficientModulePresheaf C Λ ⋙
      PresheafOfModules.sheafification.{u + 1} α).IsEquivalence := by
  have : (finiteCoefficientModulePresheaf C Λ).Full :=
    (coefficientModulePresheafFullyFaithful C Λ).full
  have : (finiteCoefficientModulePresheaf C Λ).Faithful :=
    (coefficientModulePresheafFullyFaithful C Λ).faithful
  let E := sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    finiteCoefficientModulePresheaf C Λ
  let S := PresheafOfModules.sheafification.{u + 1} α
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α
  have hunit (F : Sheaf J (ModuleCat.{u + 1} Λ)) :
      IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj F)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F).property
  let η : E ⟶ (E ⋙ S) ⋙ G :=
    Functor.whiskerLeft E (PresheafOfModules.sheafificationAdjunction α).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  have : (E ⋙ S).Faithful := Functor.Faithful.of_comp_iso (asIso η).symm
  have : (E ⋙ S).Full := Functor.Full.of_comp_faithful_iso (asIso η).symm
  have : (E ⋙ S).EssSurj := by
    refine ⟨fun M ↦ ?_⟩
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    let F' : Sheaf J (ModuleCat.{u + 1} Λ) :=
      ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M.isSheaf⟩
    refine ⟨F', ⟨?_⟩⟩
    exact asIso ((PresheafOfModules.sheafificationAdjunction α).counit.app M)
  change (E ⋙ S).IsEquivalence
  exact Functor.IsEquivalence.mk

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Continuous functions on the quotient space of connected components, with pointwise
ring operations and restriction by precomposition. Source: blueprint,
`def-weil-pbc-proetale-modules` (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientPresheaf (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    T.ProEtᵒᵖ ⥤ RingCat.{u + 1} where
  obj U := RingCat.of C(ConnectedComponents U.unop.left, Λ)
  map f := RingCat.ofHom
    { toFun := fun s ↦ s.comp
        ⟨f.unop.left.continuous.connectedComponentsMap,
          f.unop.left.continuous.connectedComponentsMap_continuous⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id U := by
    ext s c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl
  map_comp f g := by
    ext s c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl

/-- The coefficient ring sheaf is the sheafification of continuous functions on connected
components. Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientRingSheaf : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
  (presheafToSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj
    (finiteCoefficientPresheaf T Λ)

/-- The category of left modules over the specified coefficient ring sheaf, with sectionwise
linear morphisms. Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable abbrev FiniteCoefficientModules :=
  ringedSiteModules.{u + 1} (finiteCoefficientRingSheaf T Λ)

/-- Localization of integer-indexed cochain complexes of coefficient modules at
quasi-isomorphisms. Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable abbrev FiniteCoefficientDerivedCategory :=
  @DerivedCategory (FiniteCoefficientModules T Λ) _ _ (HasDerivedCategory.standard _)

/-- The strictly full bounded below subcategory, using the standard cohomological
lower bound. Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable abbrev FiniteCoefficientDerivedCategoryPlus :=
  @DerivedCategory.Plus (FiniteCoefficientModules T Λ) _ _ (HasDerivedCategory.standard _)

/-- Constant scalar sections of the continuous-function coefficient presheaf.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientConstants :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ) ⟶ finiteCoefficientPresheaf T Λ where
  app U := RingCat.ofHom
    { toFun := fun r ↦ ContinuousMap.const _ r
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ f := by ext r; rfl

/-- The canonical scalar map from the constant presheaf to the coefficient ring sheaf.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientScalarMap :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ) ⟶ (finiteCoefficientRingSheaf T Λ).obj :=
  finiteCoefficientConstants T Λ ≫
    toSheafify (Scheme.ProEt.topology T) (finiteCoefficientPresheaf T Λ)

/-- Constant scalar sections identify the coefficient sheaf with the sheafification of
constant scalars. Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules).

Proof: continuous functions to a discrete ring are locally constant. Their level sets,
pulled back along the quotient map to connected components, are open and give an open
cover of the scheme, hence a pro-etale cover. On each member the function is a constant
scalar. Two constant scalars with equal restrictions are equal locally, including the
empty object, whose empty cover is allowed. Thus the constants-to-functions map is
locally bijective. The sheafification unit is locally bijective and these properties
are closed under composition. This also treats the zero ring and disconnected schemes. -/
theorem finiteCoefficientScalarMap_locallyBijective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) ∧
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) := by
  classical
  have hinj : Presheaf.IsLocallyInjective (Scheme.ProEt.topology T)
      (finiteCoefficientConstants T Λ) := by
    refine ⟨?_⟩
    intro U a b hab
    by_cases hU : Nonempty U.unop.left
    · obtain ⟨x⟩ := hU
      have hab' := congrArg (fun s : C(ConnectedComponents U.unop.left, Λ) ↦ s ⟦x⟧) hab
      change a = b at hab'
      subst b
      simpa only [Presheaf.equalizerSieve_self_eq_top] using
        (Scheme.ProEt.topology T).top_mem U.unop
    · have : IsEmpty U.unop.left := not_nonempty_iff.mp hU
      exact (Scheme.ProEt.topology T).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology U.unop)
  have hsurj : Presheaf.IsLocallySurjective (Scheme.ProEt.topology T)
      (finiteCoefficientConstants T Λ) := by
    refine ⟨?_⟩
    intro U s
    let f : C(U.left, Λ) := s.comp ⟨_, ConnectedComponents.continuous_coe⟩
    let O (x : U.left) : U.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete _).preimage f.continuous⟩
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
    · intro x
      exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
    · intro x
      refine ⟨f x, ?_⟩
      apply ContinuousMap.ext
      intro c
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
      change f x = f y.val
      exact y.property.symm
  constructor <;> dsimp only [finiteCoefficientScalarMap] <;> infer_instance

/-- Local injectivity needed for the associated module sheaf construction.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientScalarMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) :=
  (finiteCoefficientScalarMap_locallyBijective T Λ).1

/-- Local surjectivity needed for the associated module sheaf construction.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientScalarMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) :=
  (finiteCoefficientScalarMap_locallyBijective T Λ).2

/-- The etale coefficient ring sheaf is the sheafification of the constant ring presheaf.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientEtaleRingSheaf : Sheaf T.smallEtaleTopology RingCat.{u + 1} :=
  (constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)

/-- The canonical identification of fixed-ring etale module sheaves with modules over
the constant etale ring sheaf: regard the diagram as a constant-ring module presheaf,
then sheafify along the constant-ring sheafification unit.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientEtaleRealization :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      ringedSiteModules.{u + 1} (finiteCoefficientEtaleRingSheaf T Λ) :=
  sheafToPresheaf _ _ ⋙ finiteCoefficientModulePresheaf T.Etale Λ ⋙
    PresheafOfModules.sheafification
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of Λ)))

/-- The fixed-ring encoding really presents the etale ringed module category,
including for noncommutative rings.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules).

Proof: the unit from the constant ring presheaf to its associated ring sheaf is locally
bijective. Restriction of scalars followed by forgetting to the module presheaf gives
the inverse on underlying sheaves. A fixed scalar action extends uniquely to local
sections of the constant ring sheaf, since those sections are locally constant scalars.
The sheaf axioms glue the local scalar actions and their linear maps uniquely. The unit
and counit of the associated-module-sheaf adjunction are therefore isomorphisms.
The argument uses left scalar actions and does not require commutativity. -/
theorem finiteCoefficientEtaleRealization_isEquivalence :
    (finiteCoefficientEtaleRealization T Λ).IsEquivalence := by
  have _ := ‹Finite Λ›
  have _ := ‹DiscreteTopology Λ›
  exact coefficientRealization_isEquivalence T.smallEtaleTopology Λ
    (finiteCoefficientEtaleRingSheaf T Λ)
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of Λ)))

/-- The etale derived category in the standard fixed-ring module-sheaf encoding.
The canonical equivalence above identifies its abelian category with modules over
`finiteCoefficientEtaleRingSheaf`. Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
abbrev FiniteCoefficientEtaleDerivedCategory :=
  DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- Realization as modules over the specified ring sheaf: keep the module presheaf,
then apply the canonical associated-module-sheaf functor along constant scalar sections.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientRealization :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) ⥤
      FiniteCoefficientModules T Λ :=
  sheafToPresheaf _ _ ⋙ finiteCoefficientModulePresheaf T.ProEt Λ ⋙
    PresheafOfModules.sheafification (finiteCoefficientScalarMap T Λ)

/-- Realization is additive and exact; it is the canonical identification of fixed-ring
module sheaves with modules over the coefficient ring sheaf.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules).

Proof: the scalar map is locally bijective by the level-set argument above.
The module sheafification adjunction therefore identifies sheaves of fixed-ring modules
with sheaves of modules over the sheafified ring. Its unit and counit are isomorphisms
because their underlying abelian sheaves are the sheafification unit and counit.
The construction respects addition sectionwise, and this equivalence preserves finite
limits and colimits. -/
theorem finiteCoefficientRealization_exact :
    (finiteCoefficientRealization T Λ).Additive ∧
    PreservesFiniteLimits (finiteCoefficientRealization T Λ) ∧
    PreservesFiniteColimits (finiteCoefficientRealization T Λ) := by
  have : (finiteCoefficientRealization T Λ).IsEquivalence :=
    coefficientRealization_isEquivalence (Scheme.ProEt.topology T) Λ
      (finiteCoefficientRingSheaf T Λ) (finiteCoefficientScalarMap T Λ)
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Additivity of the canonical coefficient realization.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientRealization_additive :
    (finiteCoefficientRealization T Λ).Additive :=
  (finiteCoefficientRealization_exact T Λ).1

/-- Left exactness of the canonical coefficient realization.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientRealization_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientRealization T Λ) :=
  (finiteCoefficientRealization_exact T Λ).2.1

/-- Right exactness of the canonical coefficient realization.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientRealization_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientRealization T Λ) :=
  (finiteCoefficientRealization_exact T Λ).2.2

/-- The specified inverse image on left module sheaves: the comparison inverse image,
followed by its canonical coefficient-ring realization.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientComparison :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ FiniteCoefficientModules T Λ :=
  comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙ finiteCoefficientRealization T Λ

/-- Additivity inherited from comparison and coefficient realization.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientComparison_additive :
    (finiteCoefficientComparison T Λ).Additive :=
  inferInstanceAs
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙ finiteCoefficientRealization T Λ).Additive

/-- Left exactness inherited from comparison and coefficient realization.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientComparison_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientComparison T Λ) :=
  inferInstanceAs (PreservesFiniteLimits
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙ finiteCoefficientRealization T Λ))

/-- Right exactness inherited from comparison and coefficient realization.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientComparison_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientComparison T Λ) :=
  inferInstanceAs (PreservesFiniteColimits
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙ finiteCoefficientRealization T Λ))

/-- The chosen localization of ringed module sheaves, with the standard morphism universe.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientModules_hasDerivedCategory :
    HasDerivedCategory.{u + 2} (FiniteCoefficientModules T Λ) :=
  HasDerivedCategory.standard _

/-- Applying the exact comparison termwise to integer-indexed cochain complexes induces
this functor on their localizations. Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientDerivedComparison :
    FiniteCoefficientEtaleDerivedCategory T Λ ⥤ FiniteCoefficientDerivedCategory T Λ :=
  (finiteCoefficientComparison T Λ).mapDerivedCategory

/-- Bounded constructible objects are the essential image of bounded constructible
etale complexes under the canonical derived comparison functor.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
def isBoundedConstructibleFiniteCoefficient (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    ObjectProperty (FiniteCoefficientDerivedCategory T Λ) :=
  ObjectProperty.map (fun L : FiniteCoefficientEtaleDerivedCategory T Λ ↦
    (∀ j : ℤ, ∃ S : Scheme.LocallyClosedStratification T,
      (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) ∧
      ∀ k : Fin S.n,
        ∃ d : Scheme.LocallyConstantDatum
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj
            ((_root_.DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj L)),
          ∀ i : d.cover.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
            Nonempty
              ((((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj
                ((_root_.DerivedCategory.homologyFunctor
                  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj L)).over
                    (d.cover.etalePrecoverageToEtale i)) ≅
                (constantSheaf
                  ((S.domain k).smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
                  (ModuleCat.{u + 1} Λ)).obj M)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj L))
    (finiteCoefficientDerivedComparison T Λ)

/-- The strictly full subcategory of objects of bounded constructible etale origin.
Morphisms are all ambient derived morphisms. Source: blueprint,
`def-weil-pbc-proetale-modules` (blueprint: def-weil-pbc-proetale-modules). -/
abbrev FiniteCoefficientBoundedConstructibleDerivedCategory :=
  (isBoundedConstructibleFiniteCoefficient T Λ).FullSubcategory


/-- The canonical realization identifies fixed-ring module sheaves with modules over the
continuous-function coefficient sheaf, including finite noncommutative coefficient rings.
Source: blueprint, def-weil-pbc-proetale-modules
(blueprint: def-weil-pbc-proetale-modules).
Proof: the constant-scalar map is locally bijective by the level-set argument in
finiteCoefficientScalarMap_locallyBijective. The associated-module-sheaf adjunction
therefore has invertible unit and counit on sheaves. Its inverse restricts scalars
and forgets to the fixed-ring module sheaf. The locally constant scalar actions
and their linear maps glue uniquely. This uses left modules and applies to
noncommutative rings as well. -/
theorem finiteCoefficientRealization_isEquivalence_ring (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization T Λ).IsEquivalence := by
  exact coefficientRealization_isEquivalence (Scheme.ProEt.topology T) Λ
    (finiteCoefficientRingSheaf T Λ) (finiteCoefficientScalarMap T Λ)

/-- Equivalence structure on the canonical coefficient realization.
Source: blueprint, def-weil-pbc-proetale-modules
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable instance finiteCoefficientRealizationIsEquivalenceRing (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization T Λ).IsEquivalence :=
  finiteCoefficientRealization_isEquivalence_ring T Λ

end AlgebraicGeometry.ProEtale
