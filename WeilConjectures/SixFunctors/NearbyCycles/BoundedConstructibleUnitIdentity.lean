/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleExchange

/-!

# The unit identity of nearby cycles on bounded constructible complexes

Let `φ : M ⟶ N` be a morphism of models over `f : X ⟶ Y` and `f' : X' ⟶ Y'` whose nearby cycles
preserve bounded constructible complexes. This file restricts the pullback exchange
`α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` to bounded constructible complexes
(`NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange`) and transports the unit identity
of the pushforward exchange (blueprint `det-tf-sp-trace-morphism`)
```
χ_f(Lf^* Λ) ∘ Ψ_N(η_f) ∘ σ_N = Rf'_*(Ψ_M(ε_f) ∘ σ_M ∘ ε_{f'}⁻¹) ∘ η_{f'}
```
to `Dᵇc(-)⟦Λ⟧`, with the unit comparisons `ε` of the strong monoidal pullbacks
(`NearbyCyclesModel.Hom.boundedConstructibleUnit_comp_map_unit_comp_pushforwardExchange_app`).

## Implementation notes

The objects of `Dᵇc(X)⟦Λ⟧` live in the derived category with its `HasDerivedCategory` instance
as fixed by `ProEtale.boundedConstructible`, while the ambient exchange maps are stated with the
instance found by typeclass synthesis. The two are equal only up to proof irrelevance, and the
kernel must never be asked to compare components `χ.app K` of the ambient exchange maps at such
differently presented objects: it would unfold `χ`. The transports are therefore proved for an
arbitrary natural transformation `χ` (the `_aux` lemmas) and only then instantiated, after
rewriting the restricted exchange maps as `NearbyCyclesModel.liftExchange` of the ambient ones.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section UpperStar

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

/-- On the ambient derived category, the unit comparison of the derived pullback on bounded
constructible complexes is the inverse of `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`. -/
lemma boundedConstructibleUpperStar_εIso_hom_hom :
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar Λ ℓ f)).hom.hom =
      (leftDerivedUpperStarUnitIso Λ f.left).inv :=
  rfl

/-- On the ambient derived category, the unit of `Lf^* ⊣ Rf_*` on bounded constructible complexes
is the unit of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom (K : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).unit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ f.left).unit.app K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_unit_app
    (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ f).symm K).trans ?_
  simp [boundedConstructibleUpperStarCompatibility, boundedConstructibleLowerStarCompatibility,
    ObjectProperty.liftCompιIso]

/-- On the ambient derived category, the counit of `Lf^* ⊣ Rf_*` on bounded constructible
complexes is the counit of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom (K : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ f.left).counit.app K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ f).symm K).trans ?_
  simp only [boundedConstructibleUpperStarCompatibility, boundedConstructibleLowerStarCompatibility,
    ObjectProperty.liftCompιIso, Iso.symm_inv, Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end UpperStar

namespace NearbyCyclesModel

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f.left f'.left) (hM : M.PreservesBoundedConstructible Λ)
  (hN : N.PreservesBoundedConstructible Λ)

/-! ### The pushforward exchange -/

/-- The restricted pushforward exchange is `NearbyCyclesModel.liftExchange` of the ambient one. -/
lemma boundedConstructiblePushforwardExchange_eq_liftExchange :
    φ.boundedConstructiblePushforwardExchange ℓ hM hN =
      liftExchange (φ.pushforwardExchange Λ)
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f K.obj K.property)
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f' K.obj K.property)
        (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property) :=
  rfl

/-- The components of `NearbyCyclesModel.liftExchange` of any transformation
`χ : Rf_* ⋙ Ψ_N ⟶ Ψ_M ⋙ Rf'_*`, viewed as a transformation between the restricted functors. -/
private lemma liftExchange_pushforward_app_hom_aux (K : Dᵇc(X.left)⟦Λ⟧)
    (χ : R((f.left)_*⟦Λ⟧) ⋙ N.nearbyCycles Λ ⟶ M.nearbyCycles Λ ⋙ R((f'.left)_*⟦Λ⟧)) :
    ((liftExchange χ
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f K.obj K.property)
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f' K.obj K.property)
        (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property) :
      boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleNearbyCycles hN ⟶
        boundedConstructibleNearbyCycles hM ⋙ boundedConstructibleLowerStar Λ ℓ f').app K).hom =
      χ.app K.obj :=
  liftExchange_app_hom _ _ _ _ _ K

/-- The components of the restricted pushforward exchange are those of the ambient one. -/
@[simp]
lemma boundedConstructiblePushforwardExchange_app_hom (K : Dᵇc(X.left)⟦Λ⟧) :
    ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app K).hom =
      (φ.pushforwardExchange Λ).app K.obj := by
  rw [boundedConstructiblePushforwardExchange_eq_liftExchange]
  exact liftExchange_pushforward_app_hom_aux ℓ hM hN K _

/-! ### The pullback exchange -/

/-- The pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` on bounded constructible complexes: the
restriction of `NearbyCyclesModel.Hom.pullbackExchange`. -/
noncomputable def boundedConstructiblePullbackExchange :
    boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleUpperStar Λ ℓ f' ⟶
      boundedConstructibleUpperStar Λ ℓ f ⋙ boundedConstructibleNearbyCycles hM :=
  liftExchange (φ.pullbackExchange Λ) (fun K ↦ hN K.obj K.property)
    (fun K ↦ hM K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f' K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K.obj K.property)

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
/-- The restricted pullback exchange is `NearbyCyclesModel.liftExchange` of the ambient one. -/
lemma boundedConstructiblePullbackExchange_eq_liftExchange :
    φ.boundedConstructiblePullbackExchange ℓ hM hN =
      liftExchange (φ.pullbackExchange Λ) (fun K ↦ hN K.obj K.property)
        (fun K ↦ hM K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K.obj K.property) :=
  rfl

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
/-- The components of `NearbyCyclesModel.liftExchange` of any transformation
`α : Ψ_N ⋙ Lf'^* ⟶ Lf^* ⋙ Ψ_M`, viewed as a transformation between the restricted functors. -/
private lemma liftExchange_pullback_app_hom_aux (K : Dᵇc(Y.left)⟦Λ⟧)
    (α : N.nearbyCycles Λ ⋙ L((f'.left)^*⟦Λ⟧) ⟶ L((f.left)^*⟦Λ⟧) ⋙ M.nearbyCycles Λ) :
    ((liftExchange α (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K.obj K.property) :
      boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleUpperStar Λ ℓ f' ⟶
        boundedConstructibleUpperStar Λ ℓ f ⋙ boundedConstructibleNearbyCycles hM).app K).hom =
      α.app K.obj :=
  liftExchange_app_hom _ _ _ _ _ K

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
/-- The components of the restricted pullback exchange are those of the ambient one. -/
@[simp]
lemma boundedConstructiblePullbackExchange_app_hom (K : Dᵇc(Y.left)⟦Λ⟧) :
    ((φ.boundedConstructiblePullbackExchange ℓ hM hN).app K).hom =
      (φ.pullbackExchange Λ).app K.obj := by
  rw [boundedConstructiblePullbackExchange_eq_liftExchange]
  exact liftExchange_pullback_app_hom_aux ℓ hM hN K _

/-! ### The unit identity -/

/-- The unit identity on bounded constructible complexes, for an arbitrary transformation `χ` and
arbitrary adjunctions `adj`, `adj'` in place of the ambient pushforward exchange and of the
adjunctions `Lf^* ⊣ Rf_*`, `Lf'^* ⊣ Rf'_*`, deduced from the ambient unit identity `hamb`. -/
private lemma unit_comp_map_unit_comp_liftExchange_app_aux
    (χ : R((f.left)_*⟦Λ⟧) ⋙ N.nearbyCycles Λ ⟶ M.nearbyCycles Λ ⋙ R((f'.left)_*⟦Λ⟧))
    (adj : L((f.left)^*⟦Λ⟧) ⊣ R((f.left)_*⟦Λ⟧)) (adj' : L((f'.left)^*⟦Λ⟧) ⊣ R((f'.left)_*⟦Λ⟧))
    (hη : ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).unit.app (𝟙_ _)).hom =
      adj.unit.app (𝟙_ Dᵇc(Y.left)⟦Λ⟧).obj)
    (hη' : ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f').unit.app (𝟙_ _)).hom =
      adj'.unit.app (𝟙_ Dᵇc(Y'.left)⟦Λ⟧).obj)
    (hamb : N.unit Λ ≫ (N.nearbyCycles Λ).map (adj.unit.app (𝟙_ _)) ≫ χ.app _ =
      adj'.unit.app (𝟙_ _) ≫ R((f'.left)_*⟦Λ⟧).map ((leftDerivedUpperStarUnitIso Λ f'.left).hom ≫
        M.unit Λ ≫ (M.nearbyCycles Λ).map (leftDerivedUpperStarUnitIso Λ f.left).inv)) :
    boundedConstructibleUnit ℓ hN ≫ (boundedConstructibleNearbyCycles hN).map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).unit.app (𝟙_ _)) ≫
        (liftExchange χ
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f K.obj K.property)
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f' K.obj K.property)
          (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property) :
            boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleNearbyCycles hN ⟶
            boundedConstructibleNearbyCycles hM ⋙ boundedConstructibleLowerStar Λ ℓ f').app
          ((boundedConstructibleUpperStar Λ ℓ f).obj (𝟙_ _)) =
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f').unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar Λ ℓ f').map
          ((Functor.Monoidal.εIso (boundedConstructibleUpperStar Λ ℓ f')).inv ≫
            boundedConstructibleUnit ℓ hM ≫ (boundedConstructibleNearbyCycles hM).map
              (Functor.Monoidal.εIso (boundedConstructibleUpperStar Λ ℓ f)).hom) := by
  refine ObjectProperty.hom_ext _ ((congrArg (fun u ↦ N.unit Λ ≫ (N.nearbyCycles Λ).map u ≫
    χ.app _) hη).trans (hamb.trans ?_))
  exact (congrArg (fun u ↦ u ≫ R((f'.left)_*⟦Λ⟧).map
    ((leftDerivedUpperStarUnitIso Λ f'.left).hom ≫ M.unit Λ ≫
      (M.nearbyCycles Λ).map (leftDerivedUpperStarUnitIso Λ f.left).inv)) hη').symm

/-- **Unit identity of the pushforward exchange on bounded constructible complexes** (blueprint
`det-tf-sp-trace-morphism`):
`χ_f(Lf^* Λ) ∘ Ψ_N(η_f) ∘ σ_N = Rf'_*(Ψ_M(ε_f) ∘ σ_M ∘ ε_{f'}⁻¹) ∘ η_{f'}`, where
`ε_f : Λ_X ≅ Lf^* Λ_Y` and `ε_{f'} : Λ_{X'} ≅ Lf'^* Λ_{Y'}` are the unit comparisons of the
strong monoidal pullbacks. -/
lemma boundedConstructibleUnit_comp_map_unit_comp_pushforwardExchange_app :
    boundedConstructibleUnit ℓ hN ≫ (boundedConstructibleNearbyCycles hN).map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).unit.app (𝟙_ _)) ≫
        (φ.boundedConstructiblePushforwardExchange ℓ hM hN).app _ =
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f').unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar Λ ℓ f').map
          ((Functor.Monoidal.εIso (boundedConstructibleUpperStar Λ ℓ f')).inv ≫
            boundedConstructibleUnit ℓ hM ≫ (boundedConstructibleNearbyCycles hM).map
              (Functor.Monoidal.εIso (boundedConstructibleUpperStar Λ ℓ f)).hom) := by
  rw [boundedConstructiblePushforwardExchange_eq_liftExchange]
  exact unit_comp_map_unit_comp_liftExchange_app_aux ℓ hM hN (φ.pushforwardExchange Λ) _ _
    (boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom (Λ := Λ) ℓ f (𝟙_ _))
    (boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom (Λ := Λ) ℓ f' (𝟙_ _))
    (φ.unit_comp_map_unit_comp_pushforwardExchange_app Λ)

/-! ### The mate relation -/

/-- The components of the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of a transformation `α : G ⋙ L₂ ⟶ L₁ ⋙ H`. -/
private lemma mateEquiv_app_aux {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (X : D) :
    (mateEquiv adj₁ adj₂ α).natTrans.app X =
      adj₂.unit.app (G.obj (R₁.obj X)) ≫ R₂.map (α.app (R₁.obj X) ≫ H.map (adj₁.counit.app X)) := by
  simp [mateEquiv]

/-- The components of the mate of a transformation between functors of full subcategories, on the
ambient category. -/
private lemma mateEquiv_app_hom_aux {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] {PC : ObjectProperty C} {PD : ObjectProperty D} {PE : ObjectProperty E}
    {PF : ObjectProperty F} {G : PC.FullSubcategory ⥤ PE.FullSubcategory}
    {H : PD.FullSubcategory ⥤ PF.FullSubcategory} {L₁ : PC.FullSubcategory ⥤ PD.FullSubcategory}
    {R₁ : PD.FullSubcategory ⥤ PC.FullSubcategory} {L₂ : PE.FullSubcategory ⥤ PF.FullSubcategory}
    {R₂ : PF.FullSubcategory ⥤ PE.FullSubcategory} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (X : PD.FullSubcategory) :
    ((mateEquiv adj₁ adj₂ α).natTrans.app X).hom =
      (adj₂.unit.app (G.obj (R₁.obj X))).hom ≫
        (R₂.map (α.app (R₁.obj X) ≫ H.map (adj₁.counit.app X))).hom := by
  rw [mateEquiv_app_aux]
  rfl

/-- The mate relation on bounded constructible complexes, for arbitrary transformations `α`, `χ`
and adjunctions `adj`, `adj'` in place of the ambient exchange maps and of the adjunctions
`Lf^* ⊣ Rf_*`, `Lf'^* ⊣ Rf'_*`. -/
private lemma liftExchange_eq_mateEquiv_aux
    (α : N.nearbyCycles Λ ⋙ L((f'.left)^*⟦Λ⟧) ⟶ L((f.left)^*⟦Λ⟧) ⋙ M.nearbyCycles Λ)
    (χ : R((f.left)_*⟦Λ⟧) ⋙ N.nearbyCycles Λ ⟶ M.nearbyCycles Λ ⋙ R((f'.left)_*⟦Λ⟧))
    (adj : L((f.left)^*⟦Λ⟧) ⊣ R((f.left)_*⟦Λ⟧)) (adj' : L((f'.left)^*⟦Λ⟧) ⊣ R((f'.left)_*⟦Λ⟧))
    (hχ : χ = (mateEquiv adj adj' α).natTrans)
    (hη : ∀ K : Dᵇc(Y'.left)⟦Λ⟧,
      ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f').unit.app K).hom =
        adj'.unit.app K.obj)
    (hε : ∀ K : Dᵇc(X.left)⟦Λ⟧,
      ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).counit.app K).hom =
        adj.counit.app K.obj) :
    (liftExchange χ
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f K.obj K.property)
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f' K.obj K.property)
        (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property) :
      boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleNearbyCycles hN ⟶
        boundedConstructibleNearbyCycles hM ⋙ boundedConstructibleLowerStar Λ ℓ f') =
      (mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f')
        (liftExchange α (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f' K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K.obj K.property) :
        boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleUpperStar Λ ℓ f' ⟶
          boundedConstructibleUpperStar Λ ℓ f ⋙ boundedConstructibleNearbyCycles hM)).natTrans := by
  subst hχ
  refine NatTrans.ext (funext fun K ↦ ObjectProperty.hom_ext _ ?_)
  refine (liftExchange_pushforward_app_hom_aux ℓ hM hN K _).trans
    (Eq.trans ?_ (mateEquiv_app_hom_aux (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f') _ K).symm)
  rw [mateEquiv_app_aux]
  exact congrArg₂ (fun a b ↦ a ≫ b) (hη ((boundedConstructibleNearbyCycles hN).obj
      ((boundedConstructibleLowerStar Λ ℓ f).obj K))).symm
    (congrArg (fun u ↦ R((f'.left)_*⟦Λ⟧).map (α.app _ ≫ (M.nearbyCycles Λ).map u)) (hε K).symm)

/-- The restricted pushforward exchange is the mate of the restricted pullback exchange along the
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*` on bounded constructible complexes. -/
lemma boundedConstructiblePushforwardExchange_eq_mateEquiv :
    φ.boundedConstructiblePushforwardExchange ℓ hM hN =
      (mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f')
        (φ.boundedConstructiblePullbackExchange ℓ hM hN)).natTrans := by
  rw [boundedConstructiblePushforwardExchange_eq_liftExchange,
    boundedConstructiblePullbackExchange_eq_liftExchange]
  exact liftExchange_eq_mateEquiv_aux ℓ hM hN (φ.pullbackExchange Λ) (φ.pushforwardExchange Λ)
    _ _ rfl (boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom (Λ := Λ) ℓ f')
    (boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom (Λ := Λ) ℓ f)

end Hom

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
