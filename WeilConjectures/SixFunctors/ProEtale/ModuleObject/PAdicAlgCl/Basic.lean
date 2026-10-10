/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.ContinuousMap

/-!

# The canonical coefficient morphisms of the `ℚ̄_ℓ`-sheaf

Let `ℓ` be a prime. For every scheme `X`, the `ℚ̄_ℓ`-sheaf `ℚ̄_ℓ,X` on the small pro-étale site
of `X` is the ring object of abelian sheaves `AlgebraicGeometry.ProEtale.padicAlgClSheaf X ℓ`
of `WeilConjectures.CategoryTheory.RingObjects.EllAdic`: the *sheafification* of the presheaf
of rings
```
P_X := (U ↦ {h ∈ C(U, ℚ̄_ℓ) | h takes values in a finite subextension of ℚ_ℓ})
```
(`AlgebraicGeometry.ProEtale.padicAlgClRingPresheaf X ℓ`). Unlike the coefficient sheaves of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.ContinuousMap`, which are
the sheaves `C(-, T)` of continuous maps into a topological ring `T`, `ℚ̄_ℓ,X` is not the sheaf
of continuous maps into `ℚ̄_ℓ` with its valuation topology, and it is not a sheaf of rings
`Sheaf _ RingCat` but a sheafified presheaf of rings. This file constructs the *canonical
coefficient morphisms* relating these ring objects along a morphism of schemes `f : X ⟶ Y`,
which is all that the six functors on module objects over `ℚ̄_ℓ,X` need:

* `η_f : ℚ̄_ℓ,Y ⟶ f_* ℚ̄_ℓ,X` (`AlgebraicGeometry.ProEtale.padicAlgClPushforwardHom`). On the
  presheaves of rings, the pushforward of `P_X` along `f` is the presheaf
  `V ↦ P_X(V ×_Y X)` on `Y_proét`, and the pullback of functions
  ```
  P_Y(V) ⟶ P_X(V ×_Y X),   h ↦ h ∘ p_V
  ```
  along the projection `p_V : V ×_Y X → V` is a morphism of presheaves of rings
  `P_Y ⟶ f_* P_X` (`AlgebraicGeometry.ProEtale.padicAlgClRingPresheafPushforwardHom`): a
  function with values in a finite subextension `E ⊆ ℚ̄_ℓ` stays so when pulled back. The
  sheaf-level `η_f` is the morphism `ℚ̄_ℓ,Y = (P_Y)^# ⟶ f_* (P_X)^# = f_* ℚ̄_ℓ,X` adjoint to the
  composite `P_Y ⟶ f_* P_X ⟶ f_* (P_X)^#` under the sheafification adjunction, the target
  being a sheaf since `f_*` preserves sheaves. It is characterised by
  `AlgebraicGeometry.ProEtale.toSheafify_padicAlgClPushforwardHom_hom`, and it is compatible
  with identities and compositions since the pullback of functions is
  (`AlgebraicGeometry.ProEtale.padicAlgClPushforwardHom_id`,
  `AlgebraicGeometry.ProEtale.padicAlgClPushforwardHom_comp`).
* `α_f : f^* ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,X` (`AlgebraicGeometry.ProEtale.padicAlgClPullbackHom`): the mate of
  `η_f` under the adjunction `f^* ⊣ f_*`, a morphism of ring objects since `f^*` is strong
  monoidal, see
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Monoidal`.
  It is an isomorphism for an open immersion `f`, but not in general.

The six functors on module objects over `ℚ̄_ℓ,X` are built from `η_f` and `α_f` in the other
files of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl`, by the same "`mapMod`
followed by change of scalars" recipe as in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension`: nothing there uses the
particular form of the coefficient ring objects, only the morphisms `η_f` and `α_f`.

## Sorried input

* `AlgebraicGeometry.ProEtale.isMonHom_padicAlgClPushforwardHom`: `η_f` is a morphism of ring
  objects, for the ring object structure on `f_* ℚ̄_ℓ,X` induced by the lax monoidal structure
  of `f_*`. The ring structure of `ℚ̄_ℓ,Y` is the sheafification of the pointwise
  multiplication of `P_Y` (the sheafification functor being monoidal), the lax monoidal
  structure of `f_*` is the pointwise multiplication after sheafification as well (through the
  transport of `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`), and `h ↦ h ∘ p_V` is
  multiplicative and unital; the proof is the identification of these two sheafified pointwise
  structures.
* `AlgebraicGeometry.ProEtale.isIso_padicAlgClPullbackHom_of_isOpenImmersion`: `α_j` is an
  isomorphism for an open immersion `j : U ⟶ X`, since `j^*` is restriction to `U_proét`,
  which commutes with sheafification, and `V ×_X U = V` for `V ∈ U_proét`.

The instances `AddCommGrpCat.hasFunctorialFlatResolution` and the strong monoidality of `f^*`,
which are not specific to the coefficient ring objects, are imported from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The pullback of functions along `V ×_Y X → V` on the presheaves of rings -/

section Presheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of functions along the projection `V ×_Y X → V`, as a morphism of presheaves
of rings `P_Y ⟶ (V ↦ P_X(V ×_Y X))` on `Y_proét`, where `P_X` is the presheaf of continuous
maps into `ℚ̄_ℓ` with values in a finite subextension of `ℚ_ℓ`: the pushforward of `P_X` along
`f : X ⟶ Y` is the presheaf `V ↦ P_X(V ×_Y X)`, and the pullback of a function with values in
a finite subextension has values in the same subextension. -/
noncomputable def padicAlgClRingPresheafPushforwardHom :
    padicAlgClRingPresheaf Y ℓ ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op ⋙ padicAlgClRingPresheaf X ℓ where
  app V := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((((ContinuousMap.compRightAlgHom ℤ (PadicAlgCl ℓ)
          (pullback.fst V.unop.hom f).base.hom).toRingHom).comp
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _).subtype).codRestrict
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _) (fun h ↦ by
            obtain ⟨E, hE, hh⟩ := h.2
            exact ⟨E, hE, fun x ↦ hh _⟩)).comp ULift.ringEquiv.toRingHom))
  naturality {V V'} φ := by
    ext (h : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ V.unop.left))
    refine ULift.ext _ _ (Subtype.ext ?_)
    have key : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map φ.unop).left ≫
        pullback.fst V.unop.hom f = pullback.fst V'.unop.hom f ≫ φ.unop.left := by
      rw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
    change (h.down.1.comp φ.unop.left.base.hom).comp (pullback.fst V'.unop.hom f).base.hom =
      (h.down.1.comp (pullback.fst V.unop.hom f).base.hom).comp
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map φ.unop).left.base.hom
    rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← TopCat.hom_comp,
      ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, key]

lemma padicAlgClRingPresheafPushforwardHom_app_apply (V : Y.ProEtᵒᵖ)
    (h : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ V.unop.left)) :
    ((padicAlgClRingPresheafPushforwardHom ℓ f).app V h).down.1 =
      h.down.1.comp (pullback.fst V.unop.hom f).base.hom :=
  rfl

/-- The morphism of abelian presheaves `P_Y ⟶ f_* ℚ̄_ℓ,X` underlying the pullback of functions
along the projections `V ×_Y X → V`, followed by the sheafification map `P_X ⟶ ℚ̄_ℓ,X`: the
presheaf-level morphism whose adjoint under the sheafification adjunction is `η_f`. -/
noncomputable def padicAlgClPresheafPushforwardHom :
    padicAlgClRingPresheaf Y ℓ ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} ⟶
      ((f)_*[Ab.{u + 1}].obj (padicAlgClSheaf X ℓ)).obj :=
  Functor.whiskerRight (padicAlgClRingPresheafPushforwardHom ℓ f)
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) ≫
    Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
      (toSheafify (Scheme.ProEt.topology X)
        (padicAlgClRingPresheaf X ℓ ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}))

end Presheaf

/-! ### The canonical coefficient morphisms -/

section CoefficientHom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical coefficient morphism `η_f : ℚ̄_ℓ,Y ⟶ f_* ℚ̄_ℓ,X`: the morphism of sheaves
adjoint, under the sheafification adjunction, to the pullback of functions along the projections
`V ×_Y X → V` followed by the sheafification map `P_X ⟶ ℚ̄_ℓ,X`, the target `f_* ℚ̄_ℓ,X` being a
sheaf. -/
noncomputable def padicAlgClPushforwardHom :
    padicAlgClSheaf Y ℓ ⟶ (f)_*[Ab.{u + 1}].obj (padicAlgClSheaf X ℓ) :=
  ObjectProperty.homMk (sheafifyLift (Scheme.ProEt.topology Y)
    (padicAlgClPresheafPushforwardHom ℓ f) ((f)_*[Ab.{u + 1}].obj (padicAlgClSheaf X ℓ)).property)

lemma padicAlgClPushforwardHom_hom :
    (padicAlgClPushforwardHom ℓ f).hom = sheafifyLift (Scheme.ProEt.topology Y)
      (padicAlgClPresheafPushforwardHom ℓ f)
      ((f)_*[Ab.{u + 1}].obj (padicAlgClSheaf X ℓ)).property :=
  rfl

/-- `η_f` is characterised by its restriction along the sheafification map `P_Y ⟶ ℚ̄_ℓ,Y`,
which is the pullback of functions followed by the sheafification map `P_X ⟶ ℚ̄_ℓ,X`. -/
@[reassoc]
lemma toSheafify_padicAlgClPushforwardHom_hom :
    toSheafify (Scheme.ProEt.topology Y)
        (padicAlgClRingPresheaf Y ℓ ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ≫
      (padicAlgClPushforwardHom ℓ f).hom = padicAlgClPresheafPushforwardHom ℓ f := by
  rw [padicAlgClPushforwardHom_hom, toSheafify_sheafifyLift]

/-- `η_f` is a morphism of ring objects, for the ring object structure of `f_* ℚ̄_ℓ,X` induced
by the lax monoidal structure of `f_*`. See the module docstring. -/
instance isMonHom_padicAlgClPushforwardHom : IsMonHom (padicAlgClPushforwardHom ℓ f) :=
  sorry

/-- `η` of the identity is the identification `ℚ̄_ℓ,X ≅ (𝟙 X)_* ℚ̄_ℓ,X`: both are determined by
their restrictions to `P_X`, which are the pullback of functions along the identification
`V ×_X X ≅ V` followed by the sheafification map. -/
lemma padicAlgClPushforwardHom_id (X : Scheme.{u}) :
    padicAlgClPushforwardHom ℓ (𝟙 X) =
      (ProEtale.lowerStarId Ab.{u + 1} X).inv.app (padicAlgClSheaf X ℓ) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((𝟙 X)_*[Ab.{u + 1}].obj (padicAlgClSheaf X ℓ)).property
  rw [toSheafify_padicAlgClPushforwardHom_hom]
  ext V
  have key : ((ProEt.overPullbackId X).hom.app V.unop).left = pullback.fst V.unop.hom (𝟙 X) := by
    simp [ProEt.overPullbackId, conjugateEquiv_apply_app]
  -- the presheaf-level identity: both sides are the pullback of functions along
  -- `V ×_X X ≅ V`
  have hP : (padicAlgClRingPresheafPushforwardHom ℓ (𝟙 X)).app V =
      (padicAlgClRingPresheaf X ℓ).map ((ProEt.overPullbackId X).hom.app V.unop).op := by
    ext (h : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ V.unop.left))
    refine ULift.ext _ _ (Subtype.ext ?_)
    change h.down.1.comp (pullback.fst V.unop.hom (𝟙 X)).base.hom =
      h.down.1.comp ((ProEt.overPullbackId X).hom.app V.unop).left.base.hom
    rw [key]
  have e : ((ProEtale.lowerStarId Ab.{u + 1} X).inv.app (padicAlgClSheaf X ℓ)).hom.app V =
      (padicAlgClSheaf X ℓ).obj.map ((ProEt.overPullbackId X).hom.app V.unop).op := rfl
  rw [NatTrans.comp_app, e, ← NatTrans.naturality, padicAlgClPresheafPushforwardHom,
    NatTrans.comp_app, Functor.whiskerRight_app, hP]
  rfl

/-- `η` of a composition is the composition of the `η`'s, up to the composition isomorphism
`g_* ∘ f_* ≅ (f ≫ g)_*`: both are determined by their restrictions to `P_Z`, which are the
pullback of functions along the projection `V ×_Z X → V`, the composition of the projections
`(V ×_Z Y) ×_Y X → V ×_Z Y` and `V ×_Z Y → V` up to the identification
`(V ×_Z Y) ×_Y X ≅ V ×_Z X`, followed by the sheafification map. -/
lemma padicAlgClPushforwardHom_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    padicAlgClPushforwardHom ℓ (f ≫ g) =
      padicAlgClPushforwardHom ℓ g ≫ (g)_*[Ab.{u + 1}].map (padicAlgClPushforwardHom ℓ f) ≫
        (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app (padicAlgClSheaf X ℓ) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((f ≫ g)_*[Ab.{u + 1}].obj (padicAlgClSheaf X ℓ)).property
  rw [toSheafify_padicAlgClPushforwardHom_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, toSheafify_padicAlgClPushforwardHom_hom_assoc]
  ext V : 2
  have key := MorphismProperty.Over.pullbackComp_left_fst_fst (P := @WeaklyEtale) (Q := ⊤) f g
    V.unop
  -- the presheaf-level identity: the pullback of functions along `V ×_Z X → V` is the
  -- composition of the pullbacks along `(V ×_Z Y) ×_Y X → V ×_Z Y → V`, up to
  -- `(V ×_Z Y) ×_Y X ≅ V ×_Z X`
  have hP : (padicAlgClRingPresheafPushforwardHom ℓ (f ≫ g)).app V =
      (padicAlgClRingPresheafPushforwardHom ℓ g).app V ≫
        (padicAlgClRingPresheafPushforwardHom ℓ f).app
          (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) ≫
        (padicAlgClRingPresheaf X ℓ).map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app
            V.unop).op := by
    ext (h : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ V.unop.left))
    refine ULift.ext _ _ (Subtype.ext ?_)
    change h.down.1.comp (pullback.fst V.unop.hom (f ≫ g)).base.hom =
      ((h.down.1.comp (pullback.fst V.unop.hom g).base.hom).comp
        (pullback.fst (pullback.snd V.unop.hom g) f).base.hom).comp
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app
            V.unop).left.base.hom
    rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← TopCat.hom_comp,
      ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, Category.assoc, key]
  have e : ((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app (padicAlgClSheaf X ℓ)).hom.app V =
      (padicAlgClSheaf X ℓ).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app
          V.unop).op := rfl
  have e' : ((g)_*[Ab.{u + 1}].map (padicAlgClPushforwardHom ℓ f)).hom.app V =
      (padicAlgClPushforwardHom ℓ f).hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) := rfl
  have e'' : (toSheafify (Scheme.ProEt.topology Y)
        (padicAlgClRingPresheaf Y ℓ ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})).app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.obj V) ≫
      (padicAlgClPushforwardHom ℓ f).hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) =
      (padicAlgClPresheafPushforwardHom ℓ f).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.obj V) :=
    NatTrans.congr_app (toSheafify_padicAlgClPushforwardHom_hom ℓ f)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.obj V)
  simp only [NatTrans.comp_app, padicAlgClPresheafPushforwardHom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] at e'' ⊢
  rw [e, e', reassoc_of% e'', ← NatTrans.naturality, hP, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc]
  rfl

/-- The canonical coefficient morphism `α_f : f^* ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,X`: the mate of
`η_f : ℚ̄_ℓ,Y ⟶ f_* ℚ̄_ℓ,X` under the adjunction `f^* ⊣ f_*`. It is a morphism of ring objects,
but not an isomorphism in general. -/
noncomputable def padicAlgClPullbackHom :
    (f)^*[Ab.{u + 1}].obj (padicAlgClSheaf Y ℓ) ⟶ padicAlgClSheaf X ℓ :=
  (f)^*[Ab.{u + 1}].map (padicAlgClPushforwardHom ℓ f) ≫
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counitAlgHom (padicAlgClSheaf X ℓ)

/-- `α_f` is a morphism of ring objects. -/
instance isMonHom_padicAlgClPullbackHom : IsMonHom (padicAlgClPullbackHom ℓ f) :=
  inferInstanceAs (IsMonHom ((f)^*[Ab.{u + 1}].map (padicAlgClPushforwardHom ℓ f) ≫
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counitAlgHom (padicAlgClSheaf X ℓ)))

/-- `η_f` is the mate of `α_f`: it is the unit `ℚ̄_ℓ,Y ⟶ f_* f^* ℚ̄_ℓ,Y` followed by `f_* α_f`. -/
@[reassoc]
lemma unitAlgHom_comp_map_padicAlgClPullbackHom :
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (padicAlgClSheaf Y ℓ) ≫
      (f)_*[Ab.{u + 1}].map (padicAlgClPullbackHom ℓ f) =
        padicAlgClPushforwardHom ℓ f := by
  rw [padicAlgClPullbackHom, Functor.map_comp, ← Category.assoc, Adjunction.unitAlgHom,
    Adjunction.counitAlgHom, Adjunction.unit_naturality, Category.assoc,
    Adjunction.right_triangle_components, Category.comp_id]

/-- For an open immersion `j : U ⟶ X`, the canonical coefficient morphism
`α_j : j^* ℚ̄_ℓ,X ⟶ ℚ̄_ℓ,U` is an isomorphism. See the module docstring. -/
instance isIso_padicAlgClPullbackHom_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (padicAlgClPullbackHom ℓ j) :=
  sorry

end CoefficientHom

end AlgebraicGeometry.ProEtale
