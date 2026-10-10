/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Monoidal

/-!

# The canonical coefficient morphisms of the sheaves of continuous functions

Let `T` be a commutative topological ring. For every scheme `X`, the sheaf of rings
`U ↦ C(U, T)` of continuous maps into `T` on the small pro-étale site of `X`
(`AlgebraicGeometry.ProEtale.continuousMapRingSheaf`, a sheaf by Bhatt–Scholze, Lemma 4.2.12)
has an underlying abelian sheaf, which is a commutative ring object
```
A_X(T) := (sheafCompose _ (forget₂ RingCat Ab)).obj (continuousMapRingSheaf X T)
```
of `Ab`-valued pro-étale sheaves (`AlgebraicGeometry.ProEtale.continuousMapRingObj`). This file
constructs the *canonical coefficient morphisms* relating these ring objects along a morphism of
schemes `f : X ⟶ Y`, which is all that the six functors on module objects over `A_X(T)` need:

* `η_f : A_Y(T) ⟶ f_* A_X(T)` (`AlgebraicGeometry.ProEtale.continuousMapPushforwardHom`): for
  `V ∈ Y_proét`, the sections of `f_* A_X(T)` over `V` are `C(V ×_Y X, T)`, and `η_f` is the
  pullback of continuous functions
  ```
  C(V, T) ⟶ C(V ×_Y X, T),   h ↦ h ∘ p_V
  ```
  along the projection `p_V : V ×_Y X → V`
  (`AlgebraicGeometry.ProEtale.continuousMapRingPresheafPushforwardHom`). It is a morphism of
  sheaves of rings, natural in `V`, and compatible with identities and compositions since the
  pullback of functions is (`AlgebraicGeometry.ProEtale.continuousMapPushforwardHom_id`,
  `AlgebraicGeometry.ProEtale.continuousMapPushforwardHom_comp`).
* `α_f : f^* A_Y(T) ⟶ A_X(T)` (`AlgebraicGeometry.ProEtale.continuousMapPullbackHom`): the mate
  of `η_f` under the adjunction `f^* ⊣ f_*`, a morphism of ring objects since `f^*` is strong
  monoidal, see
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Monoidal`.
  It is an isomorphism for an open immersion `f` (indeed for `f` weakly étale, where `f^*` is
  restriction), but not in general.

No adic completeness or Noetherian hypothesis on `T` is needed, and no inverse limit
presentation of `T` enters the definition: the construction applies uniformly to `ℤ_ℓ`, `ℚ_ℓ`, a
subfield `E ⊆ ℚ̄_ℓ` and its ring of integers `𝒪_E` with their valuation topologies, whose
sheaves of rings `ProEtale.padicIntSheaf`, `ProEtale.padicSheaf`, `ProEtale.padicSubfieldSheaf`
and `ProEtale.padicIntegersSheaf` of `WeilConjectures.CategoryTheory.RingObjects.EllAdic` are
instances of `continuousMapRingSheaf` (see the examples at the end of the file). The sheaf
`ℚ̄_ℓ,X` is not of this form and is treated separately, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl`.

The six functors on module objects over `A_X(T)` are built from `η_f` and `α_f` in the other
files of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension`.

## Sorried input

* `AlgebraicGeometry.ProEtale.isMonHom_continuousMapPushforwardHom`: `η_f` is a morphism of
  ring objects, for the ring object structure on `f_* A_X(T)` induced by the lax monoidal
  structure of `f_*`. Both the ring structure of `A_Y(T)` and the lax monoidal structure of
  `f_*` are given by the pointwise multiplication of functions after sheafification (the former
  through `CategoryTheory.Sheaf.monObj_sheafCompose_obj`, the latter through the transport of
  `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`), and `h ↦ h ∘ p_V` is multiplicative
  and unital; the proof is the identification of these two sheafified pointwise structures.
* `AlgebraicGeometry.ProEtale.isIso_continuousMapPullbackHom_of_isOpenImmersion`: `α_j` is an
  isomorphism for an open immersion `j : U ⟶ X`, since `j^*` is restriction to `U_proét` and
  `V ×_X U = V` for `V ∈ U_proét`.
* `AddCommGrpCat.hasFunctorialFlatResolution`: abelian groups admit functorial flat
  resolutions, by free abelian groups; it is what makes the derived functors with values in
  `Ab` available.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj

/-- Abelian groups admit functorial flat resolutions, by free abelian groups: the free abelian
group on the underlying set of `M` is flat, and surjects functorially onto `M`. -/
instance AddCommGrpCat.hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution Ab.{u} :=
  sorry

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The pullback of continuous functions along `V ×_Y X → V` -/

section Ring

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The pullback of continuous functions along the projection `V ×_Y X → V`, as a morphism of
presheaves of rings `C(-, T) ⟶ (V ↦ C(V ×_Y X, T))` on `Y_proét`: the pushforward of
`C(-, T)_X` along `f : X ⟶ Y` is the presheaf `V ↦ C(V ×_Y X, T)`. -/
noncomputable def continuousMapRingPresheafPushforwardHom :
    continuousMapRingPresheaf Y T ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op ⋙ continuousMapRingPresheaf X T where
  app V := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T
        (pullback.fst V.unop.hom f).base.hom).toRingHom).comp ULift.ringEquiv.toRingHom))
  naturality {V V'} φ := by
    ext (h : ULift.{u + 1} C(V.unop.left, T))
    have key : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map φ.unop).left ≫
        pullback.fst V.unop.hom f = pullback.fst V'.unop.hom f ≫ φ.unop.left := by
      rw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
    change ULift.up ((h.down.comp φ.unop.left.base.hom).comp
        (pullback.fst V'.unop.hom f).base.hom) =
      ULift.up ((h.down.comp (pullback.fst V.unop.hom f).base.hom).comp
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map φ.unop).left.base.hom)
    rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← TopCat.hom_comp,
      ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, key]

lemma continuousMapRingPresheafPushforwardHom_app_apply (V : Y.ProEtᵒᵖ)
    (h : ULift.{u + 1} C(V.unop.left, T)) :
    (continuousMapRingPresheafPushforwardHom f T).app V h =
      ULift.up (h.down.comp (pullback.fst V.unop.hom f).base.hom) :=
  rfl

/-- The pullback of continuous functions along the projections `V ×_Y X → V`, as a morphism of
sheaves of rings `C(-, T)_Y ⟶ f_* C(-, T)_X` on `Y_proét`. -/
noncomputable def continuousMapRingSheafPushforwardHom :
    continuousMapRingSheaf Y T ⟶
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).sheafPushforwardContinuous
        RingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          (continuousMapRingSheaf X T) :=
  ⟨continuousMapRingPresheafPushforwardHom f T⟩

end Ring

/-! ### The ring objects `A_X(T)` and the canonical coefficient morphisms -/

section CommRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The coefficient ring object `A_X(T)` of abelian sheaves on `X_proét`: the abelian sheaf
underlying the sheaf of rings `U ↦ C(U, T)`, with its ring object structure
`CategoryTheory.Sheaf.monObj_sheafCompose_obj`, commutative by
`ProEtale.isCommMonObj_continuousMapRingSheaf`. -/
noncomputable abbrev continuousMapRingObj (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (continuousMapRingSheaf X T)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical coefficient morphism `η_f : A_Y(T) ⟶ f_* A_X(T)`: the pullback of continuous
functions along the projections `V ×_Y X → V`, as a morphism of abelian sheaves. -/
noncomputable def continuousMapPushforwardHom :
    continuousMapRingObj T Y ⟶ (f)_*[Ab.{u + 1}].obj (continuousMapRingObj T X) :=
  (sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafPushforwardHom f T)

/-- `η_f` is a morphism of ring objects, for the ring object structure of `f_* A_X(T)` induced
by the lax monoidal structure of `f_*`. See the module docstring. -/
instance isMonHom_continuousMapPushforwardHom : IsMonHom (continuousMapPushforwardHom T f) :=
  sorry

/-- `η` of the identity is the identification `A_X(T) ≅ (𝟙 X)_* A_X(T)`: both are, on sections
over `V`, the pullback of functions along the identification `V ×_X X ≅ V`. -/
lemma continuousMapPushforwardHom_id (X : Scheme.{u}) :
    continuousMapPushforwardHom T (𝟙 X) =
      (ProEtale.lowerStarId Ab.{u + 1} X).inv.app (continuousMapRingObj T X) := by
  apply Sheaf.hom_ext
  ext V (h : ULift.{u + 1} C(V.unop.left, T))
  have key : ((ProEt.overPullbackId X).hom.app V.unop).left = pullback.fst V.unop.hom (𝟙 X) := by
    simp [ProEt.overPullbackId, conjugateEquiv_apply_app]
  change ULift.up (h.down.comp (pullback.fst V.unop.hom (𝟙 X)).base.hom) =
    ULift.up (h.down.comp ((ProEt.overPullbackId X).hom.app V.unop).left.base.hom)
  rw [key]

/-- `η` of a composition is the composition of the `η`'s, up to the composition isomorphism
`g_* ∘ f_* ≅ (f ≫ g)_*`: on sections over `V`, both are the pullback of functions along the
projection `V ×_Z X → V`, which is the composition of the projections `(V ×_Z Y) ×_Y X → V ×_Z Y`
and `V ×_Z Y → V` up to the identification `(V ×_Z Y) ×_Y X ≅ V ×_Z X`. -/
lemma continuousMapPushforwardHom_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    continuousMapPushforwardHom T (f ≫ g) =
      continuousMapPushforwardHom T g ≫ (g)_*[Ab.{u + 1}].map (continuousMapPushforwardHom T f) ≫
        (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app (continuousMapRingObj T X) := by
  apply Sheaf.hom_ext
  ext V (h : ULift.{u + 1} C(V.unop.left, T))
  have key := MorphismProperty.Over.pullbackComp_left_fst_fst (P := @WeaklyEtale) (Q := ⊤) f g
    V.unop
  change ULift.up (h.down.comp (pullback.fst V.unop.hom (f ≫ g)).base.hom) =
    ULift.up (((h.down.comp (pullback.fst V.unop.hom g).base.hom).comp
      (pullback.fst (pullback.snd V.unop.hom g) f).base.hom).comp
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app
          V.unop).left.base.hom)
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← TopCat.hom_comp,
    ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, Category.assoc, key]

/-- The canonical coefficient morphism `α_f : f^* A_Y(T) ⟶ A_X(T)`: the mate of
`η_f : A_Y(T) ⟶ f_* A_X(T)` under the adjunction `f^* ⊣ f_*`. It is a morphism of ring objects,
but not an isomorphism in general. -/
noncomputable def continuousMapPullbackHom :
    (f)^*[Ab.{u + 1}].obj (continuousMapRingObj T Y) ⟶ continuousMapRingObj T X :=
  (f)^*[Ab.{u + 1}].map (continuousMapPushforwardHom T f) ≫
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counitAlgHom (continuousMapRingObj T X)

/-- `α_f` is a morphism of ring objects. -/
instance isMonHom_continuousMapPullbackHom : IsMonHom (continuousMapPullbackHom T f) :=
  inferInstanceAs (IsMonHom ((f)^*[Ab.{u + 1}].map (continuousMapPushforwardHom T f) ≫
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counitAlgHom
      (continuousMapRingObj T X)))

/-- `η_f` is the mate of `α_f`: it is the unit `A_Y(T) ⟶ f_* f^* A_Y(T)` followed by
`f_* α_f`. -/
@[reassoc]
lemma unitAlgHom_comp_map_continuousMapPullbackHom :
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (continuousMapRingObj T Y) ≫
      (f)_*[Ab.{u + 1}].map (continuousMapPullbackHom T f) =
        continuousMapPushforwardHom T f := by
  rw [continuousMapPullbackHom, Functor.map_comp, ← Category.assoc, Adjunction.unitAlgHom,
    Adjunction.counitAlgHom, Adjunction.unit_naturality, Category.assoc,
    Adjunction.right_triangle_components, Category.comp_id]

/-- For an open immersion `j : U ⟶ X`, the canonical coefficient morphism
`α_j : j^* A_X(T) ⟶ A_U(T)` is an isomorphism. See the module docstring. -/
instance isIso_continuousMapPullbackHom_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (continuousMapPullbackHom T j) :=
  sorry

end CommRing

/-! ### The `ℓ`-adic coefficient sheaves -/

section EllAdic

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The ring object `ℤ_ℓ,X = C(-, ℤ_ℓ)` is `A_X(ℤ_ℓ)`. -/
example : continuousMapRingObj ℤ_[ℓ] X =
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (padicIntSheaf X ℓ) :=
  rfl

/-- The ring object `ℚ_ℓ,X = C(-, ℚ_ℓ)` is `A_X(ℚ_ℓ)`. -/
example : continuousMapRingObj ℚ_[ℓ] X =
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (padicSheaf X ℓ) :=
  rfl

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The ring object `E_X = C(-, E)` of a subfield `E ⊆ ℚ̄_ℓ`, with the topology restricted from
`ℚ̄_ℓ`, is `A_X(E)`. No `ℓ`-adic completion is involved: `ℓ` is invertible in `E`. -/
example :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    continuousMapRingObj E X =
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicSubfieldSheaf X ℓ E) :=
  rfl

/-- The ring object `𝒪_{E,X} = C(-, 𝒪_E)` of the ring of integers of a subfield `E ⊆ ℚ̄_ℓ`, with
the topology restricted from `ℚ̄_ℓ`, is `A_X(𝒪_E)`. For a finite extension `E`, the derived
`𝔪_E`-complete objects are the intended domain of the exceptional operations; this is a choice
of subcategory on which the functors act, and does not change the coefficient morphisms. -/
example :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    continuousMapRingObj (PadicAlgCl.integers ℓ E) X =
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntegersSheaf X ℓ E) :=
  rfl

end EllAdic

end AlgebraicGeometry.ProEtale
