/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Basic

/-!

# The coefficient inclusions `E_X ⟶ F_X ⟶ ℚ̄_ℓ,X` and the coefficient morphisms `η_f`

Let `ℓ` be a prime and `X` a scheme. The finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` form the
directed poset `PadicAlgCl.FiniteIntermediateField ℓ`, and
`WeilConjectures.CategoryTheory.RingObjects.EllAdic` exhibits the `ℚ̄_ℓ`-sheaf `ℚ̄_ℓ,X` as the
colimit of the sheaves `E_X = C(-, E)` over this poset (`ProEtale.isColimitPadicAlgClSheafCocone`,
the input **A0.1** of the 2-colimit description of the `ℚ̄_ℓ`-coefficients). This file records
what the module-object six functors need on top of that:

* the ring objects `E_X` of abelian sheaves (`ProEtale.padicSubfieldRingObj`) and the
  inclusions `E_X ⟶ F_X` for `E ≤ F` (`ProEtale.padicSubfieldRingObjMap`, the abelian sheaf
  morphism underlying `ProEtale.padicSubfieldSheafMapOfLE`), as morphisms of ring objects,
  strictly functorial in `E ≤ F`, together with their compatibility with the inclusions
  `E_X ⟶ ℚ̄_ℓ,X` (`ProEtale.padicSubfieldRingObjMap_comp_toPadicAlgClSheaf`);
* the canonical coefficient morphisms `η_f : E_Y ⟶ f_* E_X` of the ring objects `E_X`
  (`ProEtale.padicSubfieldPushforwardHom`, the pullback of functions of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.ContinuousMap` for the
  topological ring `E`);
* **(A0.3)** their compatibility with the coefficient inclusions: the squares
  ```
      E_Y ---> F_Y             E_Y ---> ℚ̄_ℓ,Y
       |        |                |         |
      η_f      η_f              η_f       η_f
       ↓        ↓                ↓         ↓
    f_* E_X -> f_* F_X        f_* E_X -> f_* ℚ̄_ℓ,X
  ```
  commute (`ProEtale.padicSubfieldPushforwardHom_comp_map`,
  `ProEtale.padicSubfieldPushforwardHom_comp_map_toPadicAlgClSheaf`): on the presheaves of
  functions, both composites are "pull back along `V ×_Y X → V`, then include the values". The
  corresponding squares for the mates `α_f` follow formally
  (`CategoryTheory.Adjunction.pullbackHom_square`), without assuming `α_f` to be invertible.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

instance : CoeSort (FiniteIntermediateField ℓ) Type := ⟨fun E ↦ E.1⟩

/-- The poset of finite subextensions, as a category, is filtered: it is directed and
nonempty. -/
instance : IsFiltered (FiniteIntermediateField ℓ) := isFiltered_of_directed_le_nonempty _

end PadicAlgCl

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{u}] [(J.W (A := Ab.{u})).IsMonoidal]
  [J.HasSheafCompose (forget₂ RingCat.{u} Ab.{u})]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

omit [(J.W (A := Ab.{u})).IsMonoidal] in
/-- The inverse of the counit isomorphism `(S.obj)^# ≅ S` of a sheaf of rings `S` is the
sheafification map `S.obj ⟶ (S.obj)^#`, by the triangle identity of the sheafification
adjunction. -/
lemma sheafifyRingPresheafIso_inv_hom (S : Sheaf J RingCat.{u}) :
    (sheafifyRingPresheafIso J S).inv.hom =
      toSheafify J (S.obj ⋙ forget₂ RingCat.{u} Ab.{u}) := by
  have : IsIso (sheafifyRingPresheafIso J S).hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf J Ab.{u}).map (sheafifyRingPresheafIso J S).hom))
  rw [← cancel_mono (sheafifyRingPresheafIso J S).hom.hom,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id]
  exact ((sheafificationAdjunction J Ab.{u}).right_triangle_components
    ((sheafCompose J (forget₂ RingCat.{u} Ab.{u})).obj S)).symm

omit [(J.W (A := Ab.{u})).IsMonoidal] in
/-- The morphism of ring objects `S ⟶ Q^#` induced by a morphism of presheaves of rings
`S.obj ⟶ Q` is, on sections, the morphism followed by the sheafification map. -/
lemma sheafComposeToSheafify_hom (S : Sheaf J RingCat.{u}) {Q : Cᵒᵖ ⥤ RingCat.{u}}
    (g : S.obj ⟶ Q) :
    (sheafComposeToSheafify J S g).hom =
      Functor.whiskerRight g (forget₂ RingCat.{u} Ab.{u}) ≫
        toSheafify J (Q ⋙ forget₂ RingCat.{u} Ab.{u}) := by
  rw [sheafComposeToSheafify, ObjectProperty.FullSubcategory.comp_hom,
    sheafifyRingPresheafIso_inv_hom]
  exact (toSheafify_naturality J _).symm

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The ring objects `E_X` and their inclusions -/

section RingObj

/-- The ring object `E_X = C(-, E)` of abelian pro-étale sheaves on `X`, for a finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` with the topology restricted from `ℚ̄_ℓ`: the abelian sheaf
underlying the sheaf of rings `ProEtale.padicSubfieldSheaf X ℓ E`. -/
noncomputable abbrev padicSubfieldRingObj (E : FiniteIntermediateField ℓ) :
    Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicSubfieldSheaf X ℓ E)

instance (E : FiniteIntermediateField ℓ) : IsCommMonObj (padicSubfieldRingObj X ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  isCommMonObj_continuousMapRingSheaf X E

/-- The inclusion `E_X ⟶ F_X` of the ring objects of abelian sheaves, for finite subextensions
`E ≤ F`: the abelian sheaf morphism underlying `ProEtale.padicSubfieldSheafMapOfLE`, the
postcomposition with the inclusion `E ⊆ F`. It is a morphism of ring objects. -/
noncomputable def padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObj X ℓ E ⟶ padicSubfieldRingObj X ℓ F :=
  (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicSubfieldSheafMapOfLE X ℓ h)

instance {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsMonHom (padicSubfieldRingObjMap X ℓ h) :=
  inferInstanceAs (IsMonHom ((sheafCompose (ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicSubfieldSheafMapOfLE X ℓ h)))

lemma padicSubfieldRingObjMap_id (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObjMap X ℓ (le_refl E) = 𝟙 _ := rfl

lemma padicSubfieldRingObjMap_comp {E F H : FiniteIntermediateField ℓ} (h₁ : E ≤ F) (h₂ : F ≤ H) :
    padicSubfieldRingObjMap X ℓ (h₁.trans h₂) =
      padicSubfieldRingObjMap X ℓ h₁ ≫ padicSubfieldRingObjMap X ℓ h₂ := rfl

/-- The coefficient system `E ↦ E_X` of the finite subextensions of `ℚ_ℓ`, as a functor from
the poset of finite subextensions to the abelian pro-étale sheaves on `X`: the diagram whose
colimit is `ℚ̄_ℓ,X` (`ProEtale.isColimitPadicAlgClSheafCocone`). -/
noncomputable abbrev padicSubfieldRingObjFunctor :
    FiniteIntermediateField ℓ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  padicSubfieldSheafFunctor X ℓ ⋙
    sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})

lemma padicSubfieldRingObjFunctor_map {E F : FiniteIntermediateField ℓ} (h : E ⟶ F) :
    (padicSubfieldRingObjFunctor X ℓ).map h = padicSubfieldRingObjMap X ℓ (leOfHom h) := rfl

/-- The inclusion `E_X ⟶ F_X` followed by the inclusion `F_X ⟶ ℚ̄_ℓ,X` is the inclusion
`E_X ⟶ ℚ̄_ℓ,X`: the naturality of the colimit cocone `ProEtale.padicAlgClSheafCocone`. -/
lemma padicSubfieldRingObjMap_comp_toPadicAlgClSheaf {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldSheafToPadicAlgClSheaf X ℓ F =
      padicSubfieldSheafToPadicAlgClSheaf X ℓ E := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F
  unfold padicSubfieldSheafToPadicAlgClSheaf continuousMapRingSheafToPadicAlgClSheaf
  rw [padicSubfieldRingObjMap, Sheaf.sheafCompose_map_comp_sheafComposeToSheafify]
  congr 1

end RingObj

/-! ### The compatibility of the coefficient morphisms `η_f` with the inclusions -/

section Pushforward

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical coefficient morphism `η_f : E_Y ⟶ f_* E_X` of the ring object `E_X = C(-, E)`
of a finite subextension `E`: the pullback of continuous functions along the projections
`V ×_Y X → V`. -/
noncomputable def padicSubfieldPushforwardHom (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObj Y ℓ E ⟶ (f)_*[Ab.{u + 1}].obj (padicSubfieldRingObj X ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapPushforwardHom E f

instance (E : FiniteIntermediateField ℓ) : IsMonHom (padicSubfieldPushforwardHom ℓ f E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  inferInstanceAs (IsMonHom (continuousMapPushforwardHom E f))

/-- **(A0.3)** The coefficient morphisms `η_f` are compatible with the inclusions `E_X ⟶ F_X`:
on sections over `V`, both composites send a function `h : V → E` to the function
`V ×_Y X → F` obtained by pulling back along the projection and including the values. -/
lemma padicSubfieldPushforwardHom_comp_map {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldPushforwardHom ℓ f E ≫ (f)_*[Ab.{u + 1}].map (padicSubfieldRingObjMap X ℓ h) =
      padicSubfieldRingObjMap Y ℓ h ≫ padicSubfieldPushforwardHom ℓ f F := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F
  apply Sheaf.hom_ext
  ext V (g : ULift.{u + 1} C(V.unop.left, E))
  rfl

/-- **(A0.3)** The coefficient morphisms `η_f` are compatible with the inclusions
`E_X ⟶ ℚ̄_ℓ,X`: on sections over `V`, both composites send a function `h : V → E` to the class
in `ℚ̄_ℓ,X(V ×_Y X)` of the function `V ×_Y X → ℚ̄_ℓ` obtained by pulling back along the
projection and including the values, which takes values in the finite subextension `E`. -/
lemma padicSubfieldPushforwardHom_comp_map_toPadicAlgClSheaf (E : FiniteIntermediateField ℓ) :
    padicSubfieldPushforwardHom ℓ f E ≫
        (f)_*[Ab.{u + 1}].map (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) =
      padicSubfieldSheafToPadicAlgClSheaf Y ℓ E ≫ padicAlgClPushforwardHom ℓ f := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  apply Sheaf.hom_ext
  change (padicSubfieldPushforwardHom ℓ f E).hom ≫
      Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
        (padicSubfieldSheafToPadicAlgClSheaf X ℓ E).hom =
    (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E).hom ≫ (padicAlgClPushforwardHom ℓ f).hom
  simp only [padicSubfieldSheafToPadicAlgClSheaf, continuousMapRingSheafToPadicAlgClSheaf,
    Sheaf.sheafComposeToSheafify_hom]
  rw [Category.assoc, toSheafify_padicAlgClPushforwardHom_hom, padicAlgClPresheafPushforwardHom,
    Functor.whiskerLeft_comp, ← Category.assoc, ← Category.assoc]
  congr 1

end Pushforward

end AlgebraicGeometry.ProEtale
