/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Basic

/-!

# The coefficient system `E ↦ E_X` of the finite subextensions of `ℚ_ℓ` and its colimit `ℚ̄_ℓ,X`

Let `ℓ` be a prime and `X` a scheme. The *finite subextensions* `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` form a
directed poset `PadicAlgCl.FiniteSubext ℓ` (`E ⊔ F` is again finite). For each of them, the
ring object `E_X = C(-, E)` of abelian pro-étale sheaves on `X`
(`AlgebraicGeometry.ProEtale.padicSubfieldRingObj`, the abelian sheaf underlying
`ProEtale.padicSubfieldSheaf X ℓ E` of `WeilConjectures.CategoryTheory.RingObjects.EllAdic`)
comes with its canonical coefficient morphisms `η_f : E_Y ⟶ f_* E_X`
(`AlgebraicGeometry.ProEtale.padicSubfieldPushforwardHom`, the pullback of functions of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.ContinuousMap`). This file
records the *coefficient inclusions* and their compatibilities, which are the input **A0** of
the 2-colimit description of the `ℚ̄_ℓ`-coefficients:

* `ProEtale.padicSubfieldRingObjMap h : E_X ⟶ F_X` for `E ≤ F`, the postcomposition with the
  inclusion `E ⊆ F`, a morphism of ring objects, functorial in `E ≤ F`
  (`ProEtale.padicSubfieldRingObjMap_id`, `ProEtale.padicSubfieldRingObjMap_comp`), so that
  `E ↦ E_X` is a functor `ProEtale.padicSubfieldRingObjFunctor X ℓ` on the poset of finite
  subextensions;
* the inclusion `E_X ⟶ ℚ̄_ℓ,X` into the `ℚ̄_ℓ`-sheaf `ProEtale.padicAlgClSheaf X ℓ`
  (`ProEtale.padicSubfieldSheafToPadicAlgClSheaf` of
  `WeilConjectures.CategoryTheory.RingObjects.EllAdic`), compatible with the inclusions
  `E_X ⟶ F_X` (`ProEtale.padicSubfieldRingObjMap_comp_toPadicAlgClSheaf`), so that these
  inclusions form a cocone `ProEtale.padicAlgClSheafCocone X ℓ` on the functor `E ↦ E_X` with
  vertex `ℚ̄_ℓ,X`;
* **(A0.1)** this cocone is a colimit: `ℚ̄_ℓ,X ≃ colim_E E_X`
  (`ProEtale.padicAlgClSheaf_isColimit`), compatibly with the inclusions and, through the
  squares below, with the morphisms of schemes;
* **(A0.3)** the coefficient morphisms `η_f` are compatible with the coefficient inclusions:
  the squares
  ```
      E_Y ---> F_Y             E_Y ---> ℚ̄_ℓ,Y
       |        |                |         |
      η_f      η_f              η_f       η_f
       ↓        ↓                ↓         ↓
    f_* E_X -> f_* F_X        f_* E_X -> f_* ℚ̄_ℓ,X
  ```
  commute (`ProEtale.padicSubfieldPushforwardHom_comp_map`,
  `ProEtale.padicSubfieldPushforwardHom_comp_map_toPadicAlgClSheaf`): on the presheaves of
  functions, both composites are "pull back along `V ×_Y X → V`, then include the values".
  The corresponding squares for the mates `α_f` follow formally
  (`ProEtale.ModuleObject.pullbackHom_square`), without assuming `α_f` to be invertible.

## Sorried input

* `ProEtale.padicAlgClSheaf_isColimit`: the cocone of the inclusions `E_X ⟶ ℚ̄_ℓ,X` is a colimit
  of abelian sheaves. The `ℚ̄_ℓ`-sheaf is by definition the sheafification of the presheaf of
  functions with values in some finite subextension, which is objectwise the filtered union of
  the presheaves `C(-, E)` over the finite subextensions `E`, i.e. their colimit in abelian
  presheaves (filtered colimits of abelian groups being unions); the sheafification functor
  preserves colimits, being a left adjoint, and the sheaves `C(-, E)` are their own
  sheafifications. The ring object structures are compatible along the way, so this is a
  colimit of commutative ring objects.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, as a directed poset under inclusion: the
indexing poset of the 2-colimit description of the `ℚ̄_ℓ`-coefficients. -/
abbrev FiniteSubext : Type :=
  {E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) // FiniteDimensional ℚ_[ℓ] E}

namespace FiniteSubext

instance : CoeSort (FiniteSubext ℓ) Type := ⟨fun E ↦ E.1⟩

instance finiteDimensional (E : FiniteSubext ℓ) : FiniteDimensional ℚ_[ℓ] E := E.2

instance : Nonempty (FiniteSubext ℓ) := ⟨⟨⊥, inferInstance⟩⟩

/-- The compositum `E ⊔ F` of two finite subextensions is a finite subextension. -/
noncomputable def sup (E F : FiniteSubext ℓ) : FiniteSubext ℓ :=
  ⟨E.1 ⊔ F.1, IntermediateField.finiteDimensional_sup E.1 F.1⟩

lemma le_sup_left (E F : FiniteSubext ℓ) : E ≤ sup ℓ E F := _root_.le_sup_left (a := E.1)

lemma le_sup_right (E F : FiniteSubext ℓ) : F ≤ sup ℓ E F := _root_.le_sup_right (b := F.1)

/-- The poset of finite subextensions is directed: any two have the compositum as a common
upper bound. -/
noncomputable instance : IsDirected (FiniteSubext ℓ) (· ≤ ·) :=
  ⟨fun E F ↦ ⟨sup ℓ E F, le_sup_left ℓ E F, le_sup_right ℓ E F⟩⟩

/-- The poset of finite subextensions, as a category, is filtered. -/
instance : IsFiltered (FiniteSubext ℓ) := isFiltered_of_directed_le_nonempty _

variable {ℓ} in
/-- The inclusion `E → F` of finite subextensions `E ≤ F`, as a ring homomorphism. -/
noncomputable def inclusion {E F : FiniteSubext ℓ} (h : E ≤ F) : E →+* F :=
  (IntermediateField.inclusion h).toRingHom

variable {ℓ} in
@[simp]
lemma coe_inclusion {E F : FiniteSubext ℓ} (h : E ≤ F) (x : E) :
    (inclusion h x : PadicAlgCl ℓ) = x := rfl

variable {ℓ} in
/-- The inclusion `E → F` is continuous for the topologies restricted from `ℚ̄_ℓ`: composed
with the embedding `F → ℚ̄_ℓ` it is the embedding `E → ℚ̄_ℓ`. -/
lemma continuous_inclusion {E F : FiniteSubext ℓ} (h : E ≤ F) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ F
    Continuous (inclusion h) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F
  exact continuous_induced_rng.mpr continuous_induced_dom

end FiniteSubext

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

omit [(J.W (A := Ab.{u})).IsMonoidal] in
/-- A morphism of sheaves of rings followed by the morphism of ring objects into a
sheafification is the morphism of ring objects into the sheafification induced by the
composite. -/
lemma sheafCompose_map_comp_sheafComposeToSheafify {S T : Sheaf J RingCat.{u}} (f : S ⟶ T)
    {Q : Cᵒᵖ ⥤ RingCat.{u}} (g : T.obj ⟶ Q) :
    (sheafCompose J (forget₂ RingCat.{u} Ab.{u})).map f ≫ sheafComposeToSheafify J T g =
      sheafComposeToSheafify J S (f.hom ≫ g) := by
  apply Sheaf.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, sheafComposeToSheafify_hom,
    sheafComposeToSheafify_hom,
    Functor.whiskerRight_comp, Category.assoc]
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The ring objects `E_X` and their inclusions -/

section RingObj

/-- The ring object `E_X = C(-, E)` of abelian pro-étale sheaves on `X`, for a finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` with the topology restricted from `ℚ̄_ℓ`: the abelian sheaf
underlying the sheaf of rings `ProEtale.padicSubfieldSheaf X ℓ E`. -/
noncomputable abbrev padicSubfieldRingObj (E : FiniteSubext ℓ) :
    Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicSubfieldSheaf X ℓ E)

instance (E : FiniteSubext ℓ) : IsCommMonObj (padicSubfieldRingObj X ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  isCommMonObj_continuousMapRingSheaf X E

/-- The inclusion `E_X ⟶ F_X` of the sheaves of rings of continuous functions, for finite
subextensions `E ≤ F`: postcomposition with the inclusion `E ⊆ F`. -/
noncomputable def padicSubfieldSheafMap {E F : FiniteSubext ℓ} (h : E ≤ F) :
    padicSubfieldSheaf X ℓ E ⟶ padicSubfieldSheaf X ℓ F :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ F
  continuousMapRingSheafMap X (FiniteSubext.inclusion h) (FiniteSubext.continuous_inclusion h)

lemma padicSubfieldSheafMap_hom_app_apply {E F : FiniteSubext ℓ} (h : E ≤ F) (U : X.ProEtᵒᵖ)
    (g : ULift.{u + 1} C(U.unop.left, E)) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ F
    (padicSubfieldSheafMap X ℓ h).hom.app U g =
      ULift.up ((⟨FiniteSubext.inclusion h, FiniteSubext.continuous_inclusion h⟩ : C(E, F)).comp
        g.down) :=
  rfl

lemma padicSubfieldSheafMap_id (E : FiniteSubext ℓ) :
    padicSubfieldSheafMap X ℓ (le_refl E) = 𝟙 _ := by
  apply Sheaf.hom_ext
  ext U (g : ULift.{u + 1} C(U.unop.left, E))
  exact ULift.ext _ _ (ContinuousMap.ext fun _ ↦ Subtype.ext rfl)

lemma padicSubfieldSheafMap_comp {E F H : FiniteSubext ℓ} (h₁ : E ≤ F) (h₂ : F ≤ H) :
    padicSubfieldSheafMap X ℓ (h₁.trans h₂) =
      padicSubfieldSheafMap X ℓ h₁ ≫ padicSubfieldSheafMap X ℓ h₂ := by
  apply Sheaf.hom_ext
  ext U (g : ULift.{u + 1} C(U.unop.left, E))
  exact ULift.ext _ _ (ContinuousMap.ext fun _ ↦ Subtype.ext rfl)

/-- The inclusion `E_X ⟶ F_X` of the ring objects of abelian sheaves, for finite subextensions
`E ≤ F`: postcomposition with the inclusion `E ⊆ F`. It is a morphism of ring objects. -/
noncomputable def padicSubfieldRingObjMap {E F : FiniteSubext ℓ} (h : E ≤ F) :
    padicSubfieldRingObj X ℓ E ⟶ padicSubfieldRingObj X ℓ F :=
  (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicSubfieldSheafMap X ℓ h)

instance {E F : FiniteSubext ℓ} (h : E ≤ F) : IsMonHom (padicSubfieldRingObjMap X ℓ h) :=
  inferInstanceAs (IsMonHom ((sheafCompose (ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicSubfieldSheafMap X ℓ h)))

lemma padicSubfieldRingObjMap_id (E : FiniteSubext ℓ) :
    padicSubfieldRingObjMap X ℓ (le_refl E) = 𝟙 _ := by
  rw [padicSubfieldRingObjMap, padicSubfieldSheafMap_id]
  exact CategoryTheory.Functor.map_id _ _

lemma padicSubfieldRingObjMap_comp {E F H : FiniteSubext ℓ} (h₁ : E ≤ F) (h₂ : F ≤ H) :
    padicSubfieldRingObjMap X ℓ (h₁.trans h₂) =
      padicSubfieldRingObjMap X ℓ h₁ ≫ padicSubfieldRingObjMap X ℓ h₂ := by
  unfold padicSubfieldRingObjMap
  rw [padicSubfieldSheafMap_comp X ℓ h₁ h₂, CategoryTheory.Functor.map_comp]

/-- The coefficient system `E ↦ E_X` of the finite subextensions of `ℚ_ℓ`, as a functor from
the poset of finite subextensions to the abelian pro-étale sheaves on `X`. -/
@[simps]
noncomputable def padicSubfieldRingObjFunctor :
    FiniteSubext ℓ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} where
  obj E := padicSubfieldRingObj X ℓ E
  map h := padicSubfieldRingObjMap X ℓ h.le
  map_id E := padicSubfieldRingObjMap_id X ℓ E
  map_comp h₁ h₂ := padicSubfieldRingObjMap_comp X ℓ h₁.le h₂.le

end RingObj

/-! ### The inclusions into `ℚ̄_ℓ,X` and the colimit -/

section Colimit

/-- The inclusion `E_X ⟶ F_X` followed by the inclusion `F_X ⟶ ℚ̄_ℓ,X` is the inclusion
`E_X ⟶ ℚ̄_ℓ,X`. -/
lemma padicSubfieldRingObjMap_comp_toPadicAlgClSheaf {E F : FiniteSubext ℓ} (h : E ≤ F) :
    padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldSheafToPadicAlgClSheaf X ℓ F =
      padicSubfieldSheafToPadicAlgClSheaf X ℓ E := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F
  unfold padicSubfieldSheafToPadicAlgClSheaf continuousMapRingSheafToPadicAlgClSheaf
  rw [padicSubfieldRingObjMap, Sheaf.sheafCompose_map_comp_sheafComposeToSheafify]
  congr 1

/-- The inclusions `E_X ⟶ ℚ̄_ℓ,X` form a cocone on the coefficient system `E ↦ E_X` with vertex
the `ℚ̄_ℓ`-sheaf. -/
@[simps]
noncomputable def padicAlgClSheafCocone : Cocone (padicSubfieldRingObjFunctor X ℓ) :=
  Cocone.mk (padicAlgClSheaf X ℓ)
    { app E := padicSubfieldSheafToPadicAlgClSheaf X ℓ E
      naturality E F h := by
        dsimp
        rw [Category.comp_id]
        exact padicSubfieldRingObjMap_comp_toPadicAlgClSheaf X ℓ h.le }

/-- **(A0.1)** `ℚ̄_ℓ,X` is the colimit of the ring objects `E_X` over the finite subextensions
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`: the cocone of the inclusions `E_X ⟶ ℚ̄_ℓ,X` is a colimit cocone. See the
module docstring for the argument. -/
lemma padicAlgClSheaf_isColimit : Nonempty (IsColimit (padicAlgClSheafCocone X ℓ)) :=
  sorry

end Colimit

/-! ### The compatibility of the coefficient morphisms `η_f` with the inclusions -/

section Pushforward

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical coefficient morphism `η_f : E_Y ⟶ f_* E_X` of the ring object `E_X = C(-, E)`
of a finite subextension `E`: the pullback of continuous functions along the projections
`V ×_Y X → V`. -/
noncomputable def padicSubfieldPushforwardHom (E : FiniteSubext ℓ) :
    padicSubfieldRingObj Y ℓ E ⟶ (f)_*[Ab.{u + 1}].obj (padicSubfieldRingObj X ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapPushforwardHom E f

instance (E : FiniteSubext ℓ) : IsMonHom (padicSubfieldPushforwardHom ℓ f E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  inferInstanceAs (IsMonHom (continuousMapPushforwardHom E f))

/-- **(A0.3)** The coefficient morphisms `η_f` are compatible with the inclusions `E_X ⟶ F_X`:
on sections over `V`, both composites send a function `h : V → E` to the function
`V ×_Y X → F` obtained by pulling back along the projection and including the values. -/
lemma padicSubfieldPushforwardHom_comp_map {E F : FiniteSubext ℓ} (h : E ≤ F) :
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
lemma padicSubfieldPushforwardHom_comp_map_toPadicAlgClSheaf (E : FiniteSubext ℓ) :
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
