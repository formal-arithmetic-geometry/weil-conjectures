/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Regular scalars in a monoidal coefficient diagram

Source: blueprint main-20261015, sk-def-sfb-pullback-from-point-comp, last paragraph;
det-proper-base-change-unbounded-pullback, Constructible complexes paragraph.
(blueprint: lem-sfb-coefficient-diagram-regular-scalars)

The coefficient component preserves the sequentially transported ring structures.
The regular-module comparison is normalized on the actual balancing coequalizer.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]

/-- Left multiplication by a global scalar is the existing regular-module endomorphism.
Source: blueprint main-20261015, sk-def-sfb-pullback-from-point-comp, scalar calculation.
(blueprint: lem-sfb-coefficient-diagram-regular-scalars)

Proof: braiding naturality gives β (1 ⊗ b) = (b ⊗ 1) β. Compose with
multiplication, use commutativity and braiding_leftUnitor, and invert the
unitors to identify left multiplication with regularLift's right multiplication.
The latter is already a morphism of regular modules; its linearity is
associativity with the structural unit identifications of
lem-coef-monoidal-structural-coherence. -/
theorem regularScalar_eq_leftMultiplication
    (Z : C) [MonObj Z] [IsCommMonObj Z] (b : 𝟙_ C ⟶ Z) :
    (Mod.regularLift (Mod.regular Z) b).hom = (λ_ Z).inv ≫ b ▷ Z ≫ μ[Z] := by
  change (ρ_ Z).inv ≫ Z ◁ b ≫ μ[Z] = _
  calc
    _ = (ρ_ Z).inv ≫ Z ◁ b ≫ (β_ Z Z).hom ≫ μ[Z] := by
      rw [IsCommMonObj.mul_comm]
    _ = (λ_ Z).inv ≫ b ▷ Z ≫ μ[Z] := by
      rw [BraidedCategory.braiding_naturality_right_assoc,
        rightUnitor_inv_braiding_assoc]

-- Keep the existing braided parameters in this public theorem.
set_option linter.unusedSectionVars false in
/-- The coefficient comparison is a ring morphism for sequential transport.
Source: blueprint main-20261015, sk-def-sfb-pullback-from-point-comp, last paragraph.
(blueprint: lem-sfb-coefficient-diagram-regular-scalars)

Proof: apply det-def-sfb-ring-object-transport, clause 3, to the monoidal natural
isomorphism, and identify composite transport with sequential transport using
Functor.mapMonCompIso. The unit equation is monoidal unit compatibility; the
multiplication equation is monoidal tensor compatibility followed by naturality
at the multiplication of the original ring object. -/
@[instance]
theorem coefficientDiagram_isMonHom
    (P : C ⥤ D) (Q : C ⥤ E) (F : D ⥤ E)
    [P.Monoidal] [Q.Monoidal] [F.Monoidal]
    (c : P ⋙ F ≅ Q) [NatTrans.IsMonoidal c.hom]
    (Λ : C) [MonObj Λ] :
    @IsMonHom E _ _ (F.obj (P.obj Λ)) (Q.obj Λ)
      (F.monObjObj (P.obj Λ)) (Q.monObjObj Λ) (c.hom.app Λ) := by
  let f : F.mapMon.obj (P.mapMon.obj (Mon.mk Λ)) ⟶ Q.mapMon.obj (Mon.mk Λ) :=
    (Functor.mapMonCompIso (F := P) (G := F)).inv.app (Mon.mk Λ) ≫
      (Functor.mapMonNatTrans c.hom).app (Mon.mk Λ)
  have hf : f.hom = c.hom.app Λ := by
    change 𝟙 _ ≫ c.hom.app Λ = _
    exact Category.id_comp _
  rw [← hf]
  exact f.isMonHom_hom

/-- The recorded scalar-extension functor, supplying its small-colimit instances
from preservation of all colimits. No coefficient structure is changed.
Source: blueprint main-20261015, def-sfb-modobj-extension.
(blueprint: lem-sfb-coefficient-diagram-regular-scalars) -/
noncomputable abbrev coefficientDiagramExtension
    [HasCoequalizers E]
    [∀ X : E, PreservesColimits (tensorLeft X)]
    [∀ X : E, PreservesColimits (tensorRight X)]
    {T S : E} [MonObj T] [MonObj S] [IsCommMonObj T]
    (φ : T ⟶ S) [IsMonHom φ] : Mod E T ⥤ Mod E S :=
  @Mod.extendScalars E _ _ _
    (fun X => preservesSmallestColimits_of_preservesColimits (tensorLeft X))
    (fun X => preservesSmallestColimits_of_preservesColimits (tensorRight X))
    _ T S _ _ _ φ _

/-- The actual balancing projection of the recorded scalar-extension functor,
with its sequentially transported coefficient structure supplied explicitly.
Source: blueprint main-20261015, def-sfb-modobj-extension, balancing coequalizer.
(blueprint: lem-sfb-coefficient-diagram-regular-scalars) -/
noncomputable abbrev coefficientDiagramProjection
    [HasCoequalizers E]
    [∀ X : E, PreservesColimits (tensorLeft X)]
    [∀ X : E, PreservesColimits (tensorRight X)]
    {T S : E} [MonObj T] [MonObj S] [IsCommMonObj T]
    (φ : T ⟶ S) [IsMonHom φ] (M : Mod E T) :
    S ⊗ M.X ⟶ ((coefficientDiagramExtension φ).obj M).X :=
  @Mod.extendπ E _ _ _
    (fun X => preservesSmallestColimits_of_preservesColimits (tensorLeft X))
    (fun X => preservesSmallestColimits_of_preservesColimits (tensorRight X))
    _ T S _ _ _ φ _ M

omit [BraidedCategory C] [BraidedCategory D] in
private theorem map_leftScalar (G : C ⥤ D) [G.Monoidal]
    (Z : C) [MonObj Z] (b : 𝟙_ C ⟶ Z) :
    G.map ((λ_ Z).inv ≫ b ▷ Z ≫ μ[Z]) =
      (λ_ (G.obj Z)).inv ≫ (Functor.LaxMonoidal.ε G ≫ G.map b) ▷ G.obj Z ≫
        μ[G.obj Z] := by
  simp only [Functor.map_comp, Functor.obj.μ_def, comp_whiskerRight, Category.assoc]
  rw [Functor.Monoidal.map_leftUnitor_inv]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]

/-- Scalar transport and the normalized comparison of regular modules.
Source: blueprint main-20261015, sk-def-sfb-pullback-from-point-comp, last paragraph;
det-proper-base-change-unbounded-pullback, Constructible complexes paragraph.
(blueprint: lem-sfb-coefficient-diagram-regular-scalars)

Proof:
1. Braiding naturality and braiding_leftUnitor identify left scalar multiplication
   with regularLift, which is right scalar multiplication. Commutativity and
   associativity, with lem-coef-monoidal-structural-coherence, give linearity.
2. Strong monoidal unit coherence and tensorator naturality give the two scalar
   transport identities, using det-def-sfb-ring-object-transport's multiplication.
3. The coefficient component is a ring isomorphism by the preceding clause.
   Naturality at scalar multiplication gives the displayed scalar square.
4. def-sfb-modobj-transport gives action F(μ_R) after the tensorator, literally
   the multiplication of T. The identity therefore identifies regular modules.
5. Apply lem-sfb-mixed-bimodule-right-unitor to the S-T-bimodule of
   def-sfb-modobj-extension. Its right action is S ◁ c_Λ followed by μ_S.
   This gives e, its balancing-projection formula, and the stated inverse.
6. Precompose the scalar-intertwining equation with extendπ. The induced-map
   clause of def-sfb-modobj-extension, step 3, and S-linearity of the scalar map
   give equal composites. Cancel the coequalizer projection using uniqueness
   in def-weil-pbc-category-colimit. All calculations are ambient morphism
   identities and make no assertion about pure-tensor sections. -/
theorem coefficientDiagram_regularScalars
    [HasCoequalizers E]
    [∀ X : E, PreservesColimits (tensorLeft X)]
    [∀ X : E, PreservesColimits (tensorRight X)]
    (P : C ⥤ D) (Q : C ⥤ E) (F : D ⥤ E)
    [P.Monoidal] [Q.Monoidal] [F.Monoidal]
    (c : P ⋙ F ≅ Q) [NatTrans.IsMonoidal c.hom]
    (Λ : C) [MonObj Λ] [IsCommMonObj Λ]
    [IsCommMonObj (P.obj Λ)] [IsCommMonObj (F.obj (P.obj Λ))]
    [IsCommMonObj (Q.obj Λ)] :
    (∃ i : (F.mapMod (P.obj Λ)).obj (Mod.regular (P.obj Λ)) ≅
        Mod.regular (F.obj (P.obj Λ)),
      i.hom.hom = 𝟙 (F.obj (P.obj Λ)) ∧ i.inv.hom = 𝟙 (F.obj (P.obj Λ))) ∧
    ∃ e : ((F.mapMod (P.obj Λ)) ⋙ coefficientDiagramExtension (c.hom.app Λ)).obj
        (Mod.regular (P.obj Λ)) ≅ Mod.regular (Q.obj Λ),
      @coefficientDiagramProjection E _ _ _ _ _ _ (F.obj (P.obj Λ)) (Q.obj Λ)
        (F.monObjObj (P.obj Λ)) (Q.monObjObj Λ) _ (c.hom.app Λ)
        (coefficientDiagram_isMonHom P Q F c Λ)
        ((F.mapMod (P.obj Λ)).obj (Mod.regular (P.obj Λ))) ≫
          e.hom.hom = Q.obj Λ ◁ c.hom.app Λ ≫ μ[Q.obj Λ] ∧
      e.inv.hom = (ρ_ (Q.obj Λ)).inv ≫ Q.obj Λ ◁ η[F.obj (P.obj Λ)] ≫
        @coefficientDiagramProjection E _ _ _ _ _ _ (F.obj (P.obj Λ)) (Q.obj Λ)
        (F.monObjObj (P.obj Λ)) (Q.monObjObj Λ) _ (c.hom.app Λ)
        (coefficientDiagram_isMonHom P Q F c Λ)
        ((F.mapMod (P.obj Λ)).obj (Mod.regular (P.obj Λ))) ∧
      ∀ a : 𝟙_ C ⟶ Λ,
        P.map ((λ_ Λ).inv ≫ a ▷ Λ ≫ μ[Λ]) =
          (λ_ (P.obj Λ)).inv ≫ (Functor.LaxMonoidal.ε P ≫ P.map a) ▷ P.obj Λ ≫
            μ[P.obj Λ] ∧
        Q.map ((λ_ Λ).inv ≫ a ▷ Λ ≫ μ[Λ]) =
          (λ_ (Q.obj Λ)).inv ≫ (Functor.LaxMonoidal.ε Q ≫ Q.map a) ▷ Q.obj Λ ≫
            μ[Q.obj Λ] ∧
        F.map ((λ_ (P.obj Λ)).inv ≫
            (Functor.LaxMonoidal.ε P ≫ P.map a) ▷ P.obj Λ ≫ μ[P.obj Λ]) ≫
            c.hom.app Λ =
          c.hom.app Λ ≫ (λ_ (Q.obj Λ)).inv ≫
            (Functor.LaxMonoidal.ε Q ≫ Q.map a) ▷ Q.obj Λ ≫ μ[Q.obj Λ] ∧
        ((F.mapMod (P.obj Λ)) ⋙ coefficientDiagramExtension (c.hom.app Λ)).map
            (Mod.regularLift (Mod.regular (P.obj Λ))
              (Functor.LaxMonoidal.ε P ≫ P.map a)) ≫ e.hom =
          e.hom ≫ Mod.regularLift (Mod.regular (Q.obj Λ))
            (Functor.LaxMonoidal.ε Q ≫ Q.map a) := by
  let : MonObj (F.obj (P.obj Λ)) := F.monObjObj (P.obj Λ)
  let (X : E) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    preservesSmallestColimits_of_preservesColimits (tensorLeft X)
  let (X : E) : PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    preservesSmallestColimits_of_preservesColimits (tensorRight X)
  let M := (F.mapMod (P.obj Λ)).obj (Mod.regular (P.obj Λ))
  let B : Bimod (Mon.mk (Q.obj Λ)) (Mon.mk (F.obj (P.obj Λ))) :=
    Bimod.ofMonHom (c.hom.app Λ)
  let i : M ≅ Mod.regular (F.obj (P.obj Λ)) :=
    Mod.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id, whiskerLeft_id, Category.id_comp])
  let H : Mod E (F.obj (P.obj Λ)) ⥤ Mod E (Q.obj Λ) :=
    @coefficientDiagramExtension E _ _ _ _ _ _ (F.obj (P.obj Λ)) (Q.obj Λ)
      (F.monObjObj (P.obj Λ)) (Q.monObjObj Λ) _ (c.hom.app Λ)
      (coefficientDiagram_isMonHom P Q F c Λ)
  let eX : (H.obj M).X ≅ Q.obj Λ :=
    { hom := Bimod.RightUnitorBimod.hom B
      inv := Bimod.RightUnitorBimod.inv B
      hom_inv_id := Bimod.RightUnitorBimod.hom_inv_id B
      inv_hom_id := Bimod.RightUnitorBimod.inv_hom_id B }
  let e : H.obj M ≅ Mod.regular (Q.obj Λ) :=
    Mod.isoMk eX (Bimod.RightUnitorBimod.hom_left_act_hom' B)
  have he :
      @Mod.extendπ E _ _ _ _ _ _ (F.obj (P.obj Λ)) (Q.obj Λ)
        (F.monObjObj (P.obj Λ)) (Q.monObjObj Λ) _ (c.hom.app Λ)
        (coefficientDiagram_isMonHom P Q F c Λ) M ≫ e.hom.hom =
      Q.obj Λ ◁ c.hom.app Λ ≫ μ[Q.obj Λ] := coequalizer.π_desc _ _
  refine ⟨⟨i, rfl, rfl⟩, e, he, rfl, ?_⟩
  intro a
  have hP := map_leftScalar P Λ a
  have hQ := map_leftScalar Q Λ a
  have hscalar :
      F.map ((λ_ (P.obj Λ)).inv ≫
        (Functor.LaxMonoidal.ε P ≫ P.map a) ▷ P.obj Λ ≫ μ[P.obj Λ]) ≫
        c.hom.app Λ = c.hom.app Λ ≫ (λ_ (Q.obj Λ)).inv ≫
        (Functor.LaxMonoidal.ε Q ≫ Q.map a) ▷ Q.obj Λ ≫ μ[Q.obj Λ] := by
    rw [← hP, ← Category.assoc, ← hQ]
    simpa only [Functor.comp_map, Category.assoc] using
      c.hom.naturality ((λ_ Λ).inv ≫ a ▷ Λ ≫ μ[Λ])
  refine ⟨hP, hQ, hscalar, ?_⟩
  apply @Mod.extendScalarsObj_hom_ext E _ _ _ _ _ _
    (F.obj (P.obj Λ)) (Q.obj Λ) (F.monObjObj (P.obj Λ)) (Q.monObjObj Λ)
    _ (c.hom.app Λ) (coefficientDiagram_isMonHom P Q F c Λ)
  simp only [Mod.comp_hom', Functor.comp_map, coefficientDiagramExtension,
    Mod.extendScalars_map, Mod.extendπ_extendScalarsMap_assoc]
  dsimp only [M] at he
  erw [he, reassoc_of% he]
  simp only [← regularScalar_eq_leftMultiplication] at hscalar
  change Q.obj Λ ◁ F.map
      (Mod.regularLift (Mod.regular (P.obj Λ))
        (Functor.LaxMonoidal.ε P ≫ P.map a)).hom ≫
      Q.obj Λ ◁ c.hom.app Λ ≫ μ[Q.obj Λ] = _
  rw [← whiskerLeft_comp_assoc, hscalar, whiskerLeft_comp_assoc]
  exact congrArg (fun f ↦ Q.obj Λ ◁ c.hom.app Λ ≫ f)
    (Mod.act_hom (Mod.regularLift (Mod.regular (Q.obj Λ))
      (Functor.LaxMonoidal.ε Q ≫ Q.map a))).symm

end CategoryTheory
