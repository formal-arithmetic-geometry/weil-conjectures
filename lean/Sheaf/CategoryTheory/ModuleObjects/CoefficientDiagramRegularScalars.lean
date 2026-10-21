/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import Mathlib.CategoryTheory.Monoidal.Free.Coherence

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
  sorry

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
  sorry

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
  sorry

end CategoryTheory
