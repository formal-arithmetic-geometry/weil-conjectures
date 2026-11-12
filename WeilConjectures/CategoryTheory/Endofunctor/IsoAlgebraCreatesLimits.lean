/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The forgetful functor of algebras with invertible structure morphism creates limits

Let `F : C ⥤ C` be an endofunctor. The forgetful functor `IsoAlgebra F ⥤ C` creates the limits
and the colimits which `F` preserves: a limit cone of the underlying objects of a diagram of
algebras carries a unique algebra structure making it a limit cone of algebras
(`CategoryTheory.Endofunctor.Algebra.forgetCreatesLimits`), and its structure morphism is
invertible when `F` preserves the limit (`CategoryTheory.Endofunctor.Algebra.isIsoStr_of_isLimit`).
No limits are assumed to exist in `C`. In particular, for an autoequivalence `F` the forgetful
functor creates all limits and colimits, so it preserves and reflects exactness.

## Main declarations

- `CategoryTheory.Endofunctor.IsoAlgebra.forgetCreatesLimit`,
  `CategoryTheory.Endofunctor.IsoAlgebra.forgetCreatesColimit`.
-/

@[expose] public section

universe w w' v u

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {F : C ⥤ C} {J : Type w} [Category.{w'} J]

instance : (ι F).Full :=
  inferInstanceAs (Algebra.IsIsoStr F).ι.Full

instance : (ι F).Faithful :=
  inferInstanceAs (Algebra.IsIsoStr F).ι.Faithful

instance : (forget F).Faithful :=
  inferInstanceAs (ι F ⋙ Algebra.forget F).Faithful

instance : (forget F).ReflectsIsomorphisms :=
  inferInstanceAs (ι F ⋙ Algebra.forget F).ReflectsIsomorphisms

/-- The forgetful functor of algebras with invertible structure morphism creates the limit of a
diagram `D` when `F` preserves the limit of the underlying diagram. -/
noncomputable instance forgetCreatesLimit (D : J ⥤ IsoAlgebra F)
    [PreservesLimit (D ⋙ forget F) F] : CreatesLimit D (forget F) :=
  createsLimitOfReflectsIso fun c t ↦
    have : PreservesLimit ((D ⋙ ι F) ⋙ Algebra.forget F) F :=
      inferInstanceAs (PreservesLimit (D ⋙ forget F) F)
    have : HasLimit ((D ⋙ ι F) ⋙ Algebra.forget F) := ⟨⟨⟨c, t⟩⟩⟩
    have : PreservesLimit (D ⋙ ι F) (Algebra.forget F) :=
      preservesLimit_of_createsLimit_and_hasLimit _ _
    let L := Algebra.ForgetCreatesLimits.liftedCone (D ⋙ ι F) c t
    have hL : IsLimit L := Algebra.ForgetCreatesLimits.liftedConeIsLimit (D ⋙ ι F) c t
    have hI : Algebra.IsIsoStr F L.pt :=
      Algebra.isIsoStr_of_isLimit hL fun j ↦ (D.obj j).property
    { liftedCone :=
        { pt := ⟨L.pt, hI⟩
          π :=
            { app j := ObjectProperty.homMk (L.π.app j)
              naturality _ _ g := ObjectProperty.hom_ext _ (L.π.naturality g) } }
      validLift := Cone.ext (Iso.refl _) fun _ ↦ (Category.id_comp _).symm
      makesLimit := isLimitOfReflects (ι F) hL }

/-- The forgetful functor of algebras with invertible structure morphism creates the colimit of
a diagram `D` when `F` preserves the colimit of the underlying diagram. -/
noncomputable instance forgetCreatesColimit (D : J ⥤ IsoAlgebra F)
    [PreservesColimit (D ⋙ forget F) F] : CreatesColimit D (forget F) :=
  createsColimitOfReflectsIso fun c t ↦
    have : PreservesColimit ((D ⋙ ι F) ⋙ Algebra.forget F) F :=
      inferInstanceAs (PreservesColimit (D ⋙ forget F) F)
    have : HasColimit ((D ⋙ ι F) ⋙ Algebra.forget F) := ⟨⟨⟨c, t⟩⟩⟩
    have : PreservesColimit (D ⋙ ι F) (Algebra.forget F) :=
      preservesColimit_of_createsColimit_and_hasColimit _ _
    let L := Algebra.ForgetCreatesColimits.liftedCocone (D := D ⋙ ι F) c t
    have hL : IsColimit L := Algebra.ForgetCreatesColimits.liftedCoconeIsColimit (D := D ⋙ ι F) c t
    have hI : Algebra.IsIsoStr F L.pt :=
      Algebra.isIsoStr_of_isColimit hL fun j ↦ (D.obj j).property
    { liftedCocone :=
        { pt := ⟨L.pt, hI⟩
          ι :=
            { app j := ObjectProperty.homMk (L.ι.app j)
              naturality _ _ g := ObjectProperty.hom_ext _ (L.ι.naturality g) } }
      validLift := Cocone.ext (Iso.refl _) fun _ ↦ Category.comp_id _
      makesColimit := isColimitOfReflects (ι F) hL }

/-- The forgetful functor of algebras with invertible structure morphism creates the limits of
the shapes whose limits `F` preserves. -/
noncomputable instance forgetCreatesLimitsOfShape [PreservesLimitsOfShape J F] :
    CreatesLimitsOfShape J (forget F) where

/-- The forgetful functor of algebras with invertible structure morphism creates the colimits of
the shapes whose colimits `F` preserves. -/
noncomputable instance forgetCreatesColimitsOfShape [PreservesColimitsOfShape J F] :
    CreatesColimitsOfShape J (forget F) where

/-! ### Algebras with carrier in a full subcategory

Let `P` be a property of objects of `C` which `F` preserves. The algebras with invertible structure
morphism whose carrier satisfies `P` are the algebras over the restriction `F|_P` of `F` to the
full subcategory of `P`; if `F|_P` is an autoequivalence, their forgetful functor to `P` creates
all limits and colimits. -/

section FullSubcategory

variable (F) (P : ObjectProperty C) (hF : ∀ X, P X → P (F.obj X))

/-- The algebras with invertible structure morphism whose carrier satisfies `P`. -/
abbrev carrierProperty : ObjectProperty (IsoAlgebra F) :=
  fun K ↦ P K.carrier

/-- The forgetful functor from the algebras with carrier satisfying `P` to the full subcategory
of `P`. -/
abbrev forgetFullSubcategory : (carrierProperty F P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((carrierProperty F P).ι ⋙ forget F) fun K ↦ K.property

/-- The restriction `F|_P` of `F` to the full subcategory of `P`. -/
abbrev restrict : P.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P.ι ⋙ F) fun X ↦ hF _ X.property

/-- An algebra over the restriction `F|_P` is an algebra over `F` with carrier satisfying `P`. -/
noncomputable def ofRestrict :
    IsoAlgebra (restrict F P hF) ⥤ (carrierProperty F P).FullSubcategory :=
  (carrierProperty F P).lift (mapOfNatIso (L := P.ι) (Iso.refl _)) fun K ↦ K.carrier.property

/-- The underlying object of an algebra over `F|_P`. -/
noncomputable def ofRestrictCompForgetFullSubcategoryIso :
    ofRestrict F P hF ⋙ forgetFullSubcategory F P ≅ forget (restrict F P hF) :=
  Iso.refl _

instance : (ofRestrict F P hF).Faithful :=
  have : (ofRestrict F P hF ⋙ forgetFullSubcategory F P).Faithful :=
    inferInstanceAs (forget (restrict F P hF)).Faithful
  Functor.Faithful.of_comp _ (forgetFullSubcategory F P)

instance : (ofRestrict F P hF).Full where
  map_surjective {K K'} f :=
    ⟨ObjectProperty.homMk
      { f := ObjectProperty.homMk f.hom.hom.f
        h := ObjectProperty.hom_ext _ (by
          have h := f.hom.hom.h
          dsimp [ofRestrict, mapOfNatIso] at h ⊢
          simpa using h) }, rfl⟩

instance : (ofRestrict F P hF).EssSurj where
  mem_essImage K :=
    ⟨mk ⟨K.obj.carrier, K.property⟩ (P.isoMk K.obj.str),
      ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _
        (Algebra.isoMk (Iso.refl _) (by
          dsimp [ofRestrict, mapOfNatIso]
          simp)))⟩⟩

instance : (ofRestrict F P hF).IsEquivalence where

/-- If the restriction `F|_P` is an autoequivalence, the forgetful functor from the algebras with
carrier satisfying `P` to the full subcategory of `P` creates limits and colimits: it is the
forgetful functor of the algebras over `F|_P`, which creates the limits and colimits that `F|_P`
preserves. -/
theorem nonempty_createsFiniteLimits_forgetFullSubcategory
    [(restrict F P hF).IsEquivalence] :
    Nonempty (CreatesFiniteLimits (forgetFullSubcategory F P)) ∧
      Nonempty (CreatesFiniteColimits (forgetFullSubcategory F P)) := by
  let e : forgetFullSubcategory F P ≅ (ofRestrict F P hF).inv ⋙ forget (restrict F P hF) :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (ofRestrict F P hF).asEquivalence.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ofRestrictCompForgetFullSubcategoryIso F P hF)
  exact ⟨⟨⟨fun J _ _ ↦ createsLimitsOfShapeOfNatIso e.symm⟩⟩,
    ⟨⟨fun J _ _ ↦ createsColimitsOfShapeOfNatIso e.symm⟩⟩⟩

end FullSubcategory

end CategoryTheory.Endofunctor.IsoAlgebra
