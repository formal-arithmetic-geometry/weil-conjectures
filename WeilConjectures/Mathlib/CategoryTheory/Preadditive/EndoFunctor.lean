/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Limits and the abelian structure on algebras of an endofunctor

Let `F : C ⥤ C` be an endofunctor. The forgetful functor `Endofunctor.Algebra.forget F`
creates all limits: the structure morphism of a limit `lim D` of algebras is the morphism
`F (lim D) ⟶ lim D` whose components are `F (lim D) ⟶ F (D j) ⟶ D j`. It creates colimits of
the shapes whose colimits are preserved by `F`.

If `C` is abelian and `F` is additive and preserves finite colimits, then `Algebra F` is
abelian. If moreover `F` preserves finite limits, the algebras with invertible structure
morphism form a full subcategory closed under kernels, cokernels and finite products, so
`IsoAlgebra F` is abelian as well, and its forgetful functor to `C` is exact.

## Main definitions and results

- `CategoryTheory.Endofunctor.Algebra.forgetCreatesLimits`: `Algebra.forget F` creates limits.
- `CategoryTheory.Endofunctor.Algebra.forgetCreatesColimitsOfShape`: `Algebra.forget F`
  creates colimits of the shapes whose colimits `F` preserves.
- `CategoryTheory.Endofunctor.Algebra.abelian`: `Algebra F` is abelian.
- `CategoryTheory.Endofunctor.IsoAlgebra.abelian`: `IsoAlgebra F` is abelian.
- `CategoryTheory.Endofunctor.IsoAlgebra.forgetKernelIso`,
  `CategoryTheory.Endofunctor.IsoAlgebra.forgetCokernelIso`: the underlying object of the
  kernel (resp. cokernel) of a morphism of iso-algebras is the kernel (resp. cokernel) of the
  underlying morphism.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.Endofunctor

open Limits

universe w w' v u

variable {C : Type u} [Category.{v} C]

namespace Algebra

variable {F : C ⥤ C}

section Limits

variable {J : Type w'} [Category.{w} J] (D : J ⥤ Algebra F)

lemma limitConePoint_naturality_aux {X : C} {A B : Algebra F} (f : X ⟶ A.a) (g : A ⟶ B)
    (f' : X ⟶ B.a) (h : f ≫ g.f = f') :
    𝟙 _ ≫ F.map f' ≫ B.str = (F.map f ≫ A.str) ≫ g.f := by
  rw [← h, F.map_comp, Category.id_comp, Category.assoc, Category.assoc, g.h]

lemma colimitCoconePoint_naturality_aux {X : C} {A B : Algebra F} (f : A.a ⟶ X) (g : A ⟶ B)
    (f' : B.a ⟶ X) (h : g.f ≫ f' = f) :
    F.map g.f ≫ B.str ≫ f' = (A.str ≫ f) ≫ 𝟙 _ := by
  rw [← h, Category.comp_id, g.h_assoc]

lemma liftedLimitCone_lift_aux {X Y : C} {A : Algebra F} (L : X ⟶ Y) (p : Y ⟶ A.a)
    (sX : F.obj X ⟶ X) (sY : F.obj Y ⟶ Y) (q : X ⟶ A.a) (hq : L ≫ p = q)
    (hY : sY ≫ p = F.map p ≫ A.str) (hX : F.map q ≫ A.str = sX ≫ q) :
    (F.map L ≫ sY) ≫ p = (sX ≫ L) ≫ p := by
  rw [Category.assoc, hY, ← F.map_comp_assoc, hq, hX, Category.assoc, hq]

lemma liftedColimitCocone_desc_aux {X Y : C} {A : Algebra F} (i : A.a ⟶ X) (d : X ⟶ Y)
    (sX : F.obj X ⟶ X) (sY : F.obj Y ⟶ Y) (q : A.a ⟶ Y) (hq : i ≫ d = q)
    (hX : F.map i ≫ sX = A.str ≫ i) (hY : F.map q ≫ sY = A.str ≫ q) :
    F.map i ≫ F.map d ≫ sY = F.map i ≫ sX ≫ d := by
  rw [← F.map_comp_assoc, hq, hY, reassoc_of% hX, hq]

/-- For a cone `c` over the underlying objects of a diagram `D` of algebras, the cone with point
`F c.pt` and components `F c.pt ⟶ F (D j) ⟶ D j`. Its lift is the structure morphism of the
limit of `D`. -/
@[simps]
def limitStrCone (c : Cone (D ⋙ forget F)) : Cone (D ⋙ forget F) where
  pt := F.obj c.pt
  π :=
    { app j := F.map (c.π.app j) ≫ (D.obj j).str
      naturality _ _ g := limitConePoint_naturality_aux _ _ _ (c.w g) }

/-- The algebra structure on the point of a limit cone of the underlying objects of a diagram
of algebras. -/
@[simps]
def limitConePoint {c : Cone (D ⋙ forget F)} (t : IsLimit c) : Algebra F where
  a := c.pt
  str := t.lift (limitStrCone D c)

/-- The lift of a limit cone of the underlying objects of a diagram of algebras to a cone of
algebras. -/
@[simps]
def liftedLimitCone {c : Cone (D ⋙ forget F)} (t : IsLimit c) : Cone D where
  pt := limitConePoint D t
  π :=
    { app j :=
        { f := c.π.app j
          h := (t.fac (limitStrCone D c) j).symm }
      naturality _ _ g := Hom.ext ((Category.id_comp _).trans (c.w g).symm) }

set_option backward.isDefEq.respectTransparency false in
/-- The lifted cone `liftedLimitCone D t` is a limit cone. -/
def liftedLimitConeIsLimit {c : Cone (D ⋙ forget F)} (t : IsLimit c) :
    IsLimit (liftedLimitCone D t) where
  lift s :=
    { f := t.lift ((forget F).mapCone s)
      h := t.hom_ext fun j ↦ liftedLimitCone_lift_aux _ _ _ _ _ (t.fac _ j)
        (t.fac (limitStrCone D c) j) (s.π.app j).h }
  fac _ j := Hom.ext (t.fac _ j)
  uniq s m hm := Hom.ext <| t.uniq ((forget F).mapCone s) m.f fun j ↦ congr_arg Hom.f (hm j)

/-- The forgetful functor from algebras of an endofunctor creates all limits. -/
instance forgetCreatesLimits : CreatesLimitsOfSize.{w, w'} (forget F) where
  CreatesLimitsOfShape :=
    { CreatesLimit {D} := createsLimitOfReflectsIso fun _ t ↦
        { liftedCone := liftedLimitCone D t
          validLift := Cone.ext (Iso.refl _) fun _ ↦ (Category.id_comp _).symm
          makesLimit := liftedLimitConeIsLimit D t } }

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Algebra F) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget F)

instance [HasFiniteLimits C] : PreservesFiniteLimits (forget F) where
  preservesFiniteLimits _ := inferInstance

variable [PreservesColimitsOfShape J F]

/-- For a cocone `c` over the underlying objects of a diagram `D` of algebras, the cocone over
`(D ⋙ forget F) ⋙ F` with point `c.pt` and components `F (D j) ⟶ D j ⟶ c.pt`. Its descent
along `F c` is the structure morphism of the colimit of `D`. -/
@[simps]
def colimitStrCocone (c : Cocone (D ⋙ forget F)) : Cocone ((D ⋙ forget F) ⋙ F) where
  pt := c.pt
  ι :=
    { app j := (D.obj j).str ≫ c.ι.app j
      naturality _ _ g := colimitCoconePoint_naturality_aux _ _ _ (c.w g) }

/-- The algebra structure on the point of a colimit cocone of the underlying objects of a
diagram of algebras, when `F` preserves the colimit. -/
@[simps]
def colimitCoconePoint {c : Cocone (D ⋙ forget F)} (t : IsColimit c) : Algebra F where
  a := c.pt
  str := (isColimitOfPreserves F t).desc (colimitStrCocone D c)

/-- The lift of a colimit cocone of the underlying objects of a diagram of algebras to a
cocone of algebras. -/
@[simps]
def liftedColimitCocone {c : Cocone (D ⋙ forget F)} (t : IsColimit c) : Cocone D where
  pt := colimitCoconePoint D t
  ι :=
    { app j :=
        { f := c.ι.app j
          h := (isColimitOfPreserves F t).fac (colimitStrCocone D c) j }
      naturality _ _ g := Hom.ext ((c.w g).trans (Category.comp_id _).symm) }

set_option backward.isDefEq.respectTransparency false in
/-- The lifted cocone `liftedColimitCocone D t` is a colimit cocone. -/
def liftedColimitCoconeIsColimit {c : Cocone (D ⋙ forget F)} (t : IsColimit c) :
    IsColimit (liftedColimitCocone D t) where
  desc s :=
    { f := t.desc ((forget F).mapCocone s)
      h := (isColimitOfPreserves F t).hom_ext fun j ↦ liftedColimitCocone_desc_aux _ _ _ _ _
        (t.fac _ j) ((isColimitOfPreserves F t).fac (colimitStrCocone D c) j) (s.ι.app j).h }
  fac _ j := Hom.ext (t.fac _ j)
  uniq s m hm := Hom.ext <| t.uniq ((forget F).mapCocone s) m.f fun j ↦ congr_arg Hom.f (hm j)

/-- The forgetful functor from algebras of an endofunctor creates the colimits of the shapes
whose colimits the endofunctor preserves. -/
instance forgetCreatesColimitsOfShape : CreatesColimitsOfShape J (forget F) where
  CreatesColimit {D} := createsColimitOfReflectsIso fun _ t ↦
    { liftedCocone := liftedColimitCocone D t
      validLift := Cocone.ext (Iso.refl _) fun _ ↦ Category.comp_id _
      makesColimit := liftedColimitCoconeIsColimit D t }

instance [HasColimitsOfShape J C] : HasColimitsOfShape J (Algebra F) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget F)

end Limits

instance [HasFiniteColimits C] [PreservesFiniteColimits F] :
    PreservesFiniteColimits (forget F) where
  preservesFiniteColimits _ := inferInstance

section Abelian

variable (F) [Abelian C] [F.Additive] [PreservesFiniteColimits F]

instance : HasKernels (Algebra F) where

instance : HasCokernels (Algebra F) where

instance : HasFiniteProducts (Algebra F) where
  out _ := inferInstance

instance {X Y : Algebra F} (φ : X ⟶ Y) : IsIso (Abelian.coimageImageComparison φ) := by
  have := Abelian.PreservesCoimageImageComparison.iso (forget F) φ
  rw [← isIso_iff_of_reflects_iso _ (forget F), Arrow.isIso_iff_isIso_of_isIso this.hom]
  exact inferInstanceAs (IsIso (Abelian.coimageImageComparison φ.f))

/-- The category of algebras of an additive endofunctor of an abelian category preserving
finite colimits is abelian. -/
instance abelian : Abelian (Algebra F) :=
  Abelian.ofCoimageImageComparisonIsIso

end Abelian

section IsIsoStr

/-- The structure morphism of the point of a limit of algebras with invertible structure
morphisms is invertible, if `F` preserves the limit. -/
lemma isIsoStr_of_isLimit {J : Type w'} [Category.{w} J] {D : J ⥤ Algebra F} {c : Cone D}
    (hc : IsLimit c) [PreservesLimit (D ⋙ forget F) F] [PreservesLimit D (forget F)]
    (hD : ∀ j, IsIsoStr F (D.obj j)) : IsIsoStr F c.pt := by
  let t : IsLimit ((forget F).mapCone c) := isLimitOfPreserves (forget F) hc
  let α : (D ⋙ forget F) ⋙ F ⟶ D ⋙ forget F :=
    { app j := (D.obj j).str
      naturality _ _ g := (D.map g).h }
  have : ∀ j, IsIso (α.app j) := hD
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have h : c.pt.str = (IsLimit.conePointsIsoOfNatIso (isLimitOfPreserves F t) t (asIso α)).hom :=
    t.hom_ext fun j ↦
      (c.π.app j).h.symm.trans
        (IsLimit.conePointsIsoOfNatIso_hom_comp (isLimitOfPreserves F t) t (asIso α) j).symm
  change IsIso c.pt.str
  rw [h]
  exact Iso.isIso_hom _

/-- The structure morphism of the point of a colimit of algebras with invertible structure
morphisms is invertible, if `F` preserves the colimit. -/
lemma isIsoStr_of_isColimit {J : Type w'} [Category.{w} J] {D : J ⥤ Algebra F}
    {c : Cocone D} (hc : IsColimit c) [PreservesColimit (D ⋙ forget F) F]
    [PreservesColimit D (forget F)] (hD : ∀ j, IsIsoStr F (D.obj j)) : IsIsoStr F c.pt := by
  let t : IsColimit ((forget F).mapCocone c) := isColimitOfPreserves (forget F) hc
  let α : (D ⋙ forget F) ⋙ F ⟶ D ⋙ forget F :=
    { app j := (D.obj j).str
      naturality _ _ g := (D.map g).h }
  have : ∀ j, IsIso (α.app j) := hD
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have h : c.pt.str =
      (IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves F t) t (asIso α)).hom :=
    (isColimitOfPreserves F t).hom_ext fun j ↦
      (c.ι.app j).h.trans
        (IsColimit.comp_coconePointsIsoOfNatIso_hom (isColimitOfPreserves F t) t (asIso α) j).symm
  change IsIso c.pt.str
  rw [h]
  exact Iso.isIso_hom _

instance {J : Type w'} [Category.{w} J] [HasLimitsOfShape J C] [PreservesLimitsOfShape J F] :
    (IsIsoStr F).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro _ ⟨h⟩
    exact isIsoStr_of_isLimit h.isLimit h.prop_diag_obj

instance {J : Type w'} [Category.{w} J] [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    (IsIsoStr F).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro _ ⟨h⟩
    exact isIsoStr_of_isColimit h.isColimit h.prop_diag_obj

variable [Abelian C] [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

open ZeroObject in
instance : (IsIsoStr F).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    have h : IsZero (0 : Algebra F).a := (forget F).map_isZero (isZero_zero _)
    exact (F.map_isZero h).isIso h _

instance : (IsIsoStr F).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (IsIsoStr F).prop_of_isLimit hk (by rintro (_ | _) <;> assumption)

instance : (IsIsoStr F).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (IsIsoStr F).prop_of_isColimit hk (by rintro (_ | _) <;> assumption)

instance : (IsIsoStr F).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    have := Fintype.ofFinite J
    infer_instance

end IsIsoStr

end Algebra

namespace IsoAlgebra

section Preadditive

variable {F : C ⥤ C} [Preadditive C] [F.Additive]

instance : Preadditive (IsoAlgebra F) :=
  inferInstanceAs (Preadditive (Algebra.IsIsoStr F).FullSubcategory)

instance : (ι F).Additive :=
  inferInstanceAs (Algebra.IsIsoStr F).ι.Additive

instance : (forget F).Additive :=
  inferInstanceAs (ι F ⋙ Algebra.forget F).Additive

instance : (ι F).Full :=
  inferInstanceAs (Algebra.IsIsoStr F).ι.Full

instance : (ι F).Faithful :=
  inferInstanceAs (Algebra.IsIsoStr F).ι.Faithful

instance : (forget F).ReflectsIsomorphisms :=
  inferInstanceAs (ι F ⋙ Algebra.forget F).ReflectsIsomorphisms

end Preadditive

variable (F : C ⥤ C) [Abelian C] [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The category of algebras with invertible structure morphism of an exact additive
endofunctor of an abelian category is abelian. -/
instance abelian : Abelian (IsoAlgebra F) :=
  inferInstanceAs (Abelian (Algebra.IsIsoStr F).FullSubcategory)

instance {K L : IsoAlgebra F} (φ : K ⟶ L) : PreservesLimit (parallelPair φ 0) (ι F) :=
  (Algebra.IsIsoStr F).preservesKernels_ι φ

instance {K L : IsoAlgebra F} (φ : K ⟶ L) : PreservesColimit (parallelPair φ 0) (ι F) :=
  (Algebra.IsIsoStr F).preservesCokernels_ι φ

instance : PreservesFiniteLimits (ι F) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

instance : PreservesFiniteColimits (ι F) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

instance : PreservesFiniteLimits (forget F) :=
  comp_preservesFiniteLimits (ι F) (Algebra.forget F)

instance : PreservesFiniteColimits (forget F) :=
  comp_preservesFiniteColimits (ι F) (Algebra.forget F)

variable {F}

/-- The underlying object of the kernel of a morphism of algebras with invertible structure
morphism is the kernel of the underlying morphism. -/
def forgetKernelIso {K L : IsoAlgebra F} (φ : K ⟶ L) :
    (forget F).obj (kernel φ) ≅ kernel φ.hom.f :=
  PreservesKernel.iso (forget F) φ

@[reassoc (attr := simp)]
lemma forgetKernelIso_hom_ι {K L : IsoAlgebra F} (φ : K ⟶ L) :
    (forgetKernelIso φ).hom ≫ kernel.ι φ.hom.f = (kernel.ι φ).hom.f :=
  by
  rw [forgetKernelIso, PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι φ (forget F)

/-- The underlying object of the cokernel of a morphism of algebras with invertible structure
morphism is the cokernel of the underlying morphism. -/
def forgetCokernelIso {K L : IsoAlgebra F} (φ : K ⟶ L) :
    (forget F).obj (cokernel φ) ≅ cokernel φ.hom.f :=
  PreservesCokernel.iso (forget F) φ

@[reassoc (attr := simp)]
lemma π_forgetCokernelIso_inv {K L : IsoAlgebra F} (φ : K ⟶ L) :
    cokernel.π φ.hom.f ≫ (forgetCokernelIso φ).inv = (cokernel.π φ).hom.f :=
  by
  rw [forgetCokernelIso, PreservesCokernel.iso_inv]
  exact π_comp_cokernelComparison φ (forget F)

end IsoAlgebra

end CategoryTheory.Endofunctor
