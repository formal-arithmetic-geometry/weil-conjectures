/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModBraided
public import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComp

/-!

# The derived pullback of module objects is symmetric monoidal

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback `Lf^* = L((f)^*⟦Λ⟧)` with its monoidal structure
`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar` is braided for the Koszul braidings
`DerivedCategory.braidedCategory'` of the derived tensor products
(`ProEtale.CondensedRing.leftDerivedUpperStar_μ_map_braiding_hom`).

The pullback `f^* = mapMod(f^*) ⋙ Ext_{α_f}` of module objects is braided
(`ProEtale.CondensedRing.braided_upperStar`), being the composite of braided functors. On
complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` is therefore compatible with the Koszul
braidings. The comparison `m : Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L` is a natural transformation into
the left derived bifunctor `Lf^* - ⊗ᴸ Lf^* -`, characterized by its composite with the counit;
so is `Lf^* β_{K, L} ≫ m_{L, K} ≫ β_{Lf^* L, Lf^* K}`, and both have the same composite with the
counit, by the compatibility on complexes and the symmetry of the braidings.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback `f^* = mapMod(f^*) ⋙ Ext_{α_f}` of module objects over `Λ` is braided, as the
composite of braided functors. It is not an instance, to avoid a second path to the monoidal
structure `ProEtale.CondensedRing.monoidal_upperStar`. -/
@[instance_reducible]
noncomputable def braided_upperStar : (f)^*⟦Λ⟧.Braided :=
  inferInstanceAs ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y) ⋙
    Mod.extendScalars (condensedPullbackHom Λ f)).Braided

/-- The pullback of module objects is compatible with the braidings, in the form of the
comonoidal structure. -/
lemma upperStar_μ_map_braiding_hom
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ M N ≫ (f)^*⟦Λ⟧.map (β_ M N).hom =
      (β_ ((f)^*⟦Λ⟧.obj M) ((f)^*⟦Λ⟧.obj N)).hom ≫ Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ N M :=
  (braided_upperStar Λ f).braided M N

set_option maxHeartbeats 1000000 in
-- `erw` unfolds the tensor product of complexes of module objects to its components.
/-- On complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` is compatible with the Koszul
braidings. -/
@[reassoc]
lemma upperStarTensorComplexHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
        (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B)).hom ≫ upperStarTensorComplexHom Λ f B A =
      upperStarTensorComplexHom Λ f A B ≫ ((f)^*⟦Λ⟧.mapHomologicalComplex _).map (β_ A B).hom := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [CochainComplex.Monoidal.ι_braiding_hom_assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Preadditive.zsmul_comp, Category.assoc]
  simp only [HomologicalComplex.ι_mapBifunctorDesc]
  have hβ := CochainComplex.Monoidal.ι_braiding_hom (K := A) (L := B) p q n h
  rw [Category.assoc, ← Functor.map_comp,
    show (β_ A B).hom = (CochainComplex.Monoidal.braiding A B).hom from rfl, hβ]
  simp only [Functor.map_zsmul, Preadditive.comp_zsmul, Functor.map_comp]
  rw [reassoc_of% (upperStar_μ_map_braiding_hom Λ f (A.X p) (B.X q))]
  rfl

/-- `upperStarTensorComplexHom_braiding` in the homotopy category. -/
@[reassoc]
lemma quotient_map_upperStarTensorComplexHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (β_ ((HomotopyCategory.quotient _ _).obj (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A))
        ((HomotopyCategory.quotient _ _).obj (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B))).hom ≫
      (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f B A) =
    (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f A B) ≫
      (HomotopyCategory.quotient _ _).map (((f)^*⟦Λ⟧.mapHomologicalComplex _).map
        (β_ A B).hom) := by
  rw [← Functor.map_comp, ← upperStarTensorComplexHom_braiding, Functor.map_comp]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory.MonoidalCategory

open Functor.LaxMonoidal

variable {HY HX DY DX : Type*} [Category HY] [Category HX] [Category DY] [Category DX]
  [MonoidalCategory HY] [MonoidalCategory HX] [MonoidalCategory DY] [MonoidalCategory DX]
  [BraidedCategory HY] [BraidedCategory HX] [BraidedCategory DY] [BraidedCategory DX]
  {Qy : HY ⥤ DY} {Qx : HX ⥤ DX} [Qy.LaxMonoidal] [Qx.LaxMonoidal] {LF : DY ⥤ DX}
  {FK : HY ⥤ HX} (ε : Qy ⋙ LF ⟶ FK ⋙ Qx)
  (m : ∀ K M : DY, LF.obj (K ⊗ M) ⟶ LF.obj K ⊗ LF.obj M)
  (T : ∀ P Q : HY, FK.obj P ⊗ FK.obj Q ⟶ FK.obj (P ⊗ Q))

/-- The braided transform `LF β ≫ m ≫ β` of a tensor comparison `m` of a left derived functor
has the same composite with the counit as `m`, if the underived comparison `T` is compatible
with the braidings and the braidings of the localizations and of the source are compatible and
symmetric. -/
lemma derived_braiding_tensor_aux
    (hfac : ∀ P Q : HY, m (Qy.obj P) (Qy.obj Q) ≫ (ε.app P ⊗ₘ ε.app Q) ≫ μ Qx _ _ ≫
      Qx.map (T P Q) = LF.map (μ Qy P Q) ≫ ε.app (P ⊗ Q))
    (hβx : ∀ X Y : HX, (β_ (Qx.obj X) (Qx.obj Y)).hom ≫ μ Qx Y X = μ Qx X Y ≫ Qx.map (β_ X Y).hom)
    (hβy : ∀ X Y : HY, (β_ (Qy.obj X) (Qy.obj Y)).hom ≫ μ Qy Y X = μ Qy X Y ≫ Qy.map (β_ X Y).hom)
    (hT : ∀ P Q : HY, (β_ (FK.obj P) (FK.obj Q)).hom ≫ T Q P = T P Q ≫ FK.map (β_ P Q).hom)
    (hsymm : ∀ P Q : HY, (β_ P Q).hom ≫ (β_ Q P).hom = 𝟙 _) (P Q : HY) :
    (LF.map (β_ (Qy.obj P) (Qy.obj Q)).hom ≫ m (Qy.obj Q) (Qy.obj P) ≫
        (β_ (LF.obj (Qy.obj Q)) (LF.obj (Qy.obj P))).hom) ≫ (ε.app P ⊗ₘ ε.app Q) ≫
      μ Qx _ _ ≫ Qx.map (T P Q) = LF.map (μ Qy P Q) ≫ ε.app (P ⊗ Q) := by
  have hε := ε.naturality (β_ Q P).hom
  simp only [Functor.comp_map] at hε
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  simp only [Functor.comp_obj]
  rw [reassoc_of% (hβx _ _), ← Qx.map_comp, hT,
    Qx.map_comp, reassoc_of% (hfac Q P), ← hε, ← LF.map_comp_assoc, ← LF.map_comp_assoc,
    Category.assoc, reassoc_of% (hβy P Q), ← Qy.map_comp, hsymm, Qy.map_id, Category.comp_id]

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor DerivedCategory

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

attribute [local instance] DerivedCategory.braidedCategory'

set_option maxHeartbeats 2000000 in
-- the derived categories of module objects are unfolded in the naturality checks
/-- The braided transform `(K, M) ↦ Lf^* β_{K, M} ≫ m_{M, K} ≫ β_{Lf^* M, Lf^* K}` of the tensor
comparison `m` of the derived pullback. It is `m` (`leftDerivedUpperStarTensor_eq_braid`). -/
noncomputable def leftDerivedUpperStarTensorBraid :
    leftDerivedUpperStarTensorLeft Λ f ⟶ leftDerivedUpperStarTensorRight Λ f where
  app K :=
    { app M := L((f)^*⟦Λ⟧).map (β_ K M).hom ≫ ((leftDerivedUpperStarTensor Λ f).app M).app K ≫
        (β_ (L((f)^*⟦Λ⟧).obj M) (L((f)^*⟦Λ⟧).obj K)).hom
      naturality M M' b := by
        have h := NatTrans.congr_app ((leftDerivedUpperStarTensor Λ f).naturality b) K
        dsimp [leftDerivedUpperStarTensorLeft, leftDerivedUpperStarTensorRight] at h ⊢
        rw [← Functor.map_comp_assoc (L((f)^*⟦Λ⟧)) (K ◁ b) (β_ K M').hom,
          BraidedCategory.braiding_naturality_right]
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% h, BraidedCategory.braiding_naturality_left] }
  naturality K K' a := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    have h := ((leftDerivedUpperStarTensor Λ f).app M).naturality a
    dsimp [leftDerivedUpperStarTensorLeft, leftDerivedUpperStarTensorRight] at h ⊢
    rw [← Functor.map_comp_assoc (L((f)^*⟦Λ⟧)) (a ▷ M) (β_ K' M).hom,
      BraidedCategory.braiding_naturality_left]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% h, BraidedCategory.braiding_naturality_right]

end AlgebraicGeometry.ProEtale.CondensedRing
