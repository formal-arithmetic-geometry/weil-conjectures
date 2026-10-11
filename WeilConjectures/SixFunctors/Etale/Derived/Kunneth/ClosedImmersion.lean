/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Vanishing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The external product and restriction to closed subschemes

For closed immersions `i : Z ⟶ X` and `j : W ⟶ Y` over a base `B`, with product
`i ×_B j : Z ×_B W ⟶ X ×_B Y`,

`(i ×_B j)_* (i ×_B j)^* (K ⊠ L) ≅ i_* i^* K ⊠ j_* j^* L`

(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion_of_flat`).

The proof characterises the objects `ι_* ι^* N` of `D(X_ét)` for a closed immersion `ι` by their
support: if `φ : N ⟶ M` becomes invertible after `Lι^*` and `M` vanishes on the open
complement of `ι`, then `M ≅ Rι_* Lι^* N`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_obj_leftDerivedUpperStar_obj`), by
the open–closed triangle. It is applied to `i ×_B 𝟙` and `𝟙 ×_B j` separately: the open
complement of `i ×_B 𝟙` is the preimage of the open complement of `i`, on which `Ri_* Li^* K`,
hence `Ri_* Li^* K ⊠ L`, vanishes; and the unit `K ⟶ Ri_* Li^* K` is invertible after `Li^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

section Support

variable {Z X U : Scheme.{u}}

/-- **Objects supported on a closed subscheme.** Let `i : Z ⟶ X` be a closed immersion with open
complement `j : U ⟶ X`. If `φ : N ⟶ M` becomes invertible after `Li^*` and `Lj^* M = 0`, then
`Ri_* Li^* N ≅ M`: the open–closed triangle of `M` identifies `M` with `Ri_* i^* M`. -/
theorem nonempty_iso_rightDerivedLowerStar_obj_leftDerivedUpperStar_obj (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {N M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : N ⟶ M)
    (hM : IsZero ((L((j)^*[A])).obj M)) (hφ : IsIso ((L((i)^*[A])).map φ)) :
    Nonempty ((R((i)_*[A])).obj ((L((i)^*[A])).obj N) ≅ M) := by
  obtain ⟨w, hT⟩ := exists_distTriang_openClosed A j i hij M
  have h₁ : IsZero (D((j)_!open[A]).obj (D((j)^*[A]).obj M)) :=
    D((j)_!open[A]).map_isZero
      (hM.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory A j).app M).symm)
  have : IsIso ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M) :=
    (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ hT).1 h₁
  exact ⟨(R((i)_*[A])).mapIso (asIso ((L((i)^*[A])).map φ) ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory A i).app M) ≪≫
    (asIso ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M)).symm⟩

/-- For a closed immersion `i`, the unit `K ⟶ Ri_* Li^* K` becomes invertible after `Li^*`:
`Ri_*` is fully faithful, so the counit of `Li^* ⊣ Ri_*` is invertible. -/
lemma isIso_leftDerivedUpperStar_map_unit_of_isClosedImmersion (i : Z ⟶ X)
    [IsClosedImmersion i] (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso ((L((i)^*[A])).map ((derivedUpperStarLowerStarAdjunction A i).unit.app K)) := by
  have : ((i)_*[A]).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction A i).preservesKInjectiveComplexes
  have : IsIso (derivedUpperStarLowerStarAdjunction A i).counit :=
    (derivedUpperStarLowerStarAdjunction A i).counit_isIso_of_R_fully_faithful
  have h := (derivedUpperStarLowerStarAdjunction A i).left_triangle_components K
  have : IsIso ((L((i)^*[A])).map ((derivedUpperStarLowerStarAdjunction A i).unit.app K) ≫
      (derivedUpperStarLowerStarAdjunction A i).counit.app ((L((i)^*[A])).obj K)) := by
    rw [h]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ ((derivedUpperStarLowerStarAdjunction A i).counit.app _)

end Support

section ExternalProduct

variable {B X Y Z W : Scheme.{u}}

/-- The external product `a ⊠ b : K ⊠ L ⟶ K' ⊠ L'` of two morphisms. -/
noncomputable def externalProductMap (f : X ⟶ B) (g : Y ⟶ B)
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (a : K ⟶ K') (b : L ⟶ L') :
    externalProduct A f g K L ⟶ externalProduct A f g K' L' :=
  ((derivedTensor A (pullback f g)).map ((L((pullback.fst f g)^*[A])).map a)).app _ ≫
    ((derivedTensor A (pullback f g)).obj _).map ((L((pullback.snd f g)^*[A])).map b)

variable [UpperStarPreservesFlat A]

/-- The derived pullback along `ψ` of the derived tensor product with a morphism `x` in the first
variable is invertible if `Lψ^* x` is. -/
lemma isIso_leftDerivedUpperStar_map_derivedTensor_map_app {P Q : Scheme.{u}} (ψ : P ⟶ Q)
    {M M' : _root_.DerivedCategory (Sheaf Q.smallEtaleTopology A)} (x : M ⟶ M')
    (y : _root_.DerivedCategory (Sheaf Q.smallEtaleTopology A))
    (hx : IsIso ((L((ψ)^*[A])).map x)) :
    IsIso ((L((ψ)^*[A])).map (((derivedTensor A Q).map x).app y)) := by
  have h := NatTrans.congr_app ((leftDerivedUpperStarTensorNatIso A ψ).hom.naturality x) y
  have : IsIso (((derivedTensorLeftDerivedUpperStar A ψ).map x).app y) :=
    inferInstanceAs (IsIso (((derivedTensor A P).map ((L((ψ)^*[A])).map x)).app
      ((L((ψ)^*[A])).obj y)))
  simp only [NatTrans.comp_app] at h
  have : IsIso ((L((ψ)^*[A])).map (((derivedTensor A Q).map x).app y) ≫
      (((leftDerivedUpperStarTensorNatIso A ψ).hom.app M').app y)) := by
    erw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (((leftDerivedUpperStarTensorNatIso A ψ).hom.app M').app y)

/-- The derived pullback along `ψ` of the derived tensor product with a morphism `y` in the second
variable is invertible if `Lψ^* y` is. -/
lemma isIso_leftDerivedUpperStar_map_derivedTensor_obj_map {P Q : Scheme.{u}} (ψ : P ⟶ Q)
    (x : _root_.DerivedCategory (Sheaf Q.smallEtaleTopology A))
    {M M' : _root_.DerivedCategory (Sheaf Q.smallEtaleTopology A)} (y : M ⟶ M')
    (hy : IsIso ((L((ψ)^*[A])).map y)) :
    IsIso ((L((ψ)^*[A])).map (((derivedTensor A Q).obj x).map y)) := by
  have h := ((leftDerivedUpperStarTensorNatIso A ψ).hom.app x).naturality y
  have : IsIso (((derivedTensorLeftDerivedUpperStar A ψ).obj x).map y) :=
    inferInstanceAs (IsIso (((derivedTensor A P).obj ((L((ψ)^*[A])).obj x)).map
      ((L((ψ)^*[A])).map y)))
  have : IsIso ((L((ψ)^*[A])).map (((derivedTensor A Q).obj x).map y) ≫
      (((leftDerivedUpperStarTensorNatIso A ψ).hom.app x).app M')) := by
    erw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (((leftDerivedUpperStarTensorNatIso A ψ).hom.app x).app M')

/-- Let `ψ : Z ×_B W ⟶ X ×_B Y` be compatible with `i : Z ⟶ X` and `j : W ⟶ Y`. The pullback
`Lψ^* (a ⊠ b)` of an external product of morphisms is invertible if `Li^* a` and `Lj^* b` are. -/
lemma isIso_leftDerivedUpperStar_map_externalProductMap (f : X ⟶ B) (g : Y ⟶ B)
    (f' : Z ⟶ B) (g' : W ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y) (ψ : pullback f' g' ⟶ pullback f g)
    (h₁ : ψ ≫ pullback.fst f g = pullback.fst f' g' ≫ i)
    (h₂ : ψ ≫ pullback.snd f g = pullback.snd f' g' ≫ j)
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (a : K ⟶ K') (b : L ⟶ L')
    (ha : IsIso ((L((i)^*[A])).map a)) (hb : IsIso ((L((j)^*[A])).map b)) :
    IsIso ((L((ψ)^*[A])).map (externalProductMap A f g a b)) := by
  let e₁ : L((pullback.fst f g)^*[A]) ⋙ L((ψ)^*[A]) ≅
      L((i)^*[A]) ⋙ L((pullback.fst f' g')^*[A]) :=
    (leftDerivedUpperStarComp A ψ (pullback.fst f g) (pullback.fst f' g' ≫ i) h₁.symm).symm ≪≫
      leftDerivedUpperStarComp A (pullback.fst f' g') i
  let e₂ : L((pullback.snd f g)^*[A]) ⋙ L((ψ)^*[A]) ≅
      L((j)^*[A]) ⋙ L((pullback.snd f' g')^*[A]) :=
    (leftDerivedUpperStarComp A ψ (pullback.snd f g) (pullback.snd f' g' ≫ j) h₂.symm).symm ≪≫
      leftDerivedUpperStarComp A (pullback.snd f' g') j
  have hx : IsIso ((L((ψ)^*[A])).map ((L((pullback.fst f g)^*[A])).map a)) :=
    (NatIso.isIso_map_iff e₁ a).2 (inferInstanceAs
      (IsIso ((L((pullback.fst f' g')^*[A])).map ((L((i)^*[A])).map a))))
  have hy : IsIso ((L((ψ)^*[A])).map ((L((pullback.snd f g)^*[A])).map b)) :=
    (NatIso.isIso_map_iff e₂ b).2 (inferInstanceAs
      (IsIso ((L((pullback.snd f' g')^*[A])).map ((L((j)^*[A])).map b))))
  have := isIso_leftDerivedUpperStar_map_derivedTensor_map_app A ψ _
    ((L((pullback.snd f g)^*[A])).obj L) hx
  have := isIso_leftDerivedUpperStar_map_derivedTensor_obj_map A ψ
    ((L((pullback.fst f g)^*[A])).obj K') _ hy
  rw [externalProductMap, Functor.map_comp]
  infer_instance

/-- The external product is compatible with pullback along a morphism
`ψ : Z ×_B W ⟶ X ×_B Y` compatible with `i : Z ⟶ X` and `j : W ⟶ Y`:
`Lψ^* (K ⊠ L) ≅ Li^* K ⊠ Lj^* L`. -/
theorem nonempty_iso_leftDerivedUpperStar_externalProduct_of_comp (f : X ⟶ B) (g : Y ⟶ B)
    (f' : Z ⟶ B) (g' : W ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y) (ψ : pullback f' g' ⟶ pullback f g)
    (h₁ : ψ ≫ pullback.fst f g = pullback.fst f' g' ≫ i)
    (h₂ : ψ ≫ pullback.snd f g = pullback.snd f' g' ≫ j)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Nonempty ((L((ψ)^*[A])).obj (externalProduct A f g K L) ≅
      externalProduct A f' g' ((L((i)^*[A])).obj K) ((L((j)^*[A])).obj L)) := by
  let pb₁ : (L((ψ)^*[A])).obj ((L((pullback.fst f g)^*[A])).obj K) ≅
      (L((pullback.fst f' g')^*[A])).obj ((L((i)^*[A])).obj K) :=
    ((leftDerivedUpperStarComp A ψ (pullback.fst _ _)).app K).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (ψ ≫ pullback.fst _ _) h₁).app K
  let pb₂ : (L((ψ)^*[A])).obj ((L((pullback.snd f g)^*[A])).obj L) ≅
      (L((pullback.snd f' g')^*[A])).obj ((L((j)^*[A])).obj L) :=
    ((leftDerivedUpperStarComp A ψ (pullback.snd _ _)).app L).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (ψ ≫ pullback.snd _ _) h₂).app L
  exact ⟨leftDerivedUpperStarTensorIso A ψ _ _ ≪≫ ((derivedTensor A _).mapIso pb₁).app _ ≪≫
    ((derivedTensor A _).obj _).mapIso pb₂⟩

end ExternalProduct

end Etale

end AlgebraicGeometry
