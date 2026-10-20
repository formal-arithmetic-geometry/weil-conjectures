/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
/-!
# Factorization through a K-flat complex

Source: Stacks Project, Cohomology on Sites, Tag 0G7D, lemma-factor-through-K-flat,
including the final flat-terms assertion (blueprint: lem-pur-kflat-map-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{r}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Pretriangulated in
private theorem cone_factorization
    {A : Type*} [Category A] [Abelian A] {D I M : CochainComplex A ℤ}
    (t : D ⟶ I) (m : M ⟶ mappingCone t) (hm : QuasiIso m) :
    let g := m ≫ (mappingCone.triangle t).mor₃
    ∃ (u : D ⟶ (mappingCone g)⟦(-1 : ℤ)⟧)
      (c : (mappingCone g)⟦(-1 : ℤ)⟧ ⟶ I),
      QuasiIso c ∧ Nonempty (Homotopy t (u ≫ c)) := by
  classical
  let := HasDerivedCategory.standard A
  let q := HomotopyCategory.quotient A (.up ℤ)
  -- Resolve the third vertex, then build the backwards-rotated cone triangle.
  let g := m ≫ (mappingCone.triangle t).mor₃
  let W := mappingCone g
  let N := W⟦(-1 : ℤ)⟧
  let e := (q.commShiftIso (1 : ℤ)).app D
  let f := q.map g ≫ e.hom
  let T := Triangle.mk f (e.inv ≫ (mappingCone.triangleh g).mor₂)
    (mappingCone.triangleh g).mor₃
  have hT : T ∈ distTriang _ := by
    apply isomorphic_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished g)
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
      (by simp [T, f]; rfl) (by simp [T]) (by simp [T])
  let T' := T.invRotate.invRotate
  let eD := (shiftEquiv (HomotopyCategory A (.up ℤ)) (1 : ℤ)).unitIso.app (q.obj D)
  let S := Triangle.mk (eD.hom ≫ T'.mor₁) T'.mor₂ f
  have hS : S ∈ distTriang _ := by
    apply isomorphic_distinguished _ (inv_rot_of_distTriang _ (inv_rot_of_distTriang _ hT))
    exact Triangle.isoMk _ _ eD (Iso.refl _) (Iso.refl _)
      (by cat_disch) (by cat_disch)
      (by dsimp [S, T', T, eD, Triangle.invRotate, Triangle.mk];
          simp only [shift_shiftFunctorCompIsoId_inv_app, Category.id_comp])
  have hf : f = q.map m ≫ (mappingCone.triangleh t).mor₃ := by
    change q.map g ≫ e.hom =
      q.map m ≫ (q.map (mappingCone.triangle t).mor₃ ≫ e.hom)
    rw [← Category.assoc, ← q.map_comp]
  -- TR3 supplies the middle map with identity on D and m on the resolved cone.
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ S
    (mappingCone.triangleh t) hS (HomotopyCategory.mappingCone_triangleh_distinguished t)
    (𝟙 _) (q.map m) (by
      change f ≫ (𝟙 (q.obj D))⟦(1 : ℤ)⟧' = q.map m ≫ _
      exact (congrArg (fun k ↦ f ≫ k)
        ((CategoryTheory.shiftFunctor (HomotopyCategory A (.up ℤ)) (1 : ℤ)).map_id (q.obj D))).trans
          ((Category.comp_id f).trans hf))
  let eN : q.obj N ≅ S.obj₂ := (q.commShiftIso (-1 : ℤ)).app W
  let u : D ⟶ N := q.preimage (S.mor₁ ≫ eN.inv)
  let c : N ⟶ I := q.preimage (eN.hom ≫ b)
  have huc : q.map t = q.map (u ≫ c) := by
    simp only [Functor.map_comp, u, c, Functor.map_preimage, Category.assoc,
      eN.inv_hom_id_assoc]
    change S.mor₁ ≫ b = 𝟙 _ ≫ q.map t at hb₁
    simpa using hb₁.symm
  refine ⟨u, c, ?_, ⟨HomotopyCategory.homotopyOfEq _ _ huc⟩⟩
  let φ : S ⟶ mappingCone.triangleh t :=
    { hom₁ := 𝟙 _
      hom₂ := b
      hom₃ := q.map m
      comm₁ := hb₁
      comm₂ := hb₂
      comm₃ := by
        change f ≫ (𝟙 (q.obj D))⟦(1 : ℤ)⟧' = q.map m ≫ _
        exact (congrArg (fun k ↦ f ≫ k)
          ((CategoryTheory.shiftFunctor (HomotopyCategory A (.up ℤ))
            (1 : ℤ)).map_id (q.obj D))).trans
            ((Category.comp_id f).trans hf) }
  -- In the derived category the outside maps are invertible, hence so is the middle map.
  let Q := DerivedCategory.Qh (C := A)
  have hm' : IsIso (Q.map (q.map m)) := by
    have : QuasiIso m := hm
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoMk (f := Arrow.mk (Q.map (q.map m)))
        (g := Arrow.mk (DerivedCategory.Q.map m))
        ((DerivedCategory.quotientCompQhIso A).app M)
        ((DerivedCategory.quotientCompQhIso A).app (mappingCone t))
        (by exact (DerivedCategory.quotientCompQhIso A).hom.naturality m |>.symm))).2
          (inferInstanceAs (IsIso (DerivedCategory.Q.map m)))
  have hb : IsIso (Q.map b) :=
    isIso₂_of_isIso₁₃ (Q.mapTriangle.map φ) (Q.map_distinguished _ hS)
      (Q.map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished t))
      (by dsimp [φ]; infer_instance) hm'
  have hc : IsIso (Q.map (q.map c)) := by
    simp only [c, Functor.map_preimage, Functor.map_comp]
    infer_instance
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso A c).1
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk (f := Arrow.mk (Q.map (q.map c)))
      (g := Arrow.mk (DerivedCategory.Q.map c))
      ((DerivedCategory.quotientCompQhIso A).app N)
      ((DerivedCategory.quotientCompQhIso A).app I)
      (by exact (DerivedCategory.quotientCompQhIso A).hom.naturality c |>.symm))).1 hc

private theorem acyclic_shift_factorization
    {A : Type*} [Category A] [Abelian A] {K : CochainComplex A ℤ}
    (hK : K.Acyclic) (n : ℤ) : (K⟦n⟧).Acyclic := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let P := HomotopyCategory.subcategoryAcyclic A
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
  exact P.prop_of_iso ((q.commShiftIso n).app K).symm
    (P.le_shift n _
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hK))

private theorem acyclic_cone_factorization
    {A : Type*} [Category A] [Abelian A] {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (hK : K.Acyclic) (hL : L.Acyclic) : (mappingCone f).Acyclic := by
  let P := HomotopyCategory.subcategoryAcyclic A
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
  exact P.ext_of_isTriangulatedClosed₃ _ (HomotopyCategory.mappingCone_triangleh_distinguished f)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hK)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hL)

private theorem kFlat_shift_factorization
    {K : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (hK : IsKFlatIndependentCoefficients (J := J) (R := R) K) (n : ℤ) :
    IsKFlatIndependentCoefficients (J := J) (R := R) (K⟦n⟧) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  intro F hF i
  exact (acyclic_shift_factorization (hK F hF) n i).of_iso
    (mapBifunctorShift₂Iso F K (MonoidalCategory.curriedTensor _) n).symm

private theorem kFlat_cone_factorization
    {K L : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (f : K ⟶ L) (hK : IsKFlatIndependentCoefficients (J := J) (R := R) K)
    (hL : IsKFlatIndependentCoefficients (J := J) (R := R) L) :
    IsKFlatIndependentCoefficients (J := J) (R := R) (mappingCone f) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  intro F hF i
  exact (acyclic_cone_factorization
    (HomologicalComplex.mapBifunctorMap (𝟙 F) f (MonoidalCategory.curriedTensor _) (.up ℤ))
      (hK F hF) (hL F hF) i).of_iso
        (mapBifunctorMappingCone₂Iso F f (MonoidalCategory.curriedTensor _)).symm

private theorem flat_biprod_factorization
    {M N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (hM : ObjectProperty.flat M) (hN : ObjectProperty.flat N) :
    ObjectProperty.flat (M ⊞ N) := by
  apply ObjectProperty.prop_of_iso _ (biprod.isoProd M N).symm
  exact ObjectProperty.prop_of_isLimit _ (limit.isLimit (pair M N))
    (by rintro ⟨_ | _⟩ <;> assumption)

/-- A chain map with K-flat source factors up to homotopy through a K-flat target.

Source: Stacks Project, Cohomology on Sites, Tag 0G7D, lemma-factor-through-K-flat
(blueprint: lem-pur-kflat-map-factorization).

The proof follows the source and uses the recorded generic K-flat resolution and cone
closure statements. First form the distinguished cone triangle of `t`, and resolve its
cone by a K-flat complex `M` with flat terms. Compose the connecting map with the
resolution map, then take the shifted cone of that composite; this gives a complex `N`
whose outer maps are `u : D ⟶ N` and `v : N ⟶ M`, with the required cone signs. K-flatness
of shifts follows from the signed reindexing of the total tensor complex, and cone closure
then gives K-flatness of `N`. Rotating the two cone triangles and applying the triangulated
morphism completion to the commuting square defined by the resolution map produces
`c : N ⟶ I` and a homotopy from `t` to `u ≫ c`. The exact localization at
quasi-isomorphisms, followed by the third-isomorphism property for a morphism of
triangles, shows that `c` is a quasi-isomorphism. The homotopy is Mathlib's
`Homotopy t (u ≫ c)`, whose components are the maps `h^i : D^i ⟶ I^(i-1)` and whose
component equation is `t^i - (u ≫ c)^i = d_I^(i-1) h^i + h^(i+1) d_D^i`. If all
terms of `D` are flat, the same shifted-cone model has terms that are finite direct sums
of flat terms, so the flat-term implication is retained in the displayed witness. -/
theorem exists_kFlat_map_factorization
    {D I : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (t : D ⟶ I) (hD : IsKFlatIndependentCoefficients (J := J) (R := R) D) :
    ∃ (N : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (u : D ⟶ N) (c : N ⟶ I),
      IsKFlatIndependentCoefficients (J := J) (R := R) N ∧
        QuasiIso c ∧ Nonempty (Homotopy t (u ≫ c)) ∧
        ((∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (D.X i)) →
          ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (N.X i)) := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  obtain ⟨M, m, hM, hflatM, hm, _⟩ :=
    exists_isKFlatResolutionIndependentCoefficients (J := J) (R := R) (mappingCone t)
  let g := m ≫ (mappingCone.triangle t).mor₃
  let N := (mappingCone g)⟦(-1 : ℤ)⟧
  obtain ⟨u, c, hc, huc⟩ := cone_factorization t m hm
  refine ⟨N, u, c, kFlat_shift_factorization
    (kFlat_cone_factorization g hM (kFlat_shift_factorization hD 1)) (-1), hc, huc, ?_⟩
  intro hflatD i
  have hD' : ObjectProperty.flat (D.X i) := by
    have hr := (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (D.X i)) (hflatD i)
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (D.X i)).symm hr, hr⟩
  have hM' : ObjectProperty.flat (M.X i) :=
    ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (M.X i)).symm
        (hflatM i), hflatM i⟩
  -- The very same cone model has terms Mⁱ ⊞ Dⁱ.
  have eX : N.X i ≅ M.X i ⊞ D.X i :=
    shiftFunctorObjXIso (mappingCone g) (-1) i (i - 1) (by omega) ≪≫
      HomologicalComplex.homotopyCofiber.XIsoBiprod g (i - 1) i (by change i - 1 + 1 = i; omega) ≪≫
        biprod.mapIso (Iso.refl _) (shiftFunctorObjXIso D 1 (i - 1) i (by omega))
  have hn := ObjectProperty.prop_of_iso _ eX.symm (flat_biprod_factorization hM' hD')
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (N.X i)).symm hn.2

end CochainComplex
