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
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
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

-- Stacks 0G7D: complete the cone square in K(A), then apply the exact localization.
set_option backward.isDefEq.respectTransparency false in
open Pretriangulated in
private theorem cone_factorization
    {A : Type*} [Category A] [Abelian A]
    {D I M : CochainComplex A ℤ} (t : D ⟶ I)
    (m : M ⟶ mappingCone t) [QuasiIso m] :
    let g := m ≫ (mappingCone.triangle t).mor₃
    ∃ (u : D ⟶ (mappingCone g)⟦(-1 : ℤ)⟧)
      (c : (mappingCone g)⟦(-1 : ℤ)⟧ ⟶ I),
      QuasiIso c ∧ Nonempty (Homotopy t (u ≫ c)) := by
  classical
  let := HasDerivedCategory.standard A
  let q := HomotopyCategory.quotient A (.up ℤ)
  let g := m ≫ (mappingCone.triangle t).mor₃
  let S := mappingCone.triangleh g
  let T := mappingCone.triangleh t
  have hS := HomotopyCategory.mappingCone_triangleh_distinguished g
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished t
  let b := ((q.commShiftIso (1 : ℤ)).app D).hom
  have comm : S.mor₁ ≫ b = q.map m ≫ T.rotate.rotate.mor₁ := by
    change q.map (m ≫ (mappingCone.triangle t).mor₃) ≫ b =
      q.map m ≫ (q.map (mappingCone.triangle t).mor₃ ≫ b)
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨w, hw₂, hw₃⟩ := complete_distinguished_triangle_morphism S T.rotate.rotate
    hS (rot_of_distTriang _ (rot_of_distTriang _ hT)) (q.map m) b comm
  let f' : S ⟶ T.rotate.rotate :=
    { hom₁ := q.map m, hom₂ := b, hom₃ := w, comm₁ := comm,
      comm₂ := hw₂, comm₃ := hw₃ }
  let eT : T ≅ T.rotate.rotate.invRotate.invRotate :=
    (rotCompInvRot.app T) ≪≫ (invRotate _).mapIso (rotCompInvRot.app T.rotate)
  let f : S.invRotate.invRotate ⟶ T :=
    (invRotate _).map ((invRotate _).map f') ≫ eT.inv
  let eN := (q.commShiftIso (-1 : ℤ)).app (mappingCone g)
  have hi₁ : IsIso f.hom₁ := by
    change IsIso (b⟦(-1 : ℤ)⟧' ≫ eT.inv.hom₁)
    dsimp only [b]
    infer_instance
  have hi₃ : IsIso (DerivedCategory.Qh.map f.hom₃) := by
    have : IsIso (DerivedCategory.Qh.map (q.map m)) :=
      (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) m).2 inferInstance
    change IsIso (DerivedCategory.Qh.map (q.map m ≫ eT.inv.hom₃))
    rw [Functor.map_comp]
    infer_instance
  let := hi₁
  have hi₂ : IsIso (DerivedCategory.Qh.map f.hom₂) := by
    exact isIso₂_of_isIso₁₃ (DerivedCategory.Qh.mapTriangle.map f)
      (DerivedCategory.Qh.map_distinguished _
        (inv_rot_of_distTriang _ (inv_rot_of_distTriang _ hS)))
      (DerivedCategory.Qh.map_distinguished _ hT)
      (show IsIso (DerivedCategory.Qh.map f.hom₁) from inferInstance) hi₃
  let u := q.preimage (inv f.hom₁ ≫ S.invRotate.invRotate.mor₁ ≫ eN.inv)
  let c := q.preimage (eN.hom ≫ f.hom₂)
  have hc : QuasiIso c := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A c).1
    have : IsIso (DerivedCategory.Qh.map (q.map c)) := by
      simp only [c, Functor.map_preimage, Functor.map_comp]
      infer_instance
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) c).1 this
  refine ⟨u, c, hc, ?_⟩
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  change q.map t = q.map u ≫ q.map c
  rw [show q.map u = _ from q.map_preimage _,
    show q.map c = _ from q.map_preimage _]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [f.comm₁, IsIso.inv_hom_id_assoc]
  rfl

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{r}}

-- Acyclic complexes form a triangulated subcategory of K(A).
private theorem acyclic_shift
    {A : Type*} [Category A] [Abelian A] (K : CochainComplex A ℤ)
    (hK : K.Acyclic) (n : ℤ) : (K⟦n⟧).Acyclic := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let P := HomotopyCategory.subcategoryAcyclic A
  have h : P (q.obj K) :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K).2 hK
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
  exact ObjectProperty.prop_of_iso P ((q.commShiftIso n).app K).symm (P.le_shift n _ h)

-- The signed total-tensor shift comparison works at independent site universes.
private theorem kFlat_shift
    (K : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hK : IsKFlatIndependentCoefficients K) (n : ℤ) :
    IsKFlatIndependentCoefficients (K⟦n⟧) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF
  have h := acyclic_shift _ (hK F hF) n
  intro i
  exact (h i).of_iso (mapBifunctorShift₂Iso F K (MonoidalCategory.curriedTensor _) n).symm

-- Tensor the cone triangle with an acyclic complex and use its homology sequence.
private theorem kFlat_cone
    {K L : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (f : K ⟶ L) (hK : IsKFlatIndependentCoefficients K)
    (hL : IsKFlatIndependentCoefficients L) :
    IsKFlatIndependentCoefficients (mappingCone f) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF
  let f' := HomologicalComplex.mapBifunctorMap (𝟙 F) f
    (MonoidalCategory.curriedTensor _) (.up ℤ)
  have h₁ := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hK F hF)
  have h₂ := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hL F hF)
  have h₃ := (HomotopyCategory.subcategoryAcyclic _).ext_of_isTriangulatedClosed₃ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f') h₁ h₂
  have h := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 h₃
  intro i
  exact (h i).of_iso (mapBifunctorMappingCone₂Iso F f
    (MonoidalCategory.curriedTensor _)).symm

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
  let A := SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  obtain ⟨M, m, hM, hflatM, hm, _⟩ :=
    exists_isKFlatResolutionIndependentCoefficients (R := R) (mappingCone t)
  let := hm
  let g := m ≫ (mappingCone.triangle t).mor₃
  let N := (mappingCone g)⟦(-1 : ℤ)⟧
  obtain ⟨u, c, hc, hhom⟩ := cone_factorization t m
  refine ⟨N, u, c, kFlat_shift _ (kFlat_cone g hM (kFlat_shift D hD 1)) (-1),
    hc, hhom, ?_⟩
  intro hflatD i
  have toFlat (P : A) (hP : exactFunctor _ _ (MonoidalCategory.tensorRight P)) :
      ObjectProperty.flat P := by
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight P).symm hP, hP⟩
  have hMi : ObjectProperty.flat (M.X i) := toFlat _ (hflatM i)
  have hDi : ObjectProperty.flat (D.X i) := toFlat _
    ((exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R (D.X i))
      (hflatD i))
  have hsum : ObjectProperty.flat (M.X i ⊞ D.X i) := by
    apply ObjectProperty.prop_of_iso _ (biprod.isoProd _ _).symm
    exact ObjectProperty.prop_of_isLimit _ (limit.isLimit (pair (M.X i) (D.X i)))
      (by rintro ⟨_ | _⟩ <;> assumption)
  let e : N.X i ≅ M.X i ⊞ D.X i :=
    (mappingCone g).shiftFunctorObjXIso (-1) i (i - 1) (by omega) ≪≫
      HomologicalComplex.homotopyCofiber.XIsoBiprod g (i - 1) i
        (by change i - 1 + 1 = i; omega) ≪≫
      biprod.mapIso (Iso.refl _) (D.shiftFunctorObjXIso 1 (i - 1) i (by omega))
  have hNi : ObjectProperty.flat (N.X i) := ObjectProperty.prop_of_iso _ e.symm hsum
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (N.X i)).symm hNi.2

end CochainComplex
