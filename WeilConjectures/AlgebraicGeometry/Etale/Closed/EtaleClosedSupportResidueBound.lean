/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.Finite.FiniteCohomologicalDimensionDirectImageCoproducts
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalConstantTensor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportAmplitude

/-!
# Residue tensor bound for closed support

Source: blueprint prop-exc-closed-tor, tensor-support comparison paragraphs
(blueprint: lem-exc-closed-residue-bound).
-/
set_option autoImplicit false
@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory Pretriangulated
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem nonempty_iso_of_distinguished_square
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (Δ₁ Δ₂ : Triangle C) (h₁ : Δ₁ ∈ distTriang C) (h₂ : Δ₂ ∈ distTriang C)
    (e₂ : Δ₁.obj₂ ≅ Δ₂.obj₂) (e₃ : Δ₁.obj₃ ≅ Δ₂.obj₃)
    (h : Δ₁.mor₂ ≫ e₃.hom = e₂.hom ≫ Δ₂.mor₂) :
    Nonempty (Δ₁.obj₁ ≅ Δ₂.obj₁) := by
  obtain ⟨f, hf₁, hf₃⟩ := complete_distinguished_triangle_morphism₁
    Δ₁ Δ₂ h₁ h₂ e₂.hom e₃.hom h
  let φ : Δ₁ ⟶ Δ₂ :=
    { hom₁ := f, hom₂ := e₂.hom, hom₃ := e₃.hom
      comm₁ := hf₁, comm₂ := h, comm₃ := hf₃ }
  have : IsIso f := isIso₁_of_isIso₂₃ φ h₁ h₂ (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  exact ⟨asIso f⟩

private theorem nonempty_iso_of_mapped_distinguished_square
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
    (Δ₁ Δ₂ : Triangle C) (h₁ : Δ₁ ∈ distTriang C) (h₂ : Δ₂ ∈ distTriang C)
    (e₂ : F.obj Δ₁.obj₂ ≅ Δ₂.obj₂) (e₃ : F.obj Δ₁.obj₃ ≅ Δ₂.obj₃)
    (h : F.map Δ₁.mor₂ ≫ e₃.hom = e₂.hom ≫ Δ₂.mor₂) :
    Nonempty (F.obj Δ₁.obj₁ ≅ Δ₂.obj₁) :=
  nonempty_iso_of_distinguished_square (F.mapTriangle.obj Δ₁) Δ₂
    (F.map_distinguished Δ₁ h₁) h₂ e₂ e₃ h

private noncomputable def pullback_tensor_iso
    {C D : Type*} [Category C] [Category D]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (P : C ⥤ D) (I : D ⥤ C)
    (μ : (Functor.postcompose₂.obj P).obj TC ≅
      (((Functor.whiskeringLeft₂ _).obj P).obj P).obj TD)
    (Q QH : D) (N : C) (εQ : P.obj (I.obj Q) ≅ Q) (εQH : P.obj (I.obj QH) ≅ QH)
    (e : ((TC.obj (I.obj Q)).obj N) ≅ I.obj QH) :
    ((TD.obj Q).obj (P.obj N)) ≅ QH :=
  (TD.flip.obj (P.obj N)).mapIso εQ.symm ≪≫ ((μ.app (I.obj Q)).app N).symm ≪≫
    P.mapIso e ≪≫ εQH

private theorem tensor_unit_square
    {C D : Type*} [Category C] [Category D]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (e : L ≅ L')
    (hunit : ∀ V, adj'.unit.app V = adj.unit.app V ≫ R.map (e.hom.app V))
    (μ : (Functor.postcompose₂.obj L).obj TC ≅
      (((Functor.whiskeringLeft₂ _).obj L).obj L).obj TD)
    (K N : C) [IsIso (((adj.rightAdjointProjectionMap μ.hom).app (L.obj K)).app N)] :
    ∃ e₃ : (TC.flip.obj N).obj (R.obj (L'.obj K)) ≅
        R.obj (L'.obj ((TC.obj K).obj N)),
      (TC.flip.obj N).map (adj'.unit.app K) ≫ e₃.hom =
        adj'.unit.app ((TC.obj K).obj N) := by
  let F := TC.flip.obj N
  let H := (TC.obj K).obj N
  let e₃ : F.obj (R.obj (L'.obj K)) ≅ R.obj (L'.obj H) :=
    F.mapIso (R.mapIso (e.app K).symm) ≪≫
      asIso (((adj.rightAdjointProjectionMap μ.hom).app (L.obj K)).app N) ≪≫
      R.mapIso ((μ.app K).app N).symm ≪≫ R.mapIso (e.app H)
  have hcancel : F.map (adj'.unit.app K) ≫ F.map (R.map (e.inv.app K)) =
      F.map (adj.unit.app K) := by
    rw [← F.map_comp, hunit K, Category.assoc, ← R.map_comp,
      e.hom_inv_id_app, R.map_id]
    erw [Category.comp_id]
  have hprojection : F.map (adj.unit.app K) ≫
      (((adj.rightAdjointProjectionMap μ.hom).app (L.obj K)).app N) =
      adj.unit.app H ≫ R.map ((μ.hom.app K).app N) :=
    (Adjunction.unit_app_comp_map_rightAdjointProjectionMap adj μ.hom K N).symm
  refine ⟨e₃, ?_⟩
  dsimp only [e₃, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, asIso_hom]
  simp only [← Category.assoc]
  rw [hcancel, hprojection]
  simp only [Category.assoc, ← R.map_comp]
  have hμ : (μ.hom.app K).app N ≫ (μ.inv.app K).app N = 𝟙 _ :=
    ((μ.app K).app N).hom_inv_id
  rw [← Category.assoc, hμ]
  erw [Category.id_comp]
  exact (hunit H).symm

private noncomputable def closedSupportTensorLeft
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (K N : DerivedCategoryModule A T) : DerivedCategoryModule A Z :=
  ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K)).obj
      ((upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.obj N)

private noncomputable def closedSupportTensorRight
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (K N : DerivedCategoryModule A T) : DerivedCategoryModule A Z :=
  (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
    (((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj N)

private theorem closed_support_tensor_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K N : DerivedCategoryModule A T)
    [IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
      ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj K)).app N)] :
    Nonempty (closedSupportTensorLeft A i K N ≅ closedSupportTensorRight A i K N) := by
  unfold closedSupportTensorLeft closedSupportTensorRight
  let Ri : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A T :=
    R(lowerStar (ModuleCat.{u + 1} A) i)
  let Rj : DerivedCategoryModule A U ⥤ DerivedCategoryModule A T :=
    R(lowerStar (ModuleCat.{u + 1} A) j)
  let Li : DerivedCategoryModule A T ⥤ DerivedCategoryModule A Z :=
    (upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor
  let Lj : DerivedCategoryModule A T ⥤ DerivedCategoryModule A U :=
    (upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor
  let Dj : DerivedCategoryModule A T ⥤ DerivedCategoryModule A U :=
    (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j
  let H : DerivedCategoryModule A T := ((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj N
  let Q : DerivedCategoryModule A Z := Ri.rightAdjoint.obj K
  let QH : DerivedCategoryModule A Z := Ri.rightAdjoint.obj H
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j
  let adjD := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j
  have hunit (V : DerivedCategoryModule A T) :
      adjD.unit.app V = adj.unit.app V ≫ Rj.map (e.hom.app V) := by
    exact congrArg (fun d ↦ d.unit.app V)
      (mapDerivedUpperStarLowerStarAdjunction_eq (ModuleCat.{u + 1} A) j)
  let : IsIso (((adj.rightAdjointProjectionMap
      (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j).hom).app
        (Lj.obj K)).app N) := by
    rw [leftDerivedUpperStarTensorNatIso_hom]
    change IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
      ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj K)).app N)
    infer_instance
  obtain ⟨e₃, hsquare⟩ := tensor_unit_square
    (derivedTensor (ModuleCat.{u + 1} A) T)
    (derivedTensor (ModuleCat.{u + 1} A) U) adj adjD e hunit
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j) K N
  let F := (derivedTensor (ModuleCat.{u + 1} A) T).flip.obj N
  obtain ⟨δ, hδ⟩ := exists_etale_closedSupportTriangle A i j hij
  let TK := Triangle.mk ((Adjunction.ofIsLeftAdjoint Ri).counit.app K)
    (adjD.unit.app K) (δ.app K)
  let TH := Triangle.mk ((Adjunction.ofIsLeftAdjoint Ri).counit.app H)
    (adjD.unit.app H) (δ.app H)
  have hTK : TK ∈ distTriang _ := hδ K
  have hTH : TH ∈ distTriang _ := hδ H
  have he₁ : Nonempty (F.obj (Ri.obj Q) ≅ Ri.obj QH) :=
    nonempty_iso_of_mapped_distinguished_square F TK TH hTK hTH
      (Iso.refl H) e₃ (by
        change F.map (adjD.unit.app K) ≫ e₃.hom = 𝟙 H ≫ adjD.unit.app H
        simpa only [Category.id_comp] using hsquare)
  obtain ⟨e₁⟩ := he₁
  let ε (V : DerivedCategoryModule A Z) : Li.obj (Ri.obj V) ≅ V :=
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i).app (Ri.obj V) ≪≫
      asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app V)
  exact ⟨pullback_tensor_iso (derivedTensor (ModuleCat.{u + 1} A) T)
    (derivedTensor (ModuleCat.{u + 1} A) Z) Li Ri
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) i) Q QH N (ε Q) (ε QH) e₁⟩

/-- Tensoring the closed exceptional image by a finite constant module gives the
closed-support cohomology bound. No constructibility hypothesis is required.

Source: blueprint prop-exc-closed-tor, constant tensor and support-triangle paragraphs
(blueprint: lem-exc-closed-residue-bound).

Proof:
1. Test the Tor bound of K on the constant sheaf associated to N. Its tensor H has
   cohomology in [a,b], so the closed-support amplitude theorem bounds Ri!H.
2. Finite cohomological dimension gives countable coproduct preservation for Rj_*.
   The finite-constant projection formula therefore identifies the open terms of
   the tensor of the support triangle of K and the support triangle of H.
3. The projection-map unit identity makes the middle square commute. TR3 completes
   the square; the two-isomorphisms theorem identifies the first terms.
4. Apply monoidal closed pullback. The fully faithful closed direct-image counit
   and pullback of the constant N identify those first terms with Ri!K tensor N_Z
   and Ri!H. Transport the cohomology vanishing across this isomorphism. -/
theorem closedSupport_finiteTensor_vanishing
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ModuleCat.{u + 1} A) [Finite N]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (a b c : ℤ) (_hc : 0 ≤ c)
    (_hcd : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ), c < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (K : DerivedCategoryModule A T)
    (_hTor : DerivedCategory.hasTorAmplitudeIn A T a b K) :
    ∀ q : ℤ, q < a ∨ b + c + 1 < q → IsZero
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((derivedTensor (ModuleCat.{u + 1} A) Z).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)))) := by
  let Q : DerivedCategoryModule A Z := (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K
  let NT : DerivedCategoryModule A T := (_root_.DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)
  let H : DerivedCategoryModule A T := ((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj NT
  have hres := _hTor ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)
  have hH : _root_.DerivedCategory.homologyConcentratedIn a b H := by
    constructor
    · exact (_root_.DerivedCategory.isGE_iff H a).2 fun q hq ↦ hres q (Or.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff H b).2 fun q hq ↦ hres q (Or.inr hq)
  have hQH :=
    (closedImmersion_rightAdjoint_amplitude A i j _hij a b c _hc _hcd).1 H hH
  have hcdNat : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (p : ℕ),
      c.toNat < p → IsZero (((lowerStar (ModuleCat.{u + 1} A) j).rightDerived p).obj M) := by
    intro M p hp
    exact (_hcd M p (by omega)).of_iso
      ((lowerStar (ModuleCat.{u + 1} A) j).homologyRightDerivedFunctorObjSingleFunctorIso M p).symm
  let : PreservesColimitsOfShape (Discrete ℕ)
      (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor :=
    rightDerivedLowerStar_preservesCoproducts_of_finite_dimension A j c.toNat hcdNat ℕ
  let Lj : DerivedCategoryModule A T ⥤ DerivedCategoryModule A U :=
    (upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor
  let : IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
      ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj K)).app NT) :=
    isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts A j
      ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj K) N
  obtain ⟨e⟩ := closed_support_tensor_comparison A i j _hij K NT
  let NZ : DerivedCategoryModule A Z := (_root_.DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)
  let eN : (upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.obj NT ≅ NZ :=
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) i).app
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N) ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app N)
  let eQ : ((derivedTensor (ModuleCat.{u + 1} A) Z).obj Q).obj NZ ≅
      (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj H :=
    ((derivedTensor (ModuleCat.{u + 1} A) Z).obj Q).mapIso eN.symm ≪≫
      e
  intro q hq
  have hzero : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj H)) := by
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff _ a).1 hQH.1 q hq
    · exact (_root_.DerivedCategory.isLE_iff _ (b + c + 1)).1 hQH.2 q hq
  exact hzero.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso eQ)

end AlgebraicGeometry.Etale
