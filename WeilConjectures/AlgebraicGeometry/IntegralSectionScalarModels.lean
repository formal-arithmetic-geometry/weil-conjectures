/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels
import all WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import all WeilConjectures.AlgebraicGeometry.IntegralSectionRegularScalars
import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.CategoryTheory.MapModScalarExtension
public import WeilConjectures.SixFunctors.ContinuousScalarFinitePresentation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison

/-! # Scalar realization under the integral section comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage Scheme.integralConstantModule

section FinitePresentationComparison
universe v w
variable {A : Type u} [CommRing A] {C : Type v} [Category.{w} C] [Abelian C]
  (F G : ModuleCat.{u + 1} A ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteColimits F] [PreservesFiniteColimits G]

private abbrev scalarRegular (A : Type u) [CommRing A] : ModuleCat.{u + 1} A :=
  ModuleCat.of A (ULift.{u + 1} A)

private def scalarBiproductIso (n : ℕ) :
    FiniteConstantModel.freeScalars A n ≅
      ⨁ (fun _ : Fin n ↦ scalarRegular A) :=
  (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ scalarRegular A)).symm

private def scalarFreeComparison (e : F.obj (scalarRegular A) ≅ G.obj (scalarRegular A))
    (n : ℕ) : F.obj (FiniteConstantModel.freeScalars A n) ≅
      G.obj (FiniteConstantModel.freeScalars A n) :=
  F.mapIso (scalarBiproductIso n) ≪≫ F.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ : Fin n ↦ e) ≪≫
    (G.mapBiproduct _).symm ≪≫ (G.mapIso (scalarBiproductIso n)).symm

omit [PreservesFiniteColimits G] in
private theorem scalarFreeComparison_natural
    (e : F.obj (scalarRegular A) ≅ G.obj (scalarRegular A))
    (he : ∀ f : scalarRegular A ⟶ scalarRegular A,
      F.map f ≫ e.hom = e.hom ≫ G.map f)
    (m n : ℕ) (f : FiniteConstantModel.freeScalars A m ⟶
      FiniteConstantModel.freeScalars A n) :
    F.map f ≫ (scalarFreeComparison F G e n).hom =
      (scalarFreeComparison F G e m).hom ≫ G.map f := by
  let f' := (scalarBiproductIso m).inv ≫ f ≫ (scalarBiproductIso n).hom
  have h : (F.mapBiproduct (fun _ : Fin m ↦ scalarRegular A)).inv ≫ F.map f' ≫
      (F.mapBiproduct (fun _ : Fin n ↦ scalarRegular A)).hom ≫
        (biproduct.mapIso (fun _ : Fin n ↦ e)).hom =
      (biproduct.mapIso (fun _ : Fin m ↦ e)).hom ≫
        (G.mapBiproduct (fun _ : Fin m ↦ scalarRegular A)).inv ≫ G.map f' ≫
          (G.mapBiproduct (fun _ : Fin n ↦ scalarRegular A)).hom := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    simp only [Category.assoc, biproduct.mapIso_hom, biproduct.map_π,
      biproduct.ι_map_assoc, Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
      biproduct.ι_desc_assoc, biproduct.lift_π, biproduct.lift_π_assoc]
    simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc] using
      he (biproduct.ι (fun _ : Fin m ↦ scalarRegular A) j ≫ f' ≫
        biproduct.π (fun _ : Fin n ↦ scalarRegular A) k)
  apply (cancel_epi (F.map (scalarBiproductIso m).inv)).mp
  apply (cancel_epi (F.mapBiproduct (fun _ : Fin m ↦ scalarRegular A)).inv).mp
  apply (cancel_mono (G.map (scalarBiproductIso n).hom)).mp
  apply (cancel_mono (G.mapBiproduct (fun _ : Fin n ↦ scalarRegular A)).hom).mp
  simp only [scalarFreeComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [F.map_id, G.map_id]
  simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id, Iso.inv_hom_id_assoc]
  exact h

private theorem scalarPresentationComparison
    (e : F.obj (scalarRegular A) ≅ G.obj (scalarRegular A))
    (he : ∀ f : scalarRegular A ⟶ scalarRegular A,
      F.map f ≫ e.hom = e.hom ≫ G.map f)
    (N : ModuleCat.{u + 1} A) (hN : Module.FinitePresentation A N) :
    Nonempty (F.obj N ≅ G.obj N) := by
  have := hN
  obtain ⟨m, n, f, ⟨en⟩⟩ := ContinuousScalarPresentation.ordinary_presentation A N
  exact ⟨F.mapIso en ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) (G.map f)
      (scalarFreeComparison F G e m) (scalarFreeComparison F G e n)
      (scalarFreeComparison_natural F G e he m n f) ≪≫
    (PreservesCokernel.iso G f).symm ≪≫ (G.mapIso en).symm⟩

end FinitePresentationComparison

/-- Pulling a continuous scalar extension from the condensed point to a scheme agrees
with extending the pulled-back discrete constant module along the pulled-back scalar map.
In particular this realizes every finitely presented integral scalar module by the
current coefficient ring `A_X = p_X^* A`, including torsion and the zero module.

Source: latest blueprint, the integral paragraph of `lem-sfb-dc-lower-star-preserves`
through `sk-prop-integral-criterion` and `sk-lem-integral-models` (1)--(2); the scalar
realization in Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).
(blueprint: lem-sfb-integral-section-scalar-models).

Proof: lift the monoidal adjunction for inverse image from the point to module objects
for the discrete constant ring and the continuous ring. Restriction of scalars commutes
with its right adjoint by the unit naturality square. Uniqueness of left adjoints gives
`mapModExtendScalarsIso`. Evaluate it on the sheafified ordinary scalar module. This
works for arbitrary scalar modules, so no finite presentation or nonzero-rank hypothesis
is needed. No completion representative or choice of an adic model is used. -/
theorem integralSectionScalarModels (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (N : ModuleCat.{u + 1} A) :
    Nonempty (((upperStarFromPoint X).mapMod
      (Profinite.continuousCoefficientRingObj A)).obj ((continuousScalarFunctor A).obj N) ≅
      (Mod.extendScalars ((upperStarFromPoint X).map
        (FiniteConstantModel.scalarToContinuous A))).obj
        (((upperStarFromPoint X).mapMod
          ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} A)))).obj
          (((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
            (AddCommGrpCat.of (ULift.{u + 1} A))).obj
              ((FiniteConstantModel.scalarModules A).obj N)))) := by
  let F := upperStarFromPoint X
  let : F.Braided :=
    { toMonoidal := inferInstance
      braided := Functor.LaxBraided.braided }
  let adj := upperStarFromPointAdjunction X
  let := adj.rightAdjointLaxMonoidal
  let : adj.IsMonoidal := by
    constructor
    · rfl
    · intro X Y; rfl
  let e := Functor.mapModExtendScalarsIso _ _ adj
    (FiniteConstantModel.scalarToContinuous A)
  exact ⟨e.app _⟩

end AlgebraicGeometry.ProEtale
