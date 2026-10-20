/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module
public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
public import Sheaf.Paper.CechRefinementCochainMap

/-! # Transport of the external Cech pairing to the ordinary module cup

Source: Stacks Project, Tags 01FD, 07MB and 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cech-cup-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
/-- Identify the scalar and ordinary module Cech complexes after forgetting scalars.
Their section presheaves have the same underlying additive groups.
Source: Stacks Project, Tag 01FD.
(blueprint: lem-sc-picard-external-cech-cup-transport). -/
def picardCechScalarIso {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens) (F : X.Modules) :=
  (TopCat.Presheaf.cechComplexFunctorIso U (scalarPresheaf f F)) ≪≫
    (TopCat.Presheaf.cechComplexFunctorIso U F.presheafModuleCat).symm

/-- The scalar identification preserves each tuple coordinate. -/
theorem picardCechScalarIso_apply {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens) (F : X.Modules)
    (n : ℕ) (a : ((picardCechFunctor f U).obj F).X n) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n
      ((picardCechScalarIso f U F).hom.f n a) =
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) n a := by
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n
    ((TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n).symm
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) n a)) = _
  exact AddEquiv.apply_symm_apply _ _

private theorem restriction_comp {X : Scheme.{w}}
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w}) {V W Z : X.Opensᵒᵖ}
    (i : V ⟶ W) (j : W ⟶ Z) (k : V ⟶ Z) (a : P.obj V) :
    P.map j (P.map i a) = P.map k a := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  congr 2

set_option maxHeartbeats 800000 in
-- Elaborating the coordinate transports requires additional heartbeats.
/-- An external bidegree pairing becomes the ordinary cup of the refined cochains.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech, and Tags 01FD and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-transport).

Proof: Apply the injective ordinary Cech coordinate equivalence. The scalar
identification preserves the coordinates. Use the given external bidegree
formula, then expand the ordinary cup and the two refinement formulas. Each
refinement pulls the appropriate front or back section by the pullback
adjunction unit and restricts it to the smaller product intersection. Composing
this restriction with the cup restriction agrees with the single restriction
in the external formula, by presheaf functoriality and uniqueness of morphisms
between opens. The tensor sections and hence every coordinate agree.
This works for arbitrary cochains, including degree zero, empty index families,
zero coefficients and characteristic two; there is no covering hypothesis. -/
theorem picardExternalCechCupBidegree_transport
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (p q : ℕ)
    (h : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hh : IsPicardExternalCechCupBidegree f g U V F G p q h)
    (hrefineF : ∀ ij : ι × κ,
      (pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2) ≤
        pullback.fst f g ⁻¹ᵁ U ij.1)
    (hrefineG : ∀ ij : ι × κ,
      (pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2) ≤
        pullback.snd f g ⁻¹ᵁ V ij.2)
    (gammaF : ((forget₂ (ModuleCat.{w} Γ(X, ⊤)) AddCommGrpCat.{w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{w} Γ(Limits.pullback f g, ⊤))
        AddCommGrpCat.{w}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexFunctor (fun ij : ι × κ ↦
          pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          ((tensorPullback (pullback.fst f g)).obj F).presheafModuleCat))
    (hgammaF : IsCechRefinementMap (pullback.fst f g) U
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) Prod.fst hrefineF F gammaF)
    (gammaG : ((forget₂ (ModuleCat.{w} Γ(Y, ⊤)) AddCommGrpCat.{w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor V).obj G.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{w} Γ(Limits.pullback f g, ⊤))
        AddCommGrpCat.{w}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexFunctor (fun ij : ι × κ ↦
          pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          ((tensorPullback (pullback.snd f g)).obj G).presheafModuleCat))
    (hgammaG : IsCechRefinementMap (pullback.snd f g) V
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) Prod.snd hrefineG G gammaG) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let W := fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2
    let E := externalCupCoefficients f g F G
    ∀ (a : A.X p) (b : B.X q),
      (picardCechScalarIso (pullback.fst f g ≫ f) W E).hom.f (p + q)
        (h (a ⊗ₜ[k] b)) =
      cechCupCochain W ((tensorPullback (pullback.fst f g)).obj F)
        ((tensorPullback (pullback.snd f g)).obj G) p q
        (gammaF.f p ((picardCechScalarIso f U F).hom.f p a))
        (gammaG.f q ((picardCechScalarIso g V G).hom.f q b)) := by
  classical
  intro A B W E a b
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv W E.presheafModuleCat (p + q)).injective
  rw [picardCechScalarIso_apply]
  funext y
  rw [hh]
  unfold cechCupCochain
  rw [AddEquiv.apply_symm_apply, hgammaF, hgammaG]
  rw [picardCechScalarIso_apply, picardCechScalarIso_apply]
  congr 1
  · exact (restriction_comp ((tensorPullback (pullback.fst f g)).obj F).presheaf
      _ _ _ _).symm
  · exact (restriction_comp ((tensorPullback (pullback.snd f g)).obj G).presheaf
      _ _ _ _).symm

/-- The scalar identification commutes with the differential. -/
theorem picardCechScalarIso_d {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens) (F : X.Modules)
    (n : ℕ) (a : ((picardCechFunctor f U).obj F).X n) :
    (picardCechScalarIso f U F).hom.f (n + 1)
      (((picardCechFunctor f U).obj F).d n (n + 1) a) =
    ((cechComplexFunctor U).obj F.presheafModuleCat).d n (n + 1)
      ((picardCechScalarIso f U F).hom.f n a) := by
  exact (ConcreteCategory.congr_hom ((picardCechScalarIso f U F).hom.comm n (n + 1)) a).symm

/-- The scalar identification commutes with transport between equal degrees. -/
theorem picardCechScalarIso_cast {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens) (F : X.Modules)
    {m n : ℕ} (hmn : m = n) (a : ((picardCechFunctor f U).obj F).X m) :
    (picardCechScalarIso f U F).hom.f n
      (eqToHom (congrArg (fun j ↦ ((picardCechFunctor f U).obj F).X j) hmn) a) =
    eqToHom (congrArg (fun j ↦ ((cechComplexFunctor U).obj F.presheafModuleCat).X j) hmn)
      ((picardCechScalarIso f U F).hom.f m a) := by
  subst n
  rfl

end
end AlgebraicGeometry.Scheme.Modules
