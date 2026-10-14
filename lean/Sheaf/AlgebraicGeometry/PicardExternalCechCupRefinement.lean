/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
public import Sheaf.Paper.CechRefinementCochainMap

/-! # Comparison of external cup coordinates with refinement and ordinary cup
Source: Stacks Project, Tags 01FD, 07MB and 0BED.
-/

@[expose] public section
universe w
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k]

/-- The additive Cech comparison for restriction of scalars.
Source: the explicit Cech identification, Stacks Tag 01FD.
(blueprint: lem-sc-picard-external-cech-cup-refinement). -/
def externalCupScalarCechIso {Z : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    {μ : Type w} (A : μ → Z.Opens) (M : Z.Modules) :
    ((forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}).mapHomologicalComplex _).obj
        ((picardCechFunctor t A).obj M) ≅
      ((forget₂ (ModuleCat.{w} Γ(Z, ⊤)) AddCommGrpCat.{w}).mapHomologicalComplex _).obj
        ((cechComplexFunctor A).obj M.presheafModuleCat) :=
  TopCat.Presheaf.cechComplexFunctorIso A (scalarPresheaf t M) ≪≫
    (TopCat.Presheaf.cechComplexFunctorIso A M.presheafModuleCat).symm

/-- The unique refinement map specified by its pullback and restriction coordinates.
Its specification determines every degree component uniquely.
Source: Stacks Tag 01FD.
(blueprint: lem-sc-picard-external-cech-cup-refinement). -/
def externalCupRefineCech {Z T : Scheme.{w}} (a : T ⟶ Z)
    {μ ν : Type w} (A : μ → Z.Opens) (B : ν → T.Opens)
    (r : ν → μ) (hr : ∀ j, B j ≤ a ⁻¹ᵁ A (r j)) (M : Z.Modules) :=
  (exists_unique_cechRefinementMap a A B r hr M).exists.choose

private lemma externalCupScalarCechIso_apply {Z : Scheme.{w}}
    (t : Z ⟶ Spec (CommRingCat.of k)) {μ : Type w} (A : μ → Z.Opens)
    (M : Z.Modules) (n : ℕ) (z : ((picardCechFunctor t A).obj M).X n) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv A M.presheafModuleCat n
      ((externalCupScalarCechIso t A M).hom.f n z) =
      TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) n z := by
  exact (TopCat.Presheaf.cechComplexFunctorXAddEquiv
    A M.presheafModuleCat n).apply_symm_apply _

private lemma externalCupRefineCech_apply {Z T : Scheme.{w}} (a : T ⟶ Z)
    {μ ν : Type w} (A : μ → Z.Opens) (B : ν → T.Opens)
    (r : ν → μ) (hr : ∀ j, B j ≤ a ⁻¹ᵁ A (r j)) (M : Z.Modules)
    (n : ℕ) (z : ((cechComplexFunctor A).obj M.presheafModuleCat).X n)
    (y : Fin (n + 1) → ν) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv B
        ((tensorPullback a).obj M).presheafModuleCat n
        ((externalCupRefineCech a A B r hr M).f n z) y =
      ((tensorPullback a).obj M).presheaf.map
        (cechRefinementIntersection a A B r hr n y).op
        (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app
          (op (⨅ j, A (r (y j))))
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv A M.presheafModuleCat n z
            (r ∘ y))) :=
  (exists_unique_cechRefinementMap a A B r hr M).exists.choose_spec n z y

attribute [local irreducible] externalCupRefineCech externalCupScalarCechIso
  tensorPullback tensorPullbackObj
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

set_option maxHeartbeats 800000 in
-- Comparing restrictions in the scalar and module Cech products needs extra elaboration.
/-- External bidegree coordinates are the ordinary cup of the refined factor cochains.
Source: Stacks Tag 01FD (refinement coordinates), Tag 07MB (Alexander--Whitney formula),
and Tag 0BED (equation-kunneth-on-cech).
(blueprint: lem-sc-picard-external-cech-cup-refinement).
Proof: Apply the target additive Cech coordinate equivalence. The scalar comparison is
identity on explicit section coordinates. Expand the prescribed external bidegree formula
and the ordinary cup formula. The unique refinement maps have the normalized pullback-unit
coordinates of Tag 01FD. On each front and back tuple, the cup restriction composed with
the refinement restriction equals the direct restriction to the full product intersection:
Functor.map_comp gives composition and the category of opens is thin. Thus both factors
of the tensor section agree. Coordinate injectivity proves the equality. This argument has
no differential assumption and works in degree zero, for repeated indices, empty families,
zero coefficients, and every characteristic. -/
theorem externalCup_bidegree_refinement
    {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (p q : ℕ)
    (h : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hh : IsPicardExternalCechCupBidegree f g U V F G p q h)
    (a : ((picardCechFunctor f U).obj F).X p)
    (b : ((picardCechFunctor g V).obj G).X q) :
    (externalCupScalarCechIso (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G)).hom.f (p + q)
        (h (a ⊗ₜ[k] b)) =
      cechCupCochain
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)
        ((tensorPullback (pullback.fst f g)).obj F)
        ((tensorPullback (pullback.snd f g)).obj G) p q
        ((externalCupRefineCech (pullback.fst f g) U _ Prod.fst
          (fun _ ↦ inf_le_left) F).f p ((externalCupScalarCechIso f U F).hom.f p a))
        ((externalCupRefineCech (pullback.snd f g) V _ Prod.snd
          (fun _ ↦ inf_le_right) G).f q ((externalCupScalarCechIso g V G).hom.f q b))  := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
    (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2)
    (externalCupCoefficients f g F G).presheafModuleCat (p + q)).injective
  rw [externalCupScalarCechIso_apply]
  funext y
  rw [hh a b y]
  simp only [cechCupCochain, AddEquiv.apply_symm_apply]
  apply congrArg₂ tmulSection
  · rw [externalCupRefineCech_apply, externalCupScalarCechIso_apply]
    symm
    exact TopCat.Presheaf.map_homOfLE_map_homOfLE_apply
      ((tensorPullback (pullback.fst f g)).obj F).presheaf _ _ _
  · rw [externalCupRefineCech_apply, externalCupScalarCechIso_apply]
    symm
    exact TopCat.Presheaf.map_homOfLE_map_homOfLE_apply
      ((tensorPullback (pullback.snd f g)).obj G).presheaf _ _ _

end
end AlgebraicGeometry.Scheme.Modules
