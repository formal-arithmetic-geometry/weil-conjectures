/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.SixFunctors.IntegralLisseReductionConstruction
import Sheaf.SixFunctors.IntegralLisseReductionComplete
public import Sheaf.SixFunctors.IntegralLisseReductionScalarDescent
import Sheaf.SixFunctors.IntegralLisseCoefficientQuotients
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Finite locally free quotient towers

Source: Bhatt--Scholze, Proposition 6.8.4(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private def freeCokernelIso (I : Type (u + 1)) [Finite I] (n : ℕ) :
    (integralLisseFiniteRestriction l E X n).obj (SheafOfModules.free I) ≅
      integralLisseCokernel l E X (SheafOfModules.free I) n := by
  classical
  let S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (integralLisseFiniteRing l E X n)
  let res := integralLisseFiniteRestriction l E X n
  have : res.Additive := by
    dsimp [res, integralLisseFiniteRestriction]
    infer_instance
  let Q := integralLisseCokernelFunctor l E X ⋙ (evaluation ℕᵒᵖ _).obj (op n)
  let U := SheafOfModules.unit (integralLisseRing l E X)
  let p := integralLisseRingMap l E X
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralLisseReduction l E X n))
  let e : Q.obj U ≅ res.obj (SheafOfModules.unit S) :=
    have := isIso_integralLisseQuotient_desc l E X _ p
      (integralLisseCoefficient_quotients l E X n)
    asIso (cokernel.desc _ p (integralLisseCoefficient_quotients l E X n).choose)
  exact PreservesCoproduct.iso res (fun _ : I ↦ SheafOfModules.unit S) ≪≫
    Sigma.mapIso (fun _ : I ↦ e.symm) ≪≫
    (PreservesCoproduct.iso Q (fun _ : I ↦ U)).symm

private def localCokernelIso (U : X.ProEt)
    (M N : ringedSiteModules.{u + 1} (integralLisseRing l E X))
    (e : M.over U ≅ N.over U) (n : ℕ) :
    (integralLisseCokernel l E X M n).over U ≅
      (integralLisseCokernel l E X N n).over U := by
  let F := SheafOfModules.overFunctor.{u + 1} (integralLisseRing l E X) U
  have := (ringedOverFunctor_exactGeneral (integralLisseRing l E X) U).2.2
  let a := fun P ↦ integralLisseScalar l E X P
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
  exact PreservesCokernel.iso F (a M) ≪≫
    cokernel.mapIso _ (F.map (a N)) e e (by
      ext V x
      exact (e.hom.val.app V).hom.map_smul _ x) ≪≫
    (PreservesCokernel.iso F (a N)).symm

/-- Each scalar cokernel of a finite locally free integral module is finite locally free
for its actual finite coefficient action.
Source: Bhatt--Scholze, Proposition 6.8.4(1)
(blueprint: lem-sfb-integral-lisse-cokernel-complete).
Proof: trivialize the original module. Restriction to slices preserves cokernels;
finite sums preserve the coefficient quotient calculation. The resulting local
isomorphisms are finite-coefficient linear because the coefficient reduction is
surjective on sections. The resulting finite free charts prove local freeness. -/
theorem integralLisseFiniteCokernel_isFiniteLocallyFree
    (M : IntegralLisseModule l E X) (n : ℕ) :
    (integralLisseFiniteCokernel l E X M.obj n).IsFiniteLocallyFree := by
  have hM : M.obj.IsFiniteLocallyFree := M.property
  obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
  let S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (integralLisseFiniteRing l E X n)
  let ρ := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (integralLisseReduction l E X n)
  let κ (i : q.I) := (q.generators i).I
  have (i : q.I) : Finite (κ i) := by
    have := hf.isFiniteType i
    exact inferInstanceAs (Finite (q.generators i).I)
  apply SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free
    q.X q.coversTop κ
  intro i
  have := hf.isFiniteType i
  have := hq.isIso i
  let F := SheafOfModules.overFunctor.{u + 1} (integralLisseRing l E X) (q.X i)
  let G := SheafOfModules.overFunctor.{u + 1} S (q.X i)
  have := (ringedOverFunctor_exactGeneral (integralLisseRing l E X) (q.X i)).1
  have := (ringedOverFunctor_exactGeneral S (q.X i)).1
  let e : M.obj.over (q.X i) ≅
      (SheafOfModules.free (R := integralLisseRing l E X) (κ i)).over (q.X i) :=
    (asIso (q.generators i).π).symm ≪≫ SheafOfModules.mapFreeIso F _ (Iso.refl _)
  let ρU := ((Scheme.ProEt.topology X).overPullback RingCat.{u + 1} (q.X i)).map ρ
  let resU := SheafOfModules.restrictScalars.{u + 1} ρU
  let hsurj := fun V : (Over (q.X i))ᵒᵖ ↦
    integralLisseReduction_surjective l E X n (op V.unop.left)
  let c : resU.obj ((integralLisseFiniteCokernel l E X M.obj n).over (q.X i)) ≅
      resU.obj (SheafOfModules.free (κ i)) :=
    F.mapIso (integralLisseFiniteCokernelIso l E X M.obj n) ≪≫
      localCokernelIso l E X (q.X i) _ _ e n ≪≫
      (F.mapIso (freeCokernelIso l E X (κ i) n)).symm ≪≫
      resU.mapIso (PreservesCoproduct.iso G (fun _ : κ i ↦ SheafOfModules.unit S))
  exact ⟨(SheafOfModules.ScalarDescent.fullyFaithful ρU hsurj).preimageIso c⟩

/-- Reduction of a finite locally free integral module is a normalized tower, and
its canonical quotient cone is limiting.
Source: Bhatt--Scholze, Proposition 6.8.4(1), p. 59
(blueprint: lem-sfb-integral-lisse-cokernel-complete).
Proof: use the descended finite-coefficient action and its finite free local charts
for each level. Adjacent transitions are scalar cokernels by their universal
properties. The coefficient limit, finite direct sums and descent prove completeness. -/
theorem integralLisseCokernel_complete (M : IntegralLisseModule l E X) :
    IsIntegralReductionTower l E X (integralLisseCokernelTower l E X M.obj) ∧
      Nonempty (IsLimit (Cone.mk M.obj (integralLisseCokernelCone l E X M.obj))) := by
  refine ⟨⟨?_, ?_⟩, integralLisseCokernel_isLimit l E X M⟩
  · intro n
    exact ⟨integralLisseFiniteCokernel l E X M.obj n,
      integralLisseFiniteCokernel_isFiniteLocallyFree l E X M n,
      ⟨integralLisseFiniteCokernelIso l E X M.obj n⟩⟩
  · intro n
    simpa only [integralLisseCokernelTower, Functor.ofOpSequence_map_homOfLE_succ] using
      integralLisseCokernelTransition_quotient l E X M.obj n

end AlgebraicGeometry.ProEtale
