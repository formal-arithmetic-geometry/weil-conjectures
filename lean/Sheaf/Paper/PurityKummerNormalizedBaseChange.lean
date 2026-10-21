/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.PurityFiniteKummerDefinitions
import Sheaf.Paper.PurityKummerRootTensorBaseChange
import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso

/-! # Base change for the normalized finite Kummer projection

Source: finite Kummer-level blueprint, proof steps 9--11; Stacks Tag 03PK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

private theorem constantDirectMap_naturality {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) :
    tateConstantMap T φ ≫ proEtaleCoefficientDirectImageMap h A =
      proEtaleCoefficientDirectImageMap h R ≫
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map (tateConstantMap T' φ) := by
  apply ((sheafificationAdjunction (ProEt.topology T)
    CommRingCat.{u + 1}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change toSheafify _ _ ≫ (tateConstantMap T φ).hom ≫
    (proEtaleCoefficientDirectImageMap h A).hom =
      toSheafify _ _ ≫ (proEtaleCoefficientDirectImageMap h R).hom ≫ _
  change toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} R))) ≫
      sheafifyMap (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).map
      (CommRingCat.ofHom (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
        (φ.comp ULift.ringEquiv.{u, u + 1}.toRingHom)))) ≫ _ = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  have hr (B : Type u) [CommRing B] :
      toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} B))) ≫
          (proEtaleCoefficientDirectImageMap h B).hom =
        Functor.whiskerLeft (proEtaleBaseChange h).op
          (toSheafify (ProEt.topology T') ((Functor.const T'.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} B)))) :=
    ((sheafificationAdjunction (ProEt.topology T)
      CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  rw [hr A, ← Category.assoc, hr R]
  let f : (Functor.const T'.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} R)) ⟶
      (Functor.const T'.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)) :=
    (Functor.const T'.ProEtᵒᵖ).map
      (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).symm.toRingHom.comp
        (φ.comp (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom)))
  have hn := toSheafify_naturality (ProEt.topology T') f
  exact congrArg (fun t ↦ Functor.whiskerLeft (proEtaleBaseChange h).op t) hn


private theorem root_limit_base_change (l : ℕ) [Fact l.Prime]
    {T T' : Scheme.{u}} (f : T' ⟶ T) :
    ∃ c : Scheme.purTwistZlOne T l ⟶
        (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
          (Scheme.purTwistZlOne T' l),
      (∀ r : ℕ,
        c ≫ (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
            (limit.π (Scheme.proEtaleRootsOfUnityTower T' l
              (Fact.out : l.Prime)) (op r)) =
          limit.π (Scheme.proEtaleRootsOfUnityTower T l
            (Fact.out : l.Prime)) (op r) ≫
              Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (r + 1))) := by
  let F := proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)
  let F' := proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)
  let L := proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}
  let G := proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}
  let adj := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  obtain ⟨γ, hγ⟩ := (proEtaleRootsOfUnityInverseImageIso f).2.1 l (Fact.out : l.Prime)
  let C : Cone F' :=
    { pt := L.obj (limit F)
      π :=
        { app := fun r ↦ L.map (limit.π F r) ≫ γ.app r
          naturality := by
            intro i j g
            dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
            rw [Category.id_comp, Category.assoc, ← γ.naturality g]
            change L.map (limit.π F j) ≫ γ.app j =
              L.map (limit.π F i) ≫ L.map (F.map g) ≫ γ.app j
            rw [← Category.assoc, ← L.map_comp, limit.w] } }
  let d : L.obj (limit F) ⟶ limit F' := limit.lift F' C
  refine ⟨(adj.homEquiv _ _) d, ?_⟩
  intro r
  change (adj.homEquiv _ _) d ≫ G.map (limit.π F' (op r)) = _
  rw [← adj.homEquiv_naturality_right]
  change (adj.homEquiv _ _) (limit.lift F' C ≫ limit.π F' (op r)) = _
  rw [limit.lift_π]
  change (adj.homEquiv _ _) (L.map (limit.π F (op r)) ≫ γ.app (op r)) = _
  rw [adj.homEquiv_naturality_left, hγ]
  congr 1
  exact (adj.homEquiv _ _).apply_symm_apply _

/-- Normalized projection comparisons commute with arbitrary scheme base change.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md, steps 9--11;
Stacks Tags 03PK, 040M and 03EL.
(blueprint: lem-pur-kummer-normalized-base-change)

Proof: the existing root inverse-image maps form a natural tower map. Compose
its coordinates with inverse image of each source limit projection, and use the
target limit property to obtain a map from inverse image of the source root
limit. Its adjunct is c. Adjunction naturality and the limit projection equations
give every coordinate identity for c. Take the normalized finite-root tensor
isomorphism delta of lem-pur-kummer-root-tensor-base-change. Define beta as
pullback(alpha_T), followed by delta, followed by the inverse of alpha_T'. This
is a composite of isomorphisms and gives the square. Apply alpha_T' to the source
normalization equation, use naturality of the module adjunction unit, and use the
normalization formulas for alpha_T, delta and alpha_T'. Naturality of the constant
quotient-ring map and the N-th coordinate equation for c identify both resulting
tensors. The sectionwise injectivity of alpha_T' proves the source equation.
Empty bases need no exception, and inverse image need not preserve a limit. -/
theorem kummer_normalized_base_change (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n)
    (α : ∀ (T : Scheme.{u})
      (_hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
      P.kummerLine n T ≅ P.kummerRootsTensor n N a T)
    (hα : ∀ (T : Scheme.{u})
      (hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
      P.IsKummerComparison n N a T (α T hT)) :
    P.KummerBaseChangeCompatible n N a α  := by
  intro T T' f hT hT'
  obtain ⟨c, hc⟩ := root_limit_base_change P.coefficients.l f
  obtain ⟨δ, hδ⟩ := kummer_root_tensor_base_change P n N a T T' f hT hT'
  let β := ((tatePullback f (P.kummerCoefficient n)).mapIso (α T hT)) ≪≫
    δ ≪≫ (α T' hT').symm
  have hsquare : (tatePullback f (P.kummerCoefficient n)).map (α T hT).hom ≫
      δ.hom = β.hom ≫ (α T' hT').hom := by
    dsimp only [β, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨c, hc, β, δ, ?_, hδ, hsquare⟩
  intro U z b x
  let V := (proEtaleBaseChange f).obj U
  let e := (SheafOfModules.evaluation _ (op V)).mapIso (α T' hT')
  apply (ModuleCat.mono_iff_injective e.hom).mp (by infer_instance)
  change (α T' hT').hom.val.app (op V) _ = (α T' hT').hom.val.app (op V) _
  have hsq := congrArg (fun k ↦ k.val.app (op V)
    (tateUnit f (P.kummerCoefficient n) (P.kummerLine n T) U
      (P.kummerSourceTensor n T U z b x))) hsquare
  change δ.hom.val.app (op V)
    (((tatePullback f (P.kummerCoefficient n)).map (α T hT).hom).val.app (op V)
      (tateUnit f (P.kummerCoefficient n) (P.kummerLine n T) U
        (P.kummerSourceTensor n T U z b x))) =
      (α T' hT').hom.val.app (op V) (β.hom.val.app (op V)
        (tateUnit f (P.kummerCoefficient n) (P.kummerLine n T) U
          (P.kummerSourceTensor n T U z b x))) at hsq
  rw [← hsq]
  have hu := (proEtaleRingModuleAdjunction f
    (proEtaleConstantRing T (P.kummerCoefficient n))
    (proEtaleConstantRing T' (P.kummerCoefficient n))
    (asIso (proEtaleCoefficientInverseImageMap f (P.kummerCoefficient n)))).unit.naturality
      (α T hT).hom
  have huv := congrArg (fun k ↦ k.val.app (op U)
    (P.kummerSourceTensor n T U z b x)) hu
  change tateUnit f (P.kummerCoefficient n) (P.kummerRootsTensor n N a T) U
    ((α T hT).hom.val.app (op U) (P.kummerSourceTensor n T U z b x)) =
      (((tatePullback f (P.kummerCoefficient n)).map (α T hT).hom).val.app (op V))
        (tateUnit f (P.kummerCoefficient n) (P.kummerLine n T) U
          (P.kummerSourceTensor n T U z b x)) at huv
  rw [← huv, hα T hT, hδ, hα T' hT']
  have hr := congrArg (fun k ↦ k.hom.app (op U) b)
    (constantDirectMap_naturality f
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal
        P.coefficients.l P.extension (n + 1))))
  have hcN := congrArg (fun k ↦ k.hom.app (op U) x) (hc N)
  have hz : tateRingUnit f (P.kummerCoefficient n) U
      (z * (purTwistIntegralQuotient T P.coefficients.l P.extension n).hom.app (op U) b) =
      (show (P.kummerRingSheaf n T').obj.obj (op V) from
        tateRingUnit f (P.kummerCoefficient n) U z) *
        (purTwistIntegralQuotient T' P.coefficients.l P.extension n).hom.app (op V)
          (tateRingUnit f (Padic.coefficientExtensionIntegers
            P.coefficients.l P.extension) U b) := by
    dsimp only [tateRingUnit]
    rw [map_mul]
    exact congrArg (_ * ·) hr
  rw [hz]
  exact congrArg (P.kummerTargetTensor n N a T' V
    ((show (P.kummerRingSheaf n T').obj.obj (op V) from
        tateRingUnit f (P.kummerCoefficient n) U z) *
      (purTwistIntegralQuotient T' P.coefficients.l P.extension n).hom.app (op V)
        (tateRingUnit f (Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension) U b))) hcN.symm

end WeilConjectures.PurityFiniteSetting
