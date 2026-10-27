/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Quotient and kernel support for successive module strict transforms

Source: Stacks Project, Divisors, Tag 080I, proof paragraph 1 and the first three
sentences of paragraph 2; Tag 080D (1)
(blueprint: lem-trf-iterated-transform-quotient-support).

The second fibre product is represented as `(X ×[S] S₁) ×[S₁] S₂`.
Existentially binding the quasi-coherence proof of the first transform allows the
second transform to be formed without adding a quasi-coherence hypothesis.
The map `α` is fixed by equality to the composite of the defining quotients.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem restrict_map_iso_of_le {X : Scheme.{u}} {U V : X.Opens}
    (h : V ≤ U) {M N : X.Modules} (a : M ⟶ N)
    [IsIso ((restrictFunctor U.ι).map a)] :
    IsIso ((restrictFunctor V.ι).map a) := by
  let k := X.homOfLE h
  let e : restrictFunctor V.ι ≅ restrictFunctor U.ι ⋙ restrictFunctor k :=
    (restrictFunctorCongr (X.homOfLE_ι h).symm) ≪≫ restrictFunctorComp k U.ι
  exact (NatIso.isIso_map_iff e a).mpr (by
    change IsIso ((restrictFunctor k).map ((restrictFunctor U.ι).map a))
    infer_instance)

private theorem restrict_tensor_map_iso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ U)
    {M N : Y.Modules} (a : M ⟶ N) [IsIso ((restrictFunctor U.ι).map a)] :
    IsIso ((restrictFunctor V.ι).map ((tensorPullback g).map a)) := by
  let r := X.homOfLE h ≫ (g ∣_ U)
  have hr : V.ι ≫ g = r ≫ U.ι := by
    simp [r, Category.assoc]
  let e : tensorPullback g ⋙ restrictFunctor V.ι ≅
      restrictFunctor U.ι ⋙ tensorPullback r :=
    Functor.isoWhiskerLeft _ (restrictFunctorIsoTensorPullback V.ι) ≪≫
      (tensorPullbackSectionComp V.ι g).symm ≪≫
      eqToIso (congrArg tensorPullback hr) ≪≫ tensorPullbackSectionComp r U.ι ≪≫
      Functor.isoWhiskerRight (restrictFunctorIsoTensorPullback U.ι).symm _
  exact (NatIso.isIso_map_iff e a).mpr (by
    change IsIso ((tensorPullback r).map ((restrictFunctor U.ι).map a))
    infer_instance)

private theorem restriction_unit_kills_kernel {X : Scheme.{u}} (U : X.Opens)
    {M N : X.Modules} (a : M ⟶ N) [IsIso ((restrictFunctor U.ι).map a)]
    (W : X.Opens) (s : Γ(M, W)) (hs : a.app W s = 0) :
    ((restrictAdjunction U.ι).unit.app M).app W s = 0 := by
  have hn := congrArg (fun t ↦ t.app W s)
    ((restrictAdjunction U.ι).unit.naturality a).symm
  have hz : ((restrictFunctor U.ι).map a).app (U.ι ⁻¹ᵁ W)
      (((restrictAdjunction U.ι).unit.app M).app W s) = 0 := by
    change ((restrictFunctor U.ι).map a).app (U.ι ⁻¹ᵁ W)
        (((restrictAdjunction U.ι).unit.app M).app W s) =
      ((restrictAdjunction U.ι).unit.app N).app W (a.app W s) at hn
    rw [hs, map_zero] at hn
    exact hn
  exact (ConcreteCategory.bijective_of_isIso _).injective
    (hz.trans (map_zero _).symm)

private theorem section_adjunction_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    tensorPullbackSectionAdjunction g =
      Classical.choose (exists_tensorPullbackAdjunction g) := by
  apply ((Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction g)).2
    (Classical.choose (exists_tensorPullbackAdjunction g)) ?_).symm
  intro M U m
  exact Classical.choose_spec (exists_tensorPullbackAdjunction g) M (Opposite.op U) m

/-- Both successive strict transforms are quasi-coherent. Their composite quotient is
surjective, is an isomorphism off the two inverse-image centres, and its kernel sections
vanish on that complement. The restriction unit is the actual restriction of sections.
Source: Stacks Project, Divisors, Tags 080I (proof paragraphs 1--2) and 080D (1)
(blueprint: lem-trf-iterated-transform-quotient-support).

Proof: apply lem-trf-strict-transform-sheaf-kernel to `(f,I,F)` to obtain quasi-coherence
of M, its quotient epimorphism and its invertibility off the first centre. Apply it
again to `(f₁,J,M)` to obtain quasi-coherence of N and the second quotient epimorphism,
invertible off the second centre. Pullback preserves epimorphisms by
lem-weil-pbc-module-pullback-epi-direct-sum (1), so the composite alpha is epimorphic.
Let U be the complement of the first centre on A and V the complement of both centres
on B. The fibre-product identities imply that q restricted to V factors through U.
Pullback composition (def-pc-module-pullback) and
lem-weil-pbc-open-immersion-module-pullback-restriction identify the first pulled-back
quotient on V with the pullback of its restriction to U, hence with an isomorphism.
The second quotient is also invertible on V. Thus alpha is invertible on V.
A section killed by alpha restricts to a section killed by that isomorphism, so is zero
there. Equivalently every local section of its kernel restricts to zero. -/
theorem iteratedModuleStrictTransform_quotient_support
    {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ h₁ : (moduleStrictTransform f I F).IsQuasicoherent,
      ∃ α : (tensorPullback
          (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).obj
            ((tensorPullback (pullback.fst f I.blowupMap)).obj F) ⟶
          @moduleStrictTransform _ _ (pullback.snd f I.blowupMap) J inferInstance
            (moduleStrictTransform f I F) h₁,
        α = (tensorPullback
            (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).map
              (cokernel.π (kernel.ι (moduleStrictTransformRestriction f I F))) ≫
          cokernel.π (kernel.ι (moduleStrictTransformRestriction (pullback.snd f I.blowupMap) J
            (moduleStrictTransform f I F))) ∧
        (@moduleStrictTransform _ _ (pullback.snd f I.blowupMap) J inferInstance
          (moduleStrictTransform f I F) h₁).IsQuasicoherent ∧
        Epi α ∧
        IsIso ((restrictFunctor
          (((pullback.fst (pullback.snd f I.blowupMap) J.blowupMap ≫
              pullback.fst f I.blowupMap ≫ f) ⁻¹ᵁ I.support.compl) ⊓
            ((pullback.fst (pullback.snd f I.blowupMap) J.blowupMap ≫
              pullback.snd f I.blowupMap) ⁻¹ᵁ J.support.compl)).ι).map α) ∧
        ∀ (W : (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Opens)
          (s : Γ((tensorPullback
            (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).obj
              ((tensorPullback (pullback.fst f I.blowupMap)).obj F), W)),
          α.app W s = 0 →
            ((restrictAdjunction
              (((pullback.fst (pullback.snd f I.blowupMap) J.blowupMap ≫
                  pullback.fst f I.blowupMap ≫ f) ⁻¹ᵁ I.support.compl) ⊓
                ((pullback.fst (pullback.snd f I.blowupMap) J.blowupMap ≫
                  pullback.snd f I.blowupMap) ⁻¹ᵁ J.support.compl)).ι).unit.app
                    ((tensorPullback
                      (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).obj
                        ((tensorPullback (pullback.fst f I.blowupMap)).obj F))).app W s = 0 := by
  let p := pullback.fst f I.blowupMap
  let q := pullback.fst (pullback.snd f I.blowupMap) J.blowupMap
  let M := moduleStrictTransform f I F
  have hM := moduleStrictTransform_properties f I F
  let : M.IsQuasicoherent := hM.2.2.2.1
  have hN := moduleStrictTransform_properties (pullback.snd f I.blowupMap) J M
  let π₀ := moduleStrictTransformπ f I F
  let π₁ := moduleStrictTransformπ (pullback.snd f I.blowupMap) J M
  let α := (tensorPullback q).map π₀ ≫ π₁
  let V := ((q ≫ p ≫ f) ⁻¹ᵁ I.support.compl) ⊓
    ((q ≫ pullback.snd f I.blowupMap) ⁻¹ᵁ J.support.compl)
  let : Epi π₀ := hM.1
  let : Epi π₁ := hN.1
  let := (tensorPullbackSectionAdjunction q).isLeftAdjoint
  let : IsIso ((restrictFunctor (moduleStrictTransformOpen f I).ι).map π₀) :=
    hM.2.2.2.2.1
  let : IsIso ((restrictFunctor
      (moduleStrictTransformOpen (pullback.snd f I.blowupMap) J).ι).map π₁) :=
    hN.2.2.2.2.1
  have hV₀ : V ≤ q ⁻¹ᵁ moduleStrictTransformOpen f I := by
    simp [V, moduleStrictTransformOpen, p, pullback.condition]
  have hV₁ : V ≤ moduleStrictTransformOpen (pullback.snd f I.blowupMap) J := by
    simp [V, moduleStrictTransformOpen, q, pullback.condition]
  let : IsIso ((restrictFunctor V.ι).map ((tensorPullback q).map π₀)) :=
    restrict_tensor_map_iso q _ V hV₀ π₀
  let : IsIso ((restrictFunctor V.ι).map π₁) := restrict_map_iso_of_le hV₁ π₁
  have : IsIso ((restrictFunctor V.ι).map α) := by
    dsimp only [α]
    rw [Functor.map_comp]
    infer_instance
  refine ⟨inferInstance, α, rfl, hN.2.2.2.1, inferInstance, inferInstance, ?_⟩
  intro W s hs
  exact restriction_unit_kills_kernel V α W s hs

/-- For F = O_X the same quotient, after the two multiplication identifications,
is the canonical quotient of O_B onto the second transform. The multiplication maps
`ε_p : p*O_X → O_A` and `ε_q : q*O_A → O_B` are the adjoints of the structure-sheaf maps
under the section-normalized pullback adjunction of def-pc-module-pullback; the statement
asserts that they are invertible. The right-hand side is the pullback of the canonical
first structure-sheaf quotient `ε_p⁻¹ ≫ π₀ : O_A → M`, preceded by `ε_q⁻¹` and followed
by the second defining quotient; it is surjective.
Source: Stacks Project, Divisors, Tags 080I (proof paragraph 1) and 080D (1)
(blueprint: lem-trf-iterated-transform-quotient-support).

Proof: specialize the quotient assertion to the structure sheaf. By
lem-weil-pbc-module-pullback-structure-sheaf, the maps epsilon_p and epsilon_q are the
multiplication isomorphisms. Precomposing alpha with epsilon_q inverse and the pullback
of epsilon_p inverse preserves its epimorphism property. Functoriality of pullback
and associativity give the displayed equality with the composite canonical quotient
from O_B. This proves precisely the structure-sheaf clause of the node. -/
theorem iteratedModuleStrictTransform_quotient_structureSheaf
    {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType] :
    let p := pullback.fst f I.blowupMap
    let q := pullback.fst (pullback.snd f I.blowupMap) J.blowupMap
    let εp := ((tensorPullbackSectionAdjunction p).homEquiv _ _).symm
      (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)
    let εq := ((tensorPullbackSectionAdjunction q).homEquiv _ _).symm
      (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom)
    let M := @moduleStrictTransform X S f I inferInstance
      (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf))
    let π₀ := cokernel.π (kernel.ι (moduleStrictTransformRestriction f I
      (SheafOfModules.unit X.ringCatSheaf)))
    let π₁ := cokernel.π (kernel.ι
      (moduleStrictTransformRestriction (pullback.snd f I.blowupMap) J M))
    M.IsQuasicoherent ∧
    ∃ (hp : IsIso εp) (hq : IsIso εq),
      Epi ((@asIso _ _ _ _ εq hq).inv ≫
        (tensorPullback q).map ((@asIso _ _ _ _ εp hp).inv ≫ π₀) ≫ π₁) ∧
      (@asIso _ _ _ _ εq hq).inv ≫ (tensorPullback q).map (@asIso _ _ _ _ εp hp).inv ≫
          (tensorPullback q).map π₀ ≫ π₁ =
        (@asIso _ _ _ _ εq hq).inv ≫
          (tensorPullback q).map ((@asIso _ _ _ _ εp hp).inv ≫ π₀) ≫ π₁ := by
  dsimp only
  let p := pullback.fst f I.blowupMap
  let q := pullback.fst (pullback.snd f I.blowupMap) J.blowupMap
  have hp : IsIso (((tensorPullbackSectionAdjunction p).homEquiv _ _).symm
      (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)) := by
    rw [section_adjunction_eq]
    exact (tensorPullbackObjUnitToUnit_isIso p).1
  have hq : IsIso (((tensorPullbackSectionAdjunction q).homEquiv _ _).symm
      (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom)) := by
    rw [section_adjunction_eq]
    exact (tensorPullbackObjUnitToUnit_isIso q).1
  let := hp
  let := hq
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hM := moduleStrictTransform_properties f I (SheafOfModules.unit X.ringCatSheaf)
  let := hM.2.2.2.1
  have hN := moduleStrictTransform_properties (pullback.snd f I.blowupMap) J
    (moduleStrictTransform f I (SheafOfModules.unit X.ringCatSheaf))
  let := hM.1
  let := hN.1
  let := (tensorPullbackSectionAdjunction q).isLeftAdjoint
  refine ⟨hM.2.2.2.1, hp, hq, ?_, ?_⟩
  · infer_instance
  · simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.Modules
