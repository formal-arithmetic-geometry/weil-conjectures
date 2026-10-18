/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker E2
-/
module

public import Sheaf.CategoryTheory.DiscreteModulesAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Degree-zero cochains and invariants

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology (blueprint: lem-exc-continuous-cochains-invariants-zero).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

set_option linter.unusedVariables false in
/-- Degree-zero continuous cochain homology is the left exact invariant functor.

Proof: A continuous map from the singleton `Fin 0 → G` is a constant coefficient.
The degree-zero differential is the function `g ↦ ρ(g)m - m`, so its kernel is exactly
`⨅ g, ker (ρ(g) - id)`. There are no incoming boundaries in degree zero; the homology
kernel description therefore gives a linear equivalence to this invariant submodule.
Postcomposition commutes with evaluation and with the kernel inclusion, making the
identifications natural. Define the invariant functor on maps by restriction of the
underlying equivariant linear map. Restriction preserves identities, compositions and
addition. This construction is data, independent of any existence choice. Finally the
forgetful functor detects module kernels and finite products by
`lem-exc-discrete-modules-abelian`; taking invariant elements commutes with both kernels
and finite products. Thus the constructed invariant functor preserves finite limits.
The degree-zero equivalences assemble into the asserted natural isomorphism.

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology, degree-zero differential and invariants.
(blueprint: lem-exc-continuous-cochains-invariants-zero). -/
theorem continuousCochains_invariants_zero
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    let h := Classical.choose (discreteModules_abelian.{u, v, max u w} G A)
    letI := h
    letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := h.toPreadditive
    letI : Preadditive (ModuleCat.{max u w} A) :=
      (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
    letI := (Classical.choose_spec
      (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.1
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, TopologicalSpace M.obj.V :=
      fun _ ↦ ⊥
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, DiscreteTopology M.obj.V :=
      fun _ ↦ ⟨rfl⟩
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
        ContinuousConstSMul A M.obj.V :=
      fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
    let S := fun M : DiscreteContinuousRep.{v, u, max u w} A G =>
      ⨅ g : G, LinearMap.ker (M.obj.ρ g - LinearMap.id)
    ∀ F : DiscreteContinuousRep.{v, u, max u w} A G ⥤
        CochainComplex (ModuleCat.{max u w} A) ℕ,
      ∀ e : ∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ),
        (F.obj M).X n ≃ₗ[A] C(Fin n → G, M.obj.V),
        (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
          (n : ℕ) (x : (F.obj M).X n) (g : Fin n → G),
          e N n (((F.map f).f n).hom x) g = f.hom.hom (e M n x g)) →
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ)
          (x : (F.obj M).X n) (g : Fin (n + 1) → G),
          e M (n + 1) (((F.obj M).d n (n + 1)).hom x) g =
            M.obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
              ∑ k : Fin (n + 1),
                (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) →
    ∃ V : DiscreteContinuousRep.{v, u, max u w} A G ⥤ ModuleCat.{max u w} A,
      ∃ a : V.Additive,
        letI instAdditive : V.Additive := a
        ∃ t : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
            V.obj M ≃ₗ[A] S M,
          (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
            (x : V.obj M),
            (t N ((V.map f).hom x)).val = f.hom.hom (t M x).val) ∧
          PreservesFiniteLimits V ∧
          Nonempty ((F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u w} A)
            (ComplexShape.up ℕ) 0) ≅ V) := by
  classical
  dsimp only
  let h := Classical.choose (discreteModules_abelian.{u, v, max u w} G A)
  let := h
  let : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := h.toPreadditive
  let : Preadditive (ModuleCat.{max u w} A) :=
    (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
  let := (Classical.choose_spec
    (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.1
  let : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, TopologicalSpace M.obj.V :=
    fun _ ↦ ⊥
  let : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, DiscreteTopology M.obj.V :=
    fun _ ↦ ⟨rfl⟩
  let : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
      ContinuousConstSMul A M.obj.V :=
    fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
  intro F e hm hd
  let S := fun M : DiscreteContinuousRep.{v, u, max u w} A G ↦
    ⨅ g : G, LinearMap.ker (M.obj.ρ g - LinearMap.id)
  have hS (M : DiscreteContinuousRep.{v, u, max u w} A G) (x : M.obj.V) :
      x ∈ S M ↔ ∀ g : G, M.obj.ρ g x = x := by
    simp only [S, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  let V : DiscreteContinuousRep.{v, u, max u w} A G ⥤ ModuleCat.{max u w} A :=
    { obj := fun M ↦ ModuleCat.of A (S M)
      map := fun {M N} f ↦ ModuleCat.ofHom
        { toFun := fun x ↦ ⟨f.hom.hom x.val, (hS N _).mpr (fun g ↦ by
            rw [← hom_comm_apply f.hom g x.val, (hS M x.val).mp x.property g])⟩
          map_add' := fun x y ↦ Subtype.ext (map_add f.hom.hom x.val y.val)
          map_smul' := fun a x ↦ Subtype.ext (map_smul f.hom.hom a x.val) }
      map_id := fun M ↦ by ext x; rfl
      map_comp := fun f g ↦ by ext x; rfl }
  let P : ObjectProperty (Rep.{max u w} A G) :=
    fun X ↦ ∀ x : X.V, IsOpen {g : G | X.ρ g x = x}
  let L : ModuleCat.{max u w} A ⥤ P.FullSubcategory :=
    P.lift (trivialFunctor A G) (by
      intro X x
      change IsOpen {g : G | x = x}
      simp)
  have adj : L ⊣ V := Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun f ↦ ModuleCat.ofHom
            { toFun := fun x ↦ ⟨f.hom.hom x, (hS Y _).mpr (fun g ↦
                (hom_comm_apply f.hom g x).symm)⟩
              map_add' := fun x y ↦ Subtype.ext (map_add f.hom.hom x y)
              map_smul' := fun a x ↦ Subtype.ext (map_smul f.hom.hom a x) }
          invFun := fun f ↦ ObjectProperty.homMk (Rep.ofHom
            ⟨(S Y).subtype.comp f.hom, fun g ↦ by
              ext x
              exact ((hS Y _).mp (f.hom x).property g).symm⟩)
          left_inv := fun f ↦ by
            apply ObjectProperty.hom_ext
            apply Rep.hom_ext
            apply Representation.IntertwiningMap.ext
            ext x
            rfl
          right_inv := fun f ↦ by ext x; rfl }
      homEquiv_naturality_left_symm := fun f g ↦ by
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        ext x
        rfl
      homEquiv_naturality_right := fun f g ↦ by ext x; rfl }
  let : V.IsRightAdjoint := adj.isRightAdjoint
  let : V.Additive := Functor.additive_of_preserves_binary_products V
  refine ⟨V, inferInstance, (fun M ↦ LinearEquiv.refl A (S M)), ?_, inferInstance, ?_⟩
  · intro M N f x
    rfl
  · let z : Fin 0 → G := fun _ ↦ 1
    have hdiff (M : DiscreteContinuousRep.{v, u, max u w} A G)
        (x : (F.obj M).X 0) (g : Fin 1 → G) :
        e M 1 (((F.obj M).d 0 1).hom x) g =
          M.obj.ρ (g 0) (e M 0 x z) - e M 0 x z := by
      rw [hd]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, zero_add, pow_one,
        neg_smul, one_smul, add_zero, sub_eq_add_neg]
      congr 1
      · exact congrArg (fun t ↦ M.obj.ρ (g 0) (e M 0 x t)) (Subsingleton.elim _ _)
      · exact congrArg (fun t ↦ -(e M 0 x t)) (Subsingleton.elim _ _)
    let i (M : DiscreteContinuousRep.{v, u, max u w} A G) :
        V.obj M ⟶ (F.obj M).X 0 := ModuleCat.ofHom
      { toFun := fun m ↦ (e M 0).symm (ContinuousMap.const _ m.val)
        map_add' := by
          intro x y
          apply (e M 0).injective
          simp only [LinearEquiv.apply_symm_apply, map_add]
          ext g
          rfl
        map_smul' := by
          intro a x
          apply (e M 0).injective
          simp only [LinearEquiv.apply_symm_apply, map_smul]
          ext g
          rfl }
    have hi (M : DiscreteContinuousRep.{v, u, max u w} A G) :
        i M ≫ (F.obj M).d 0 1 = 0 := by
      ext m
      apply (e M 1).injective
      ext g
      change e M 1 (((F.obj M).d 0 1).hom ((i M).hom m)) g = e M 1 0 g
      rw [map_zero, ContinuousMap.zero_apply, hdiff]
      change M.obj.ρ (g 0)
        ((e M 0) ((e M 0).symm (ContinuousMap.const _ m.val)) z) -
        ((e M 0) ((e M 0).symm (ContinuousMap.const _ m.val)) z) = 0
      simp only [LinearEquiv.apply_symm_apply, ContinuousMap.const_apply]
      exact sub_eq_zero.mpr ((hS M m.val).mp m.property (g 0))
    let j (M : DiscreteContinuousRep.{v, u, max u w} A G) :
        V.obj M ⟶ (F.obj M).cycles 0 :=
      (F.obj M).liftCycles (i M) 1 (by simp) (hi M)
    let p (M : DiscreteContinuousRep.{v, u, max u w} A G) :
        (F.obj M).cycles 0 ⟶ V.obj M := ModuleCat.ofHom
      { toFun := fun x ↦ ⟨e M 0 (((F.obj M).iCycles 0).hom x) z, (hS M _).mpr (by
          intro g
          apply sub_eq_zero.mp
          have hx := ConcreteCategory.congr_hom ((F.obj M).iCycles_d 0 1) x
          change ((F.obj M).d 0 1).hom (((F.obj M).iCycles 0).hom x) = 0 at hx
          have hx' := hdiff M (((F.obj M).iCycles 0).hom x) (fun _ ↦ g)
          rw [hx, map_zero, ContinuousMap.zero_apply] at hx'
          exact hx'.symm)⟩
        map_add' := by
          intro x y
          apply Subtype.ext
          change e M 0 (((F.obj M).iCycles 0).hom (x + y)) z =
            e M 0 (((F.obj M).iCycles 0).hom x) z +
              e M 0 (((F.obj M).iCycles 0).hom y) z
          simp
        map_smul' := by
          intro a x
          apply Subtype.ext
          change e M 0 (((F.obj M).iCycles 0).hom (a • x)) z =
            a • e M 0 (((F.obj M).iCycles 0).hom x) z
          simp }
    have hj (M : DiscreteContinuousRep.{v, u, max u w} A G) :
        j M ≫ (F.obj M).iCycles 0 = i M :=
      (F.obj M).liftCycles_i (i M) 1 (by simp) (hi M)
    have hpj (M : DiscreteContinuousRep.{v, u, max u w} A G) :
        p M ≫ j M = 𝟙 _ := by
      apply (cancel_mono ((F.obj M).iCycles 0)).mp
      rw [Category.assoc, hj]
      ext x
      apply (e M 0).injective
      ext g
      change (e M 0) ((e M 0).symm
        (ContinuousMap.const _ (e M 0 (((F.obj M).iCycles 0).hom x) z))) g =
          e M 0 (((F.obj M).iCycles 0).hom x) g
      simp only [LinearEquiv.apply_symm_apply, ContinuousMap.const_apply]
      exact congrArg (e M 0 (((F.obj M).iCycles 0).hom x)) (Subsingleton.elim _ _)
    have hjp (M : DiscreteContinuousRep.{v, u, max u w} A G) :
        j M ≫ p M = 𝟙 _ := by
      ext x
      have hx := ConcreteCategory.congr_hom (hj M) x
      change ((F.obj M).iCycles 0).hom ((j M).hom x) = (i M).hom x at hx
      change e M 0 (((F.obj M).iCycles 0).hom ((j M).hom x)) z = x.val
      rw [hx]
      change (e M 0) ((e M 0).symm (ContinuousMap.const _ x.val)) z = x.val
      simp
    let a (M : DiscreteContinuousRep.{v, u, max u w} A G) :
        (F.obj M).cycles 0 ≅ V.obj M :=
      { hom := p M, inv := j M, hom_inv_id := hpj M, inv_hom_id := hjp M }
    refine ⟨NatIso.ofComponents
      (fun M ↦ (F.obj M).isoHomologyπ₀.symm ≪≫ a M) ?_⟩
    intro M N f
    change HomologicalComplex.homologyMap (F.map f) 0 ≫
      (F.obj N).isoHomologyπ₀.inv ≫ p N =
      (F.obj M).isoHomologyπ₀.inv ≫ p M ≫ V.map f
    rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality,
      Category.assoc]
    congr 1
    ext x
    have hx := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (F.map f) 0) x
    change ((F.obj N).iCycles 0).hom
      ((HomologicalComplex.cyclesMap (F.map f) 0).hom x) =
        ((F.map f).f 0).hom (((F.obj M).iCycles 0).hom x) at hx
    change e N 0 (((F.obj N).iCycles 0).hom
      ((HomologicalComplex.cyclesMap (F.map f) 0).hom x)) z =
      f.hom.hom (e M 0 (((F.obj M).iCycles 0).hom x) z)
    rw [hx]
    exact hm M N f 0 (((F.obj M).iCycles 0).hom x) z

end Rep
