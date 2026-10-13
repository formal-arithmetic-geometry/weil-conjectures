/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.WeilSheaf.GeometricCoinvariants

/-!
# Lisse Weil sheaves and lisse Weil representations

Let `C₀` be a smooth geometrically connected curve over the finite field `K` with Weil group
`W = W(C₀)` (`AlgebraicGeometry.WeilGroup`). This file connects the two sides of the purity theorem
for real sheaves: the sheaf side, lisse Weil sheaves `AlgebraicGeometry.WeilSheaf` on `C₀` with
their geometric stalks, local Frobenius, global sections and geometric coinvariants, and the
representation side, lisse representations of `W(C₀)`.

The lisse sheaf–representation equivalence (`prop-wf-weil-sheaf-representation-equivalence`,
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`) sends a lisse Weil sheaf `ℱ` to its
Weil fundamental representation `(V, ρ) = (ℱ_η̄, ρ_ℱ)`. From it we deduce that every lisse
representation `ρ` of `W(C₀)` is the fundamental representation of a lisse Weil sheaf `ℱ`
whose local Frobenius at a closed point `x` has the characteristic polynomial of
`ρ (Frob_x)`, and whose geometric coinvariants `Γ(C̄, ℱ^∨)^∨`
(`AlgebraicGeometry.WeilSheaf.geometricCoinvariants`) are the coinvariants `V_{π₁(C)}` with the
Frobenius induced by the degree-one lift `γ`
(`AlgebraicGeometry.WeilGroup.exists_weilSheaf_of_isLisse`).

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`: the lisse sheaf–representation
  equivalence.
- `AlgebraicGeometry.WeilGroup.exists_weilSheaf_of_isLisse`: the lisse Weil sheaf of a lisse
  representation, with its stalks and its geometric coinvariants.

## Implementation notes

The Weil fundamental representation of `def-wf-fundamental-representation` is the geometric
generic stalk `ℱ_η̄` with the monodromy action of `π₁(C₀, η̄)` extended to the Weil group by the
Weil structure. Neither the monodromy action of the étale fundamental group on a stalk of an
`ℓ`-adic pro-étale sheaf nor the functor `ℱ ↦ ρ_ℱ` is available, so the equivalence is
existentially quantified, and the fact that it *is* the Weil fundamental representation is
recorded by the properties of it that the blueprint uses: at a closed point `x`, the stalk
`ℱ_x̄` with its local Frobenius `F_x` is `V` with `ρ (Frob_x)` (the stalk at `x̄` being
transported to the base point along a path, which carries the geometric Frobenius of `κ(x)` to
the Frobenius element `Frob_x` of `W(C₀)`); the equivalence is compatible with duals (it is a
tensor equivalence); and the global sections `H⁰(C̄, ℱ)` are the invariants `V ^ {π₁(C)}` with
the Frobenius `ρ (γ)`, which is `p-real-sections` for `U₀ = C₀`. The last clause is a
consequence of the equivalence in the blueprint (`p-real-sections`); it is recorded with it here
because the functor, being existentially quantified, can only be described through its
properties.
-/

@[expose] public section

universe u

open CategoryTheory

namespace FrobeniusModule

variable {k : Type*} [Field k]

/-- If a Frobenius module `M` is identified with the dual `N^∨` of a finite-dimensional space
`N` with an automorphism `T`, so that the Frobenius of `M` becomes the inverse transpose of
`T`, then the dual Frobenius module `M^∨` is `N` with `T`. -/
theorem exists_linearEquiv_dual_of_linearEquiv_dual (M : FrobeniusModule k) {N : Type*}
    [AddCommGroup N] [Module k N] [FiniteDimensional k N] (T : N ≃ₗ[k] N)
    (c : M.carrier ≃ₗ[k] Module.Dual k N) (hc : ∀ m n, c (M.frobenius m) (T n) = c m n) :
    ∃ f : M.dual.carrier ≃ₗ[k] N, ∀ φ, f (M.dual.frobenius φ) = T (f φ) := by
  refine ⟨c.dualMap.symm.trans (Module.evalEquiv k N).symm, fun φ ↦ ?_⟩
  apply (Module.evalEquiv k N).injective
  refine LinearMap.ext fun ψ ↦ ?_
  have key : M.frobenius.symm (c.symm ψ) = c.symm (ψ ∘ₗ T.toLinearMap) := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq]
    refine LinearMap.ext fun n ↦ ?_
    have h := hc (c.symm (ψ ∘ₗ T.toLinearMap)) (T.symm n)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [h, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply,
    Module.evalEquiv_apply, Module.Dual.eval_apply, ← LinearEquiv.coe_toLinearMap T,
    ← LinearMap.comp_apply, Module.apply_evalEquiv_symm_apply, LinearEquiv.dualMap_symm]
  change (show Module.Dual k M.carrier from M.dual.frobenius φ) (c.symm ψ) =
    (show Module.Dual k M.carrier from φ) (c.symm (ψ ∘ₗ T.toLinearMap))
  rw [dual_frobenius_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, key]

end FrobeniusModule

namespace AlgebraicGeometry

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [GeometricallyConnected (C ↘ Spec (.of K))] (W : WeilGroup (C ↘ Spec (.of K))) (l : ℕ)
  [Fact l.Prime] [Fact (ringChar K ≠ l)]

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence` (subsection `sk-i-real-sheaves`):
The lisse sheaf–representation equivalence.

The functor `ℱ ↦ (V, ρ) = (ℱ_η̄, ρ_ℱ)`, sending a lisse Weil sheaf on the curve `C₀` to its Weil
fundamental representation (`def-wf-fundamental-representation`), is an exact tensor
equivalence between lisse Weil sheaves on `C₀` and lisse representations of `W(C₀)`
(`AlgebraicGeometry.WeilGroup.isLisseRep`). The functor `e.functor` is the Weil fundamental
representation:

* at every closed point `x`, the geometric stalk `ℱ_x̄` with its local Frobenius `F_x` is
  isomorphic to `V` with `ρ (Frob_x)`, `Frob_x = W.frobenius x` being a Frobenius element at `x`
  (`def-wf-fundamental-representation`, the stalk at `x̄` transported to the base point along a
  path);
* it is compatible with duals: the representation of `ℱ^∨` is the contragredient of that of `ℱ`;
* the global sections `H⁰(C̄, ℱ)` are the invariants `V ^ {π₁(C)}`, compatibly with the
  Frobenius `ρ (γ)` of the degree-one lift `γ` (`p-real-sections`, for `U₀ = C₀`). -/
theorem exists_equivalence_isLisse :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
          (x : C.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ (W.frobenius x) (f v)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        Nonempty ((e.functor.obj ⟨F.obj.dual F.property, F.property.dual⟩).obj.ρ.Equiv
          (e.functor.obj F).obj.ρ.dual)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        ∃ f : F.obj.globalSections.carrier ≃ₗ[PadicAlgCl l]
            Representation.invariants ((e.functor.obj F).obj.ρ.comp W.geometric.subtype),
          ∀ v, (f (F.obj.globalSections.frobenius v) : (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ W.frobeniusLift (f v)) := by
  sorry

/-- The linear isomorphism underlying an isomorphism of representations. -/
private noncomputable def repLinearEquivOfIso {k G : Type*} [CommRing k] [Monoid G]
    {A B : Rep.{u} k G} (e : A ≅ B) : A.V ≃ₗ[k] B.V :=
  LinearEquiv.ofLinearMap e.hom.hom.toLinearMap e.inv.hom.toLinearMap
    (LinearMap.ext fun b ↦ by
      change (e.inv ≫ e.hom).hom b = b
      rw [e.inv_hom_id]
      rfl)
    (LinearMap.ext fun a ↦ by
      change (e.hom ≫ e.inv).hom a = a
      rw [e.hom_inv_id]
      rfl)

private theorem repLinearEquivOfIso_apply {k G : Type*} [CommRing k] [Monoid G]
    {A B : Rep.{u} k G} (e : A ≅ B) (a : A.V) : repLinearEquivOfIso e a = e.hom.hom a :=
  rfl

variable {W l}

set_option maxHeartbeats 400000 in
-- the final transport through the duals unfolds large `let`-bound linear equivalences
/-- A lisse representation `ρ` of `W(C₀)` is the Weil fundamental representation of a lisse Weil
sheaf `ℱ` on `C₀`: the local Frobenius `F_x` on the stalk `ℱ_x̄` has the characteristic
polynomial of `ρ (Frob_x)` at every closed point `x`, and the geometric coinvariants
`Γ(C̄, ℱ^∨)^∨` of `ℱ` are the coinvariants `V_{π₁(C)}` of `ρ`, with the Frobenius induced by
`ρ (γ)`.

The sheaf is the image of `ρ` under the inverse of the equivalence
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`. Its stalks are described by that
equivalence. For the coinvariants: the global sections `Γ(C̄, ℱ^∨)` are the invariants of the
representation of `ℱ^∨`, which is the contragredient `ρ^∨`, and the `π₁(C)`-invariant linear
forms on `V` are the linear forms on `V_{π₁(C)}`; dualising gives `V_{π₁(C)}` back, with the
Frobenius `ρ (γ)`. -/
theorem exists_weilSheaf_of_isLisse {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] {ρ : Representation (PadicAlgCl l) W.carrier V}
    (hρ : W.IsLisse l ρ) :
    ∃ (F : WeilSheaf K l C) (hF : F.IsLisse),
      (∀ x : C.finitePoints, (F.stalk x).frobeniusEnd.charpoly = (ρ (W.frobenius x)).charpoly) ∧
      ∃ f : (F.geometricCoinvariants hF).carrier ≃ₗ[PadicAlgCl l]
          Representation.Coinvariants (ρ.comp W.geometric.subtype),
        ∀ v, f ((F.geometricCoinvariants hF).frobenius v) =
          ρ.toCoinvariants W.geometric W.frobeniusLift (f v) := by
  obtain ⟨e, hst, hdu, hse⟩ := W.exists_equivalence_isLisse l
  let X : ObjectProperty.FullSubcategory (W.isLisseRep l) := ⟨Rep.of ρ, inferInstance, hρ⟩
  set F := e.inverse.obj X
  set ρF := (e.functor.obj F).obj.ρ
  let ψ : (e.functor.obj F).obj.V ≃ₗ[PadicAlgCl l] V :=
    repLinearEquivOfIso ((ObjectProperty.ι _).mapIso (e.counitIso.app X))
  have hψ (g : W.carrier) (v : (e.functor.obj F).obj.V) : ψ (ρF g v) = ρ g (ψ v) :=
    Rep.hom_comm_apply ((ObjectProperty.ι _).mapIso (e.counitIso.app X)).hom g v
  have hψ' (g : W.carrier) (v : V) : ψ.symm (ρ g v) = ρF g (ψ.symm v) := by
    rw [LinearEquiv.symm_apply_eq, hψ, LinearEquiv.apply_symm_apply]
  refine ⟨F.obj, F.property, fun x ↦ ?_, ?_⟩
  · obtain ⟨f, hf⟩ := hst F x
    refine LinearMap.charpoly_eq_of_comp_eq (f.trans ψ) (LinearMap.ext fun v ↦ ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, FrobeniusModule.frobeniusEnd_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, hf, hψ, LinearEquiv.trans_apply]
  · set G := W.geometric
    set Fd : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) :=
      ⟨F.obj.dual F.property, F.property.dual⟩
    set ρd := (e.functor.obj Fd).obj.ρ
    obtain ⟨a, ha⟩ := hse Fd
    obtain ⟨b⟩ := hdu F
    let bL := b.toLinearEquiv
    have hb (g : W.carrier) (u) : bL (ρd g u) = ρF.dual g (bL u) :=
      Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap g u
    have hdual (g : W.carrier) (φ : Module.Dual (PadicAlgCl l) (e.functor.obj F).obj.V) (w) :
        ρF.dual g φ w = φ (ρF g⁻¹ w) := by
      rw [Representation.dual_apply]
      rfl
    -- the linear forms coming from invariants of `ρ^∨` are invariant
    have hinv (u : Representation.invariants (ρd.comp G.subtype)) (h : G) (w) :
        bL u.1 (ρF h w) = bL u.1 w := by
      have h1 : ρd ((h⁻¹ : G) : W.carrier) u.1 = u.1 := u.2 h⁻¹
      have h2 := congrArg (fun z ↦ bL z w) h1
      rw [hb, hdual, Subgroup.coe_inv, inv_inv] at h2
      exact h2
    have hmk (h : G) (v : V) : Representation.Coinvariants.mk (ρ.comp G.subtype) (ρ h v) =
        Representation.Coinvariants.mk (ρ.comp G.subtype) v :=
      Representation.Coinvariants.mk_self_apply _ h v
    -- invariant linear forms on `V` are the linear forms on the coinvariants
    let toF : Representation.invariants (ρd.comp G.subtype) →ₗ[PadicAlgCl l]
        Module.Dual (PadicAlgCl l) (Representation.Coinvariants (ρ.comp G.subtype)) :=
      { toFun u := Representation.Coinvariants.lift (ρ.comp G.subtype)
          (bL u.1 ∘ₗ ψ.symm.toLinearMap) (fun h ↦ LinearMap.ext fun v ↦ by
            simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, MonoidHom.comp_apply,
              Subgroup.coe_subtype]
            rw [hψ', hinv u h])
        map_add' u u' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ by
          simp [Representation.Coinvariants.lift_mk])
        map_smul' r u := Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ by
          simp [Representation.Coinvariants.lift_mk]) }
    have htoF (u) (v : V) : toF u (Representation.Coinvariants.mk _ v) = bL u.1 (ψ.symm v) :=
      rfl
    let invF : Module.Dual (PadicAlgCl l) (Representation.Coinvariants (ρ.comp G.subtype)) →ₗ[
        PadicAlgCl l] Representation.invariants (ρd.comp G.subtype) :=
      { toFun φ := ⟨bL.symm (φ ∘ₗ Representation.Coinvariants.mk _ ∘ₗ ψ.toLinearMap), fun h ↦ by
          change ρd (h : W.carrier) _ = _
          apply bL.injective
          rw [hb, LinearEquiv.apply_symm_apply]
          refine LinearMap.ext fun w ↦ ?_
          rw [hdual]
          simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
          rw [hψ, ← Subgroup.coe_inv, hmk]⟩
        map_add' φ φ' := Subtype.ext (by simp [LinearMap.add_comp])
        map_smul' r φ := Subtype.ext (by simp [LinearMap.smul_comp]) }
    let d : Representation.invariants (ρd.comp G.subtype) ≃ₗ[PadicAlgCl l]
        Module.Dual (PadicAlgCl l) (Representation.Coinvariants (ρ.comp G.subtype)) :=
      LinearEquiv.ofLinearMap toF invF
      (LinearMap.ext fun φ ↦ Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ by
        change bL (bL.symm _) (ψ.symm v) = _
        rw [LinearEquiv.apply_symm_apply]
        simp))
      (LinearMap.ext fun u ↦ Subtype.ext (by
        change bL.symm (toF u ∘ₗ Representation.Coinvariants.mk _ ∘ₗ ψ.toLinearMap) = u.1
        rw [LinearEquiv.symm_apply_eq]
        refine LinearMap.ext fun v ↦ ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, htoF,
          LinearEquiv.symm_apply_apply]))
    -- the Frobenius `ρ (γ)` on the coinvariants
    let Q := ρ.toCoinvariants G
    let T : Representation.Coinvariants (ρ.comp G.subtype) ≃ₗ[PadicAlgCl l]
        Representation.Coinvariants (ρ.comp G.subtype) :=
      LinearEquiv.ofLinearMap (Q W.frobeniusLift) (Q W.frobeniusLift⁻¹)
        (LinearMap.ext fun n ↦ by
          rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply, LinearMap.id_apply])
        (LinearMap.ext fun n ↦ by
          rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply, LinearMap.id_apply])
    have hc (m : Fd.obj.globalSections.carrier)
        (n : Representation.Coinvariants (ρ.comp G.subtype)) :
        (a.trans d) (Fd.obj.globalSections.frobenius m) (T n) = (a.trans d) m n := by
      refine Representation.Coinvariants.induction_on n fun v ↦ ?_
      change toF (a _) (Q W.frobeniusLift (Representation.Coinvariants.mk _ v)) =
        toF (a m) (Representation.Coinvariants.mk _ v)
      rw [Representation.toCoinvariants_mk, htoF, htoF, ha, hb, hdual, hψ',
        ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    obtain ⟨f, hf⟩ := FrobeniusModule.exists_linearEquiv_dual_of_linearEquiv_dual
      Fd.obj.globalSections T (a.trans d) hc
    exact ⟨f, hf⟩

end WeilGroup

end AlgebraicGeometry
