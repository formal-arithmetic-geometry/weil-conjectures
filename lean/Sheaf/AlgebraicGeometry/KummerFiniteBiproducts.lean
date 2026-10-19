/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Integral finite-basis comparisons in sheaf cohomology

The explicit finite-sum comparison used in the integral-lift clause of Kummer
coefficient change. Source: Stacks Tag 015B, additivity of cohomology.
(blueprint: lem-pur-kummer-finite-biproducts).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

private lemma cohomology_map_sum (C : Scheme.{u})
    {F G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {ι : Type*} (s : Finset ι) (f : ι → (F ⟶ G)) (q : ℕ) (x : Sheaf.H F q) :
    Sheaf.H.map (∑ j ∈ s, f j) q x = ∑ j ∈ s, Sheaf.H.map (f j) q x := by
  induction s using Finset.cons_induction with
  | empty =>
    exact congrArg (fun f ↦ f x) ((Sheaf.functorH C.smallEtaleTopology q).map_zero F G)
  | cons a s ha ih => simp only [Finset.sum_cons, Sheaf.H.map_add_apply, ih]

private lemma cohomology_map_zsmul (C : Scheme.{u})
    {F G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) (q : ℕ) (n : ℤ) (x : Sheaf.H F q) :
    Sheaf.H.map (n • f) q x = n • Sheaf.H.map f q x := by
  exact congrArg (fun f ↦ f x) ((Sheaf.functorH C.smallEtaleTopology q).map_zsmul
    (f := f) (r := n))

/-- A finite integral basis identifies tensoring cohomology with the cohomology of
its finite biproduct, with the expected formula on pure tensors.
Source: Stacks Tag 015B, finite-sum additivity.
Proof: send a tensor to the sum of the basis-coordinate multiples of the inclusions.
The inverse sends y to the sum of H of each projection applied to y, tensor the
corresponding basis vector. The projection-inclusion identities and the two finite
basis expansions make the composites identities, also for the empty basis.
(blueprint: lem-pur-kummer-finite-biproducts). -/
theorem integral_cohomology_biproduct (C : Scheme.{u})
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (L : ModuleCat.{u + 1} ℤ) (r : ℕ) (b : Module.Basis (Fin r) ℤ L)
    [HasBiproduct (fun _ : Fin r ↦ G)] (q : ℕ) :
    ∃ alpha : (Sheaf.H G q ⊗[ℤ] L) ≃+ Sheaf.H (⨁ fun _ : Fin r ↦ G) q,
      ∀ (x : Sheaf.H G q) (l : L), alpha (x ⊗ₜ[ℤ] l) =
        Sheaf.H.map (∑ j : Fin r, (b.repr l j) •
          biproduct.ι (fun _ : Fin r ↦ G) j) q x := by
  classical
  let incl (j : Fin r) := Sheaf.H.map (biproduct.ι (fun _ : Fin r ↦ G) j) q
  let proj (j : Fin r) := Sheaf.H.map (biproduct.π (fun _ : Fin r ↦ G) j) q
  let phi : (Sheaf.H G q ⊗[ℤ] L) →ₗ[ℤ] Sheaf.H (⨁ fun _ : Fin r ↦ G) q :=
    (Finsupp.lsum ℤ (fun j ↦ (incl j).toIntLinearMap)).comp
      (TensorProduct.equivFinsuppOfBasisRight b).toLinearMap
  have hphi (x : Sheaf.H G q) (l : L) :
      phi (x ⊗ₜ[ℤ] l) = ∑ j : Fin r, (b.repr l j) • incl j x := by
    change Finsupp.sum _ _ = _
    rw [Finsupp.sum_fintype]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        LinearEquiv.coe_coe, AddMonoidHom.coe_toIntLinearMap, map_zsmul]
    · intro j
      exact map_zero (incl j)
  let psi : Sheaf.H (⨁ fun _ : Fin r ↦ G) q →ₗ[ℤ] (Sheaf.H G q ⊗[ℤ] L) :=
    ∑ j : Fin r, ((TensorProduct.mk ℤ (Sheaf.H G q) L).flip (b j)).comp
      (proj j).toIntLinearMap
  have hpsi (y : Sheaf.H (⨁ fun _ : Fin r ↦ G) q) :
      psi y = ∑ j : Fin r, proj j y ⊗ₜ[ℤ] b j := by
    simp only [psi, LinearMap.sum_apply, LinearMap.comp_apply,
      AddMonoidHom.coe_toIntLinearMap, TensorProduct.mk_apply, LinearMap.flip_apply]
  refine ⟨{ toFun := phi
            invFun := psi
            map_add' := phi.map_add
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul x l =>
      rw [hphi, map_sum]
      simp only [map_zsmul, hpsi]
      have hcomp (i j : Fin r) : proj j (incl i x) = if i = j then x else 0 := by
        by_cases h : i = j
        · subst j
          simp [proj, incl, ← Sheaf.H.map_comp_apply]
        · simp only [proj, incl, ← Sheaf.H.map_comp_apply, biproduct.ι_π, h, dite_false,
            if_false]
          exact congrArg (fun f ↦ f x)
            ((Sheaf.functorH C.smallEtaleTopology q).map_zero G G)
      change (∑ i : Fin r, ∑ j : Fin r,
        ((b.repr l i) • proj j (incl i x)) ⊗ₜ[ℤ] b j) = _
      simp only [hcomp, smul_ite, smul_zero, TensorProduct.ite_tmul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      calc
        _ = ∑ j : Fin r, x ⊗ₜ[ℤ] ((b.repr l j) • b j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact (((TensorProduct.mk ℤ (Sheaf.H G q) L).flip (b j)).toAddMonoidHom.map_zsmul
            (b.repr l j) x).trans
              (((TensorProduct.mk ℤ (Sheaf.H G q) L x).toAddMonoidHom.map_zsmul
                (b.repr l j) (b j)).symm)
        _ = x ⊗ₜ[ℤ] l := by
          rw [← TensorProduct.tmul_sum]
          apply congrArg (fun l ↦ x ⊗ₜ[ℤ] l)
          calc
            _ = ∑ j : Fin r, L.isModule.smul (b.repr l j) (b j) := by
              apply Finset.sum_congr rfl
              intro j _
              exact (int_smul_eq_zsmul L.isModule (b.repr l j) (b j)).symm
            _ = l := b.sum_repr l
  · intro y
    rw [hpsi, map_sum]
    simp only [hphi, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    simp only [incl, proj, ← Sheaf.H.map_comp_apply]
    rw [← cohomology_map_sum, biproduct.total, Sheaf.H.map_id_apply]
  · intro x l
    change phi _ = _
    rw [hphi, cohomology_map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (cohomology_map_zsmul C _ q _ x).symm

/-- A finite sum of the ordinary Kummer sequence is short exact.
Source: Stacks Tags 03PL and 015B, finite direct sums of exact sequences.
(blueprint: lem-pur-kummer-finite-biproducts). -/
theorem kummer_biproduct_shortExact (C : Scheme.{u}) (m : ℕ)
    (hm : IsUnit (m : Γ(C, ⊤))) (r : ℕ)
    [HasFiniteBiproducts (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    ∃ w : biproduct.map (fun _ : Fin r ↦ (C.kummerSequence m).f) ≫
        biproduct.map (fun _ : Fin r ↦ (C.kummerSequence m).g) = 0,
      (ShortComplex.mk _ _ w).ShortExact := by
  let F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    Functor.const (Discrete (Fin r)) ⋙ lim
  let E (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      (⨁ fun _ : Fin r ↦ G) ≅ F.obj G :=
    biproduct.isoProduct _ ≪≫ Pi.isoLimit ((Functor.const (Discrete (Fin r))).obj G)
  have hE {G G' : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : G ⟶ G') :
      (E G).hom ≫ F.map a = biproduct.map (fun _ : Fin r ↦ a) ≫ (E G').hom := by
    apply limit.hom_ext
    intro j
    obtain ⟨j⟩ := j
    simp [E, F]
  have w : biproduct.map (fun _ : Fin r ↦ (C.kummerSequence m).f) ≫
      biproduct.map (fun _ : Fin r ↦ (C.kummerSequence m).g) = 0 := by
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, biproduct.map_π]
    rw [← Category.assoc, biproduct.map_π, Category.assoc,
      (C.kummerSequence m).zero, comp_zero, zero_comp]
  refine ⟨w, ?_⟩
  let e : ShortComplex.mk _ _ w ≅ (C.kummerSequence m).map F :=
    ShortComplex.isoMk (E _) (E _) (E _) (hE _) (hE _)
  exact ShortComplex.shortExact_of_iso e.symm
    ((C.kummerSequence_shortExact m hm).map_of_exact F)

end AlgebraicGeometry.Scheme
