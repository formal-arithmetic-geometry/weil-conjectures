/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.CharacterModule

/-!
# Finitely generated kernels stabilize in a directed system of module localizations

Source: literature/stacks-project/algebra.tex, Algebra Tag 046Y
(blueprint: lem-trf-localization-system-kernel-stabilization).
-/

@[expose] public section

universe uI uD uP uQ uR

-- Keep the existing interface, including redundant compatibility hypotheses.
set_option linter.unusedVariables false in
/--
Let `I` be a small nonempty directed set, with a directed system of commutative rings
`D i`, modules `P i`, and semilinear transition maps.  Let `P` be the compatible
module colimit of the underlying abelian groups, and assume every transition is a
localization.  If the kernel at one stage is finitely generated, all sufficiently
late maps to `P` are injective.

Source: Stacks Project, Algebra, Tag 046Y, middle proof paragraph (finite kernel
generators and denominator argument); Tag 00D7 for eventual vanishing; Tag 07JZ
for fractions (blueprint: lem-trf-localization-system-kernel-stabilization).
The proof follows four steps: choose generators and kill each in a later stage;
choose one common upper bound and kill the whole kernel; represent a later kernel
element by a fraction from the initial stage; use the cocone and linearity identities
to put its numerator in the killed kernel and conclude the element is zero.
-/
theorem localization_system_kernel_stabilization
    (I : Type uI) [Preorder I] [Nonempty I]
    (directed : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
    (D : I → Type uD) [∀ i, CommRing (D i)]
    (d : ∀ i j : I, i ≤ j → D i →+* D j)
    (d_id : ∀ i : I, d i i (le_refl i) = RingHom.id (D i))
    (d_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      (d j k hjk).comp (d i j hij) = d i k (hij.trans hjk))
    (P : I → Type uP) [∀ i, AddCommGroup (P i)]
    (moduleP : ∀ i : I, Module (D i) (P i))
    (p : ∀ i j : I, i ≤ j → P i →+ P j)
    (p_id : ∀ i : I, p i i (le_refl i) = AddMonoidHom.id (P i))
    (p_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      (p j k hjk).comp (p i j hij) = p i k (hij.trans hjk))
    (p_semilinear : ∀ i j (hij : i ≤ j) (a : D i) (x : P i),
      p i j hij (a • x) = d i j hij a • p i j hij x)
    (Q : Type uQ) [AddCommGroup Q]
    (moduleQ : ∀ i : I, Module (D i) Q)
    (q_smul_compat : ∀ i j (hij : i ≤ j) (a : D i) (x : Q),
      d i j hij a • x = a • x)
    (psi : ∀ i : I, P i →ₗ[D i] Q)
    (psi_compat : ∀ i j (hij : i ≤ j),
      (psi j).toAddMonoidHom.comp (p i j hij) = (psi i).toAddMonoidHom)
    (cocone : ∀ (R : Type uR) [AddCommGroup R]
      (f : ∀ i : I, P i →+ R)
      (hf : ∀ i j (hij : i ≤ j), (f j).comp (p i j hij) = f i),
      ∃! g : Q →+ R, ∀ i : I, g.comp (psi i).toAddMonoidHom = f i)
    (i₀ : I)
    (finite_kernel : Module.Finite (D i₀) (LinearMap.ker (psi i₀)))
    (W : ∀ i j : I, i ≤ j → Submonoid (D i))
    (W_one : ∀ i j (hij : i ≤ j), (1 : D i) ∈ W i j hij)
    (W_mul : ∀ i j (hij : i ≤ j) (a b : D i), a ∈ W i j hij → b ∈ W i j hij →
      a * b ∈ W i j hij)
    (d_localization : ∀ i j (hij : i ≤ j),
      letI : Algebra (D i) (D j) := (d i j hij).toAlgebra
      IsLocalization (W i j hij) (D j))
    (localization_equiv : ∀ i j (hij : i ≤ j),
      letI : Algebra (D i) (D j) := (d i j hij).toAlgebra
      letI : IsLocalization (W i j hij) (D j) := d_localization i j hij
      letI : Module (D i) (P i) := moduleP i
      letI : Module (D j) (P j) := moduleP j
      letI : Module (D j) (LocalizedModule (W i j hij) (P i)) :=
        LocalizedModule.moduleOfIsLocalization (S := W i j hij) (T := D j)
      ∃ e : LocalizedModule (W i j hij) (P i) ≃ₗ[D j] P j,
        ∀ (m : P i) (s : W i j hij),
          ∃ u : D j, d i j hij (s : D i) * u = 1 ∧
            e (LocalizedModule.mk m s) = u • p i j hij m) :
    ∃ j : I, i₀ ≤ j ∧ ∀ l : I, j ≤ l → Function.Injective (psi l) := by
  classical
  let : IsDirectedOrder I := ⟨directed⟩
  let : DirectedSystem P (fun i j h ↦ p i j h) :=
    { map_self := fun {i} x ↦ DFunLike.congr_fun (p_id i) x
      map_map := fun {k j i} hij hjk x ↦ DFunLike.congr_fun (p_comp i j k hij hjk) x }
  have eventually_zero (i : I) (x : P i) (hx : psi i x = 0) :
      ∃ j, ∃ h : i ≤ j, p i j h x = 0 := by
    apply AddCommGroup.DirectLimit.of.zero_exact i x
    apply CharacterModule.eq_zero_of_character_apply
    intro c
    let up : AddCircle (1 : ℚ) →+ ULift.{uR} (AddCircle (1 : ℚ)) :=
      { toFun := ULift.up
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    let f (j : I) : P j →+ ULift.{uR} (AddCircle (1 : ℚ)) :=
      up.comp (c.comp (AddCommGroup.DirectLimit.of P p j))
    have hf (j k : I) (h : j ≤ k) : (f k).comp (p j k h) = f j := by
      apply DFunLike.ext
      intro y
      change up (c (AddCommGroup.DirectLimit.of P p k (p j k h y))) = _
      rw [AddCommGroup.DirectLimit.of_f]
      rfl
    obtain ⟨g, hg, _⟩ := cocone _ f hf
    have h := DFunLike.congr_fun (hg i) x
    change g (psi i x) = ULift.up (c (AddCommGroup.DirectLimit.of P p i x)) at h
    rw [hx, map_zero] at h
    exact (congrArg ULift.down h).symm
  let K := LinearMap.ker (psi i₀)
  obtain ⟨s, hs⟩ := finite_kernel.fg_top
  have kill_finite (t : Finset K) :
      ∃ j, ∃ h : i₀ ≤ j, ∀ z ∈ t, p i₀ j h z = 0 := by
    induction t using Finset.induction_on with
    | empty => exact ⟨i₀, le_refl _, by simp⟩
    | @insert z t hz ih =>
      obtain ⟨j, hij, hj⟩ := ih
      obtain ⟨k, hik, hk⟩ := eventually_zero i₀ z z.property
      obtain ⟨l, hjl, hkl⟩ := directed j k
      refine ⟨l, hij.trans hjl, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with hy | hy
      · subst y
        have hcomp := DFunLike.congr_fun (p_comp i₀ k l hik hkl) (z : P i₀)
        simpa only [AddMonoidHom.comp_apply, hk, map_zero] using hcomp.symm
      · have hcomp := DFunLike.congr_fun (p_comp i₀ j l hij hjl) (y : P i₀)
        simpa only [AddMonoidHom.comp_apply, hj y hy, map_zero] using hcomp.symm
  obtain ⟨j, hij, hj⟩ := kill_finite s
  have kill (l : I) (hjl : j ≤ l) (z : K) : p i₀ l (hij.trans hjl) z = 0 := by
    have hz : z ∈ Submodule.span (D i₀) (s : Set K) := by
      rw [hs]
      trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      have hcomp := DFunLike.congr_fun (p_comp i₀ j l hij hjl) (z : P i₀)
      simpa only [AddMonoidHom.comp_apply, hj z hz, map_zero] using hcomp.symm
    | zero => exact map_zero _
    | add x y _ _ hx hy => simp only [Submodule.coe_add, map_add, hx, hy, add_zero]
    | smul a x _ hx => simp only [Submodule.coe_smul, p_semilinear, hx, smul_zero]
  refine ⟨j, hij, fun l hjl ↦ ?_⟩
  apply (injective_iff_map_eq_zero (psi l)).2
  intro x hx
  let h := hij.trans hjl
  let : Algebra (D i₀) (D l) := (d i₀ l h).toAlgebra
  let : IsLocalization (W i₀ l h) (D l) := d_localization i₀ l h
  let : Module (D l) (LocalizedModule (W i₀ l h) (P i₀)) :=
    LocalizedModule.moduleOfIsLocalization (S := W i₀ l h) (T := D l)
  obtain ⟨e, he⟩ := localization_equiv i₀ l h
  have fraction (v : LocalizedModule (W i₀ l h) (P i₀))
      (hv : psi l (e v) = 0) : e v = 0 := by
    induction v using LocalizedModule.induction_on with
    | _ y w =>
      obtain ⟨u, hu, heu⟩ := he y w
      have numerator : p i₀ l h y = d i₀ l h (w : D i₀) • e (LocalizedModule.mk y w) := by
        rw [heu, smul_smul, hu, one_smul]
      have hy : psi i₀ y = 0 := by
        have hc := DFunLike.congr_fun (psi_compat i₀ l h) y
        change psi l (p i₀ l h y) = psi i₀ y at hc
        rw [← hc, numerator, map_smul, hv, smul_zero]
      rw [heu, kill l hjl ⟨y, hy⟩, smul_zero]
  simpa only [e.apply_symm_apply] using fraction (e.symm x) (by simpa using hx)
