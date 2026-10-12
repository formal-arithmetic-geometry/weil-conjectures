/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Sheaf.Algebra.Homology.SubcategoryRightResolutionAssembly

/-!
# The ascending pushout system for a right resolution

Source: Stacks Project, Tag 05T6(1), dual of the induction in Tag 05T7(1).
(blueprint: lem-weil-pbc-subcategory-right-resolution-system).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
/-- One term and its cokernel projection, with the mono induction invariant. -/
private structure RightResolutionFrontier (K : CochainComplex C ℤ) (𝓘 : Set C) (a : ℤ) (m : ℕ) where
  X : C
  Q : C
  p : X ⟶ Q
  α : K.X (a + m) ⟶ X
  β : K.opcycles (a + m) ⟶ Q
  mem : X ∈ 𝓘
  epi : Epi p
  monoα : Mono α
  monoβ : Mono β
  comm : K.pOpcycles (a + m) ≫ β = α ≫ p
attribute [instance] RightResolutionFrontier.epi RightResolutionFrontier.monoα
  RightResolutionFrontier.monoβ
/-- A successor term, its incoming differential and the local pushout witness. -/
private structure RightResolutionExtension
    {K : CochainComplex C ℤ} {𝓘 : Set C} {a : ℤ} {m : ℕ}
    (S : RightResolutionFrontier K 𝓘 a m) where
  next : RightResolutionFrontier K 𝓘 a (m + 1)
  d : S.X ⟶ next.X
  zero : d ≫ next.p = 0
  cokernel : IsColimit (CokernelCofork.ofπ next.p zero)
  square : ∃ (P : C) (u : K.X (a + (m + 1 : ℕ)) ⟶ P)
    (v : S.Q ⟶ P)
    (j : P ⟶ next.X), Mono j ∧
    IsPushout (K.fromOpcycles (a + m) (a + (m + 1 : ℕ))) S.β u v ∧
    u ≫ j = next.α ∧ S.p ≫ v ≫ j = d

/-- The pushout construction and the next mono cokernel map (05T6, dual of 05T7). -/
private noncomputable def RightResolutionFrontier.step
    {K : CochainComplex C ℤ} {𝓘 : Set C} {a : ℤ} {m : ℕ}
    (S : RightResolutionFrontier K 𝓘 a m)
    (hembed : ∀ X : C, ∃ (Y : C) (f : X ⟶ Y), Y ∈ 𝓘 ∧ Mono f) :
    RightResolutionExtension S := by
  classical
  let n := a + (m : ℤ)
  let n' := a + ((m + 1 : ℕ) : ℤ)
  let f := K.fromOpcycles n n'
  let P := pushout f S.β
  let u : K.X n' ⟶ P := pushout.inl f S.β
  let v : S.Q ⟶ P := pushout.inr f S.β
  let Y := (hembed P).choose
  let j : P ⟶ Y := (hembed P).choose_spec.choose
  have hY : Y ∈ 𝓘 := (hembed P).choose_spec.choose_spec.1
  have hj : Mono j := (hembed P).choose_spec.choose_spec.2
  let d := S.p ≫ v ≫ j
  let p := cokernel.π d
  let eI := cokernel.map d (v ≫ j) S.p (𝟙 Y) (by simp [d])
  have : IsIso eI := by dsimp [eI]; infer_instance
  let qK : K.opcycles n' ⟶ cokernel f :=
    K.descOpcycles (cokernel.π f) n (by dsimp [n, n']; simp; omega)
      (by
        rw [← K.p_fromOpcycles n n']
        change (K.pOpcycles (a + m) ≫ f) ≫ cokernel.π f = 0
        rw [Category.assoc, cokernel.condition, comp_zero])
  let qK' : cokernel f ⟶ K.opcycles n' :=
    cokernel.desc f (K.pOpcycles n') (by
      apply (cancel_epi (K.pOpcycles (a + m))).1
      simp [f, n])
  have hqK : qK ≫ qK' = 𝟙 _ := by
    apply (cancel_epi (K.pOpcycles n')).1
    simp [qK, qK']
  have hqK' : qK' ≫ qK = 𝟙 _ := by
    apply (cancel_epi (cokernel.π f)).1
    simp [qK, qK']
  have : IsIso qK := ⟨qK', hqK, hqK'⟩
  let θ := cokernel.map f v S.β u (pushout.condition (f := f) (g := S.β))
  have : IsIso θ := isIso_cokernel_map_of_isPushout (IsPushout.of_hasPushout f S.β)
  let jbar := cokernel.map v (v ≫ j) (𝟙 S.Q) j (by simp)
  have : Mono jbar := Abelian.mono_cokernel_map_of_isPullback
    (IsPullback.of_vert_isIso_mono (by simp))
  let β := qK ≫ θ ≫ jbar ≫ inv eI
  have hpI : cokernel.π (v ≫ j) ≫ inv eI = p := by
    apply (cancel_mono eI).1
    simp [eI, p]
  have : Mono u := by dsimp [u]; infer_instance
  let T : RightResolutionFrontier K 𝓘 a (m + 1) :=
    ⟨Y, cokernel d, p, u ≫ j, β, hY, inferInstance, inferInstance, inferInstance,
      by simp [β, qK, θ, jbar, Category.assoc, hpI, p]⟩
  refine ⟨T, d, cokernel.condition d, cokernelIsCokernel d, ?_⟩
  exact ⟨P, u, v, j, hj, IsPushout.of_hasPushout f S.β, rfl, rfl⟩

/-- Start in degree `a`, whose incoming differential is zero. -/
private noncomputable def RightResolutionFrontier.initial
    (K : CochainComplex C ℤ) (𝓘 : Set C) (a : ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.X n))
    (hembed : ∀ X : C, ∃ (Y : C) (f : X ⟶ Y), Y ∈ 𝓘 ∧ Mono f) :
    RightResolutionFrontier K 𝓘 a 0 := by
  classical
  let n := a + ((0 : ℕ) : ℤ)
  let Y := (hembed (K.X n)).choose
  let α : K.X n ⟶ Y := (hembed (K.X n)).choose_spec.choose
  have hY : Y ∈ 𝓘 := (hembed (K.X n)).choose_spec.choose_spec.1
  have : Mono α := (hembed (K.X n)).choose_spec.choose_spec.2
  have hd : K.d (n - 1) n = 0 := (hK (n - 1) (by dsimp [n]; omega)).eq_of_src _ _
  have : IsIso (K.pOpcycles n) := K.isIso_pOpcycles (n - 1) n (by simp) hd
  exact ⟨Y, Y, 𝟙 Y, α, inv (K.pOpcycles n) ≫ α, hY, inferInstance, inferInstance,
    inferInstance, by
      change K.pOpcycles n ≫ inv (K.pOpcycles n) ≫ α = α ≫ 𝟙 Y
      simp⟩

/-- Iterate the explicit pushout construction. -/
private noncomputable def RightResolutionFrontier.sequence
    {K : CochainComplex C ℤ} {𝓘 : Set C} {a : ℤ}
    (S₀ : RightResolutionFrontier K 𝓘 a 0)
    (hembed : ∀ X : C, ∃ (Y : C) (f : X ⟶ Y), Y ∈ 𝓘 ∧ Mono f) :
    ∀ m : ℕ, RightResolutionFrontier K 𝓘 a m
  | 0 => S₀
  | m + 1 => ((sequence S₀ hembed m).step hembed).next


/-- Construct the terms and differential of the right resolution, together with its local
pushout factorizations. This statement does not assert any cohomology comparison.
Source: Stacks Project, Tag 05T6(1), dual of Tag 05T7(1).
(blueprint: lem-weil-pbc-subcategory-right-resolution-system).

Proof: Start in degree `a` by embedding `K.X a` into an object `X₀` of the subset.
The incoming differential of `K` is zero since `K.X (a - 1)` is zero, so its opcycles
projection is an isomorphism. Take `Q₀ = X₀`, its projection to be the identity, and
the opcycles map to be the inverse of that isomorphism followed by the embedding.
Given the construction through
`n`, push out `K.fromOpcycles n (n + 1)` along the mono map on opcycles. Embed this
pushout `P` into an object of the subset, using the embedding hypothesis. Let the next
augmentation component be the pushout map from `K.X (n + 1)` followed by this embedding,
and let the new differential be the cokernel projection followed by the other pushout
map and the embedding. The pushout identity gives commutation; the cokernel identity
makes successive differentials compose to zero. The next map on opcycles is mono: it
factors as the isomorphism on cokernels across the pushout followed by the mono map on
cokernels induced by the embedding. Thus the induction continues, retaining all earlier
terms and maps. Recursion over the natural numbers `n - a` supplies the terms and local squares.
The separate assembly theorem assembles the complex
and its augmentation. For `n < a - 1`, use zero pushouts and the identity of zero for
the displayed factorization. No cohomology calculation is needed for this construction.
-/
theorem exists_subcategory_right_resolution_system
    (C : Type u) [Category.{v} C] [Abelian C]
    (𝓘 : Set C) (hzero : (0 : C) ∈ 𝓘)
    (hembed : ∀ X : C, ∃ (Y : C) (f : X ⟶ Y), Y ∈ 𝓘 ∧ Mono f)
    (a : ℤ) (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.X n)) :
    ∃ (I : CochainComplex C ℤ) (α : K ⟶ I),
      (∀ n : ℤ, Mono (α.f n)) ∧ (∀ n : ℤ, I.X n ∈ 𝓘) ∧
      (∀ n : ℤ, n < a → IsZero (I.X n)) ∧
      (∀ n : ℤ, Mono (opcyclesMap α n)) ∧
      (∀ n : ℤ, ∃ (P : C) (u : K.X (n + 1) ⟶ P) (v : I.opcycles n ⟶ P)
        (j : P ⟶ I.X (n + 1)), Mono j ∧
        IsPushout (K.fromOpcycles n (n + 1)) (opcyclesMap α n) u v ∧
        u ≫ j = α.f (n + 1) ∧ v ≫ j = I.fromOpcycles n (n + 1)) := by
  classical
  let S₀ := RightResolutionFrontier.initial K 𝓘 a hK hembed
  let S := RightResolutionFrontier.sequence S₀ hembed
  let E := fun m ↦ (S m).step hembed
  have hinit : IsIso (S 0).p := by
    change IsIso (𝟙 S₀.X)
    infer_instance
  exact exists_complex_of_cokernel_pushout_system C 𝓘 hzero a K hK
    (fun m ↦ (S m).X) (fun m ↦ (S m).Q) (fun m ↦ (S m).p)
    (fun m ↦ (S m).α) (fun m ↦ (S m).β)
    (fun m ↦ (S m).mem) (fun m ↦ (S m).epi)
    (fun m ↦ (S m).monoα) (fun m ↦ (S m).monoβ)
    (fun m ↦ (S m).comm) hinit
    (fun m ↦ (E m).d) (fun m ↦ (E m).zero)
    (fun m ↦ (E m).cokernel) (fun m ↦ (E m).square)

end CochainComplex
