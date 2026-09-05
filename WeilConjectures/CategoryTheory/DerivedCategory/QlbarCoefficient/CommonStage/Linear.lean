/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.QlbarCoefficient.CommonStage.Preadditive

/-!
# The linear structure on the common-stage category

Let `K` be a commutative ring which is the filtered union of a monotone family of subrings
`k i`, indexed by the same preorder `I` as a transition system `S`, and suppose that each
`C i` is `k i`-linear and that every transition functor `T j/i` is *semilinear* for the
inclusion `k i ⊆ k j`. Then the common-stage category is `K`-linear: a scalar `α : K`
already lives in some `k i`, so `α • f` may be computed at any stage lying over both `i`
and a stage of definition of `f`.

The semilinearity condition `T j/i (a • u) = a • T j/i u` is *not* recorded in the
reference notes, but without it the scalar multiplication is not well defined: two
representatives of the same morphism, taken at different stages, would give different
answers.

In the intended application `K = ℚ̄_ℓ`, the index `I` is the poset of finite subextensions
`E` of `ℚ̄_ℓ / ℚ_ℓ`, `k E = E`, and `C E = Dᵇ_c(Y, E)`. Every element of `ℚ̄_ℓ` is algebraic
over `ℚ_ℓ`, hence lies in a finite subextension: this is exactly `ScalarSystem.exists_mem`.

## Main definitions

- `CategoryTheory.TransitionSystem.ScalarSystem`: the coefficient rings `k i ⊆ K` and the
  `k i`-linear structures on the `C i`.
- `CategoryTheory.TransitionSystem.IsLinear`: semilinearity of the transition functors.
- `CategoryTheory.TransitionSystem.CommonStage.smulHom`: the action of `K` on morphisms.
- `CategoryTheory.TransitionSystem.CommonStage.linear`: the `Linear K` instance on the
  common-stage category.
-/

@[expose] public section

universe uK w v u

namespace CategoryTheory

open Category

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  [∀ i, Preadditive (C i)]

/-- A system of coefficient rings for a transition system: a monotone family of subrings
`k i` of `K` whose union is all of `K`, together with `k i`-linear structures on the
categories `C i`. -/
class TransitionSystem.ScalarSystem (S : TransitionSystem C) (K : Type uK) [CommRing K] where
  /-- The subring of scalars available at the stage `i`. -/
  k : I → Subring K
  /-- The family of coefficient rings is monotone. -/
  mono : Monotone k
  /-- Every scalar of `K` is already defined at some stage. -/
  exists_mem (α : K) : ∃ i, α ∈ k i
  /-- The category at the stage `i` is `k i`-linear. -/
  linear (i : I) : Linear (k i) (C i)

attribute [instance_reducible, instance] TransitionSystem.ScalarSystem.linear

namespace TransitionSystem.ScalarSystem

variable (S : TransitionSystem C) (K : Type uK) [CommRing K] [ScalarSystem S K]

/-- The subring of scalars available at the stage `i`. -/
abbrev scalars (i : I) : Subring K := k (S := S) (K := K) i

lemma scalars_mono : Monotone (scalars S K) := mono (S := S) (K := K)

lemma exists_mem_scalars (α : K) : ∃ i, α ∈ scalars S K i := exists_mem (S := S) (K := K) α

/-- The inclusion of scalars `k i → k j` attached to `i ≤ j`. -/
def incl {i j : I} (h : i ≤ j) (a : scalars S K i) : scalars S K j :=
  ⟨(a : K), scalars_mono S K h a.2⟩

@[simp]
lemma coe_incl {i j : I} (h : i ≤ j) (a : scalars S K i) :
    ((incl S K h a : scalars S K j) : K) = a := rfl

/-- A chosen stage at which the scalar `α` is defined. -/
noncomputable def stageOf (α : K) : I := (exists_mem_scalars S K α).choose

lemma mem_stageOf (α : K) : α ∈ scalars S K (stageOf S K α) :=
  (exists_mem_scalars S K α).choose_spec

/-- The scalar `α : K` regarded as an element of `k p`, for any stage `p` above the chosen
stage of definition of `α`. -/
def scalarAt (α : K) {p : I} (h : stageOf S K α ≤ p) : scalars S K p :=
  ⟨α, scalars_mono S K h (mem_stageOf S K α)⟩

@[simp]
lemma coe_scalarAt (α : K) {p : I} (h : stageOf S K α ≤ p) :
    ((scalarAt S K α h : scalars S K p) : K) = α := rfl

end TransitionSystem.ScalarSystem

open TransitionSystem.ScalarSystem in
/-- A transition system equipped with a scalar system is *linear* if every transition
functor is semilinear for the inclusion of scalars `k i ⊆ k j`. -/
class TransitionSystem.IsLinear (S : TransitionSystem C) (K : Type uK) [CommRing K]
    [TransitionSystem.ScalarSystem S K] : Prop where
  /-- The transition functors are semilinear. -/
  map_smul {i j : I} (h : i ≤ j) {X Y : C i} (a : scalars S K i) (u : X ⟶ Y) :
    (S.T h).map (a • u) = incl S K h a • (S.T h).map u

namespace TransitionSystem.CommonStage

open TransitionSystem.ScalarSystem

variable {S : TransitionSystem C} (K : Type uK) [CommRing K] [S.ScalarSystem K]
  {X Y Z : CommonStage S} {p q : I}

section

variable [S.IsLinear K]

@[simp]
lemma transport_smul {hX : X.stage ≤ p} {hY : Y.stage ≤ p} (hpq : p ≤ q) (a : scalars S K p)
    (u : X.extend hX ⟶ Y.extend hY) :
    transport hpq (a • u) = incl S K hpq a • transport hpq u := by
  simp [transport, TransitionSystem.IsLinear.map_smul (S := S) (K := K)]

end

variable [S.IsAdditive] [IsDirectedOrder I]

omit [S.IsAdditive] in
/-- Any two scalars and a morphism can be brought to one common stage. -/
lemma exists_stage₂ (α β : K) (f : X ⟶ Y) :
    ∃ (p : I) (_ : stageOf S K α ≤ p) (_ : stageOf S K β ≤ p) (hX : X.stage ≤ p)
      (hY : Y.stage ≤ p) (u : X.extend hX ⟶ Y.extend hY), f = homMk hX hY u := by
  obtain ⟨q, hX, hY, u, rfl⟩ := exists_homMk f
  obtain ⟨s, hs₁, hs₂⟩ := exists_ge_ge (stageOf S K α) (stageOf S K β)
  obtain ⟨p, hp₁, hp₂⟩ := exists_ge_ge s q
  exact ⟨p, hs₁.trans hp₁, hs₂.trans hp₁, hX.trans hp₂, hY.trans hp₂, transport hp₂ u,
    (homMk_transport _ _ hp₂ u).symm⟩

omit [S.IsAdditive] in
/-- A scalar and a morphism can be brought to one common stage. -/
lemma exists_stage₁ (α : K) (f : X ⟶ Y) :
    ∃ (p : I) (_ : stageOf S K α ≤ p) (hX : X.stage ≤ p) (hY : Y.stage ≤ p)
      (u : X.extend hX ⟶ Y.extend hY), f = homMk hX hY u := by
  obtain ⟨p, hα, _, hX, hY, u, hu⟩ := exists_stage₂ K α α f
  exact ⟨p, hα, hX, hY, u, hu⟩

variable [S.IsLinear K]

omit [S.IsAdditive] in
/-- Multiplication of a morphism of the common-stage category by a scalar of `K`,
computed at any stage lying over a stage of definition of the morphism and over a stage at
which the scalar is defined. -/
noncomputable def smulHom (α : K) (f : X ⟶ Y) : X ⟶ Y :=
  Quotient.liftOn (f : Hom X Y)
    (fun u ↦ homMk (u.leLeft.trans (le_ub_right (stageOf S K α) u.stage))
      (u.leRight.trans (le_ub_right (stageOf S K α) u.stage))
      (scalarAt S K α (le_ub_left (stageOf S K α) u.stage) •
        transport (le_ub_right (stageOf S K α) u.stage) u.hom))
    (fun u u' h ↦ by
      obtain ⟨r₀, hr₀, hr₀'⟩ := exists_ge_ge (ub I (stageOf S K α) u.stage)
        (ub I (stageOf S K α) u'.stage)
      obtain ⟨r, hr, e⟩ := h.exists_ge
        ((le_ub_right (stageOf S K α) u.stage).trans hr₀)
        ((le_ub_right (stageOf S K α) u'.stage).trans hr₀')
      rw [← homMk_transport _ _ (hr₀.trans hr), ← homMk_transport _ _ (hr₀'.trans hr),
        transport_smul K, transport_smul K]
      simp only [transport_transport]
      rw [e]
      rfl)

omit [S.IsAdditive] in
lemma smulHom_homMk (α : K) (hs : stageOf S K α ≤ p) (hX : X.stage ≤ p) (hY : Y.stage ≤ p)
    (u : X.extend hX ⟶ Y.extend hY) :
    smulHom K α (homMk hX hY u) = homMk hX hY (scalarAt S K α hs • u) := by
  have h : smulHom K α (homMk hX hY u) =
      homMk (hX.trans (le_ub_right (stageOf S K α) p))
        (hY.trans (le_ub_right (stageOf S K α) p))
        (scalarAt S K α (le_ub_left (stageOf S K α) p) •
          transport (le_ub_right (stageOf S K α) p) u) := rfl
  rw [h, ← homMk_transport hX hY (le_ub_right (stageOf S K α) p), transport_smul K]
  rfl

noncomputable instance homModule (X Y : CommonStage S) : Module K (X ⟶ Y) :=
  letI : SMul K (X ⟶ Y) := ⟨smulHom K⟩
  { smul := (· • ·)
    one_smul := fun f ↦ by
      obtain ⟨p, h₁, hX, hY, u, rfl⟩ := exists_stage₁ K (1 : K) f
      change smulHom K (1 : K) _ = _
      rw [smulHom_homMk K (1 : K) h₁]
      congr 1
      rw [show scalarAt S K (1 : K) h₁ = 1 from rfl]
      exact one_smul _ u
    mul_smul := fun α β f ↦ by
      obtain ⟨p, hα, hβ, hX, hY, u, rfl⟩ := exists_stage₂ K α β f
      obtain ⟨q, hq₁, hq₂⟩ := exists_ge_ge (stageOf S K (α * β)) p
      rw [← homMk_transport hX hY hq₂ u]
      change smulHom K (α * β) _ = smulHom K α (smulHom K β _)
      rw [smulHom_homMk K (α * β) hq₁, smulHom_homMk K β (hβ.trans hq₂),
        smulHom_homMk K α (hα.trans hq₂)]
      congr 1
      rw [← mul_smul]
      rfl
    smul_zero := fun α ↦ by
      obtain ⟨p, hα, hX, hY, u, _⟩ := exists_stage₁ K α (0 : X ⟶ Y)
      change smulHom K α (0 : X ⟶ Y) = 0
      rw [show (0 : X ⟶ Y) = homMk hX hY (0 : X.extend hX ⟶ Y.extend hY) from
        (homMk_zero hX hY).symm, smulHom_homMk K α hα, smul_zero, homMk_zero]
    smul_add := fun α f g ↦ by
      obtain ⟨p₀, hα, hX₀, hY₀, u₀, rfl⟩ := exists_stage₁ K α f
      obtain ⟨p₁, hX₁, hY₁, u₁, rfl⟩ := exists_homMk g
      obtain ⟨p, hp₀, hp₁⟩ := exists_ge_ge p₀ p₁
      rw [← homMk_transport hX₀ hY₀ hp₀ u₀, ← homMk_transport hX₁ hY₁ hp₁ u₁]
      change smulHom K α (_ + _) = smulHom K α _ + smulHom K α _
      rw [homMk_add, smulHom_homMk K α (hα.trans hp₀), smulHom_homMk K α (hα.trans hp₀),
        smulHom_homMk K α (hα.trans hp₀), homMk_add, smul_add]
    add_smul := fun α β f ↦ by
      obtain ⟨p, hα, hβ, hX, hY, u, rfl⟩ := exists_stage₂ K α β f
      obtain ⟨q, hq₁, hq₂⟩ := exists_ge_ge (stageOf S K (α + β)) p
      rw [← homMk_transport hX hY hq₂ u]
      change smulHom K (α + β) _ = smulHom K α _ + smulHom K β _
      rw [smulHom_homMk K (α + β) hq₁, smulHom_homMk K α (hα.trans hq₂),
        smulHom_homMk K β (hβ.trans hq₂), homMk_add]
      congr 1
      rw [← add_smul]
      rfl
    zero_smul := fun f ↦ by
      obtain ⟨p, h₀, hX, hY, u, rfl⟩ := exists_stage₁ K (0 : K) f
      change smulHom K (0 : K) _ = 0
      rw [smulHom_homMk K (0 : K) h₀, show scalarAt S K (0 : K) h₀ = 0 from rfl, zero_smul,
        homMk_zero] }

@[simp]
lemma homMk_smul (α : K) (hs : stageOf S K α ≤ p) (hX : X.stage ≤ p) (hY : Y.stage ≤ p)
    (u : X.extend hX ⟶ Y.extend hY) :
    α • homMk hX hY u = homMk hX hY (scalarAt S K α hs • u) :=
  smulHom_homMk K α hs hX hY u

/-- The common-stage category is `K`-linear: every scalar of `K`, being defined at some
finite stage, acts on morphisms through the linear structure at a large enough stage. -/
noncomputable instance linear : Linear K (CommonStage S) where
  homModule := homModule K
  smul_comp X Y Z α f g := by
    obtain ⟨p₀, hα, hX, hY, u, rfl⟩ := exists_stage₁ K α f
    obtain ⟨p₁, hY', hZ, v, rfl⟩ := exists_homMk g
    obtain ⟨p, hp₀, hp₁⟩ := exists_ge_ge p₀ p₁
    rw [← homMk_transport hX hY hp₀ u, ← homMk_transport hY' hZ hp₁ v,
      homMk_smul K α (hα.trans hp₀), homMk_comp_homMk, homMk_comp_homMk,
      homMk_smul K α (hα.trans hp₀), Linear.smul_comp]
  comp_smul X Y Z f α g := by
    obtain ⟨p₀, hα, hY', hZ, v, rfl⟩ := exists_stage₁ K α g
    obtain ⟨p₁, hX, hY, u, rfl⟩ := exists_homMk f
    obtain ⟨p, hp₀, hp₁⟩ := exists_ge_ge p₀ p₁
    rw [← homMk_transport hY' hZ hp₀ v, ← homMk_transport hX hY hp₁ u,
      homMk_smul K α (hα.trans hp₀), homMk_comp_homMk, homMk_comp_homMk,
      homMk_smul K α (hα.trans hp₀), Linear.comp_smul]

end TransitionSystem.CommonStage

end CategoryTheory
