/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.AlgebraicGeometry.PrescribedPointSystemData

import WeilConjectures.Mathlib.Topology.Sober
import Mathlib.RingTheory.KrullDimension.Field

/-!
# An open condition of nonzero prescribed jets

Source: blueprint, finite-cover-curve proof, paragraph 2, derivative conditions.
(blueprint: lem-zl-prescribed-point-nonzero-jet-open).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- A closed point in positive pure dimension has nonzero cotangent space;
tensoring with the rank-one invertible stalk preserves this. -/
private theorem jetTarget_nontrivial {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : ℕ) (hd : 0 < d) (hdim : X.IsPureDimension d)
    (M : X.Modules) [M.IsInvertible] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nontrivial (PrescribedPointJet M x) := by
  have hnotfield : ¬ IsField (X.presheaf.stalk x) := by
    intro hfield
    have hc : Order.coheight x = 0 := by
      have h := ringKrullDim_stalk_eq_coheight x
      rw [ringKrullDim_eq_zero_of_isField hfield] at h
      exact_mod_cast h.symm
    have hg : x ∈ genericPoints X := mem_genericPoints_iff_forall_specializes.mpr
      (fun y hy ↦ (hy.antisymm (Scheme.le_iff_specializes.mp
        ((Order.coheight_eq_zero.mp hc) (Scheme.le_iff_specializes.mpr hy)))).eq)
    have hdim0 := hdim (closure {x}) hg
    rw [hx.closure_eq] at hdim0
    have hzero : topologicalKrullDim ({x} : Set X) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [hdim0] at hzero
    have : d ≤ 0 := by exact_mod_cast hzero
    omega
  have : Nontrivial (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) :=
    not_subsingleton_iff_nontrivial.mp
      (fun h ↦ hnotfield (IsLocalRing.subsingleton_cotangentSpace_iff.mp h))
  let e := Classical.choice (invertible_stalk_linearEquiv X M x)
  let e' : PrescribedPointJet M x ≃ₗ[X.presheaf.stalk x]
      IsLocalRing.CotangentSpace (X.presheaf.stalk x) :=
    (TensorProduct.congr (LinearEquiv.refl _ _) e).trans (TensorProduct.rid _ _)
  exact e'.toEquiv.nontrivial

/-- The tensor-pullback unit on global sections is semilinear. -/
private theorem sectionsUnit_smul {X Y : Scheme.{u}} (j : X ⟶ Y) (M : Y.Modules)
    (r : Γ(Y, ⊤)) (v : Γ(M, ⊤)) :
    tensorSectionsUnit j M (r • v) = j.appTop r • tensorSectionsUnit j M v := by
  have hi : homOfLE j.preimage_top.ge = 𝟙 (⊤ : X.Opens) := rfl
  unfold tensorSectionsUnit
  erw [hi, op_id, ((tensorPullback j).obj M).presheaf.map_id, Category.comp_id]
  exact Hom.app_smul _ r v

/-- Coefficient combinations preserve addition. -/
private theorem combination_add {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (M : Y.Modules) {I : Type u} [Fintype I]
    (s : I → Γ(M, ⊤)) (a b : I → k) :
    prescribedPointCombination f M s (a + b) =
      prescribedPointCombination f M s a + prescribedPointCombination f M s b := by
  simp only [prescribedPointCombination, Pi.add_apply, map_add, add_smul,
    Finset.sum_add_distrib]

/-- Coefficient combinations respect scalars pulled back from the field. -/
private theorem combination_smul {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (M : Y.Modules) {I : Type u} [Fintype I]
    (s : I → Γ(M, ⊤)) (b : k) (a : I → k) :
    prescribedPointCombination f M s (b • a) =
      f.appTop ((Scheme.ΓSpecIso (.of k)).inv b) • prescribedPointCombination f M s a := by
  simp only [prescribedPointCombination, Pi.smul_apply, smul_eq_mul, map_mul,
    mul_smul, Finset.smul_sum]

/-- On combinations vanishing at x, the concrete jet construction is linear
for the scalar map from the coefficient field to the stalk. -/
private theorem jet_coefficients_linear {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (j : X ⟶ Y) (M : Y.Modules)
    [((tensorPullback j).obj M).IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(M, ⊤)) (x : X)
    (hvan : ∀ a : I → k, ((tensorPullback j).obj M).presheaf.germ ⊤ x trivial
      (tensorSectionsUnit j M (prescribedPointCombination f M s a)) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x)
            (((tensorPullback j).obj M).presheaf.stalk x))) :
    ∃ ρ : k →+* X.presheaf.stalk x,
      letI : Module k (PrescribedPointJet ((tensorPullback j).obj M) x) :=
        Module.compHom _ ρ
      ∃ L : (I → k) →ₗ[k] PrescribedPointJet ((tensorPullback j).obj M) x,
        ∀ a, L a = prescribedPointJet ((tensorPullback j).obj M) x
          (tensorSectionsUnit j M (prescribedPointCombination f M s a)) := by
  classical
  let N := (tensorPullback j).obj M
  let R := X.presheaf.stalk x
  let e := Classical.choice (invertible_stalk_linearEquiv X N x)
  let σ : k →+* Γ(Y, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let ρ : k →+* R := (X.presheaf.germ ⊤ x trivial).hom.comp (j.appTop.hom.comp σ)
  let c : (I → k) → R := fun a ↦ e (N.presheaf.germ ⊤ x trivial
    (tensorSectionsUnit j M (prescribedPointCombination f M s a)))
  have hc (a : I → k) : c a ∈ IsLocalRing.maximalIdeal R := by
    have h := Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R) e.toLinearMap
      (hvan a)
    change c a ∈ (IsLocalRing.maximalIdeal R • (⊤ : Ideal R) : Ideal R) at h
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using h
  have hadd (a b : I → k) : c (a + b) = c a + c b := by
    simp only [c, combination_add, map_add]
  have hsmul (b : k) (a : I → k) : c (b • a) = ρ b • c a := by
    dsimp only [c]
    rw [combination_smul, sectionsUnit_smul]
    exact (congrArg e (PresheafOfModules.germ_smul N.val x ⊤ trivial
      (j.appTop (σ b)) (tensorSectionsUnit j M (prescribedPointCombination f M s a)))).trans
        (e.map_smul _ _)
  let : Module k (IsLocalRing.maximalIdeal R) := Module.compHom _ ρ
  let : Module k (PrescribedPointJet N x) := Module.compHom _ ρ
  let C : (I → k) →ₗ[k] IsLocalRing.maximalIdeal R :=
    { toFun := fun a ↦ ⟨c a, hc a⟩
      map_add' := fun a b ↦ Subtype.ext (hadd a b)
      map_smul' := fun b a ↦ Subtype.ext (hsmul b a) }
  let T : IsLocalRing.maximalIdeal R →ₗ[R] PrescribedPointJet N x :=
    ((TensorProduct.mk R (IsLocalRing.CotangentSpace R) (N.presheaf.stalk x)).flip
      (e.symm 1)).comp (IsLocalRing.maximalIdeal R).toCotangent
  let T' : IsLocalRing.maximalIdeal R →ₗ[k] PrescribedPointJet N x :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun b a ↦ T.map_smul (ρ b) a }
  refine ⟨ρ, T'.comp C, ?_⟩
  intro a
  change T (C a) = if h : c a ∈ IsLocalRing.maximalIdeal R then
    TensorProduct.tmul R ((IsLocalRing.maximalIdeal R).toCotangent ⟨c a, h⟩) (e.symm 1)
    else 0
  rw [dif_pos (hc a)]
  rfl

/-- A coefficient point lies in D(p) exactly when p evaluates to a nonzero scalar. -/
private theorem coefficient_basicOpen {k : Type u} [Field k] {I : Type u}
    (a : I → k) (p : MvPolynomial I k) (q : Spec (.of k)) :
    bertiniCoefficientPoint (k := k) a q ∈ PrimeSpectrum.basicOpen p ↔
      MvPolynomial.eval a p ≠ 0 := by
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  change MvPolynomial.eval₂Hom (algebraMap k k) a p ∉ q.asIdeal ↔ _
  simp only [hq, Ideal.mem_bot]
  rfl

/-- Simultaneous surjectivity supplies a common nonzero tuple. Detect its entries
by linear functionals and intersect the basic opens of their coefficient polynomials. -/
private theorem linear_nonzero_open {k : Type u} [Field k]
    {I J : Type u} [Finite I] [Finite J]
    (V : J → Type u) [∀ x, AddCommGroup (V x)] [∀ x, Module k (V x)]
    [∀ x, Nontrivial (V x)] (L : ∀ x, (I → k) →ₗ[k] V x)
    (hsurj : Function.Surjective (fun a ↦ fun x ↦ L x a)) :
    ∃ O : (Spec (.of (MvPolynomial I k))).Opens,
      (O : Set (Spec (.of (MvPolynomial I k)))).Nonempty ∧
      ∀ a : I → k, Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (O : Set _) →
        ∀ x, L x a ≠ 0 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose b hb using fun x : J ↦ exists_ne (0 : V x)
  obtain ⟨a₀, ha₀⟩ := hsurj b
  choose ℓ hℓ using fun x : J ↦ Module.Projective.exists_dual_ne_zero k (hb x)
  let F (x : J) : (I → k) →ₗ[k] k := (ℓ x).comp (L x)
  let p (x : J) : MvPolynomial I k :=
    ∑ i, MvPolynomial.C (F x (Pi.single i 1)) * MvPolynomial.X i
  have heval (x : J) (a : I → k) : MvPolynomial.eval a (p x) = F x a := by
    have ha : a = ∑ i, a i • Pi.single i (1 : k) := by
      ext i
      simp [Pi.single_apply]
    conv_rhs => rw [ha]
    simp only [p, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      LinearMap.map_smul, smul_eq_mul, mul_comm]
  let B (x : J) : (Spec (.of (MvPolynomial I k))).Opens := PrimeSpectrum.basicOpen (p x)
  let O : (Spec (.of (MvPolynomial I k))).Opens := ⨅ x, B x
  have hmem (a : I → k) (q : Spec (.of k)) :
      bertiniCoefficientPoint (k := k) a q ∈ O ↔ ∀ x, F x a ≠ 0 := by
    change bertiniCoefficientPoint (k := k) a q ∈
      (O : Set (Spec (.of (MvPolynomial I k)))) ↔ _
    have hcoe : (O : Set (Spec (.of (MvPolynomial I k)))) =
        ⋂ x : J, (B x : Set (Spec (.of (MvPolynomial I k)))) :=
      TopologicalSpace.Opens.coe_iInf B
    rw [hcoe]
    simp only [Set.mem_iInter, SetLike.mem_coe, B]
    apply forall_congr'
    intro x
    exact (coefficient_basicOpen a (p x) q).trans (by rw [heval])
  refine ⟨O, ⟨bertiniCoefficientPoint (k := k) a₀ (⊥ : PrimeSpectrum k), ?_⟩, ?_⟩
  · apply (hmem _ _).mpr
    intro x
    simpa only [F, LinearMap.comp_apply, congrFun ha₀ x] using hℓ x
  · intro a ha x hzero
    have h := (hmem a (⊥ : PrimeSpectrum k)).mp (ha ⟨_, rfl⟩) x
    exact h (by simp only [F, LinearMap.comp_apply, hzero, map_zero])

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Surjectivity of simultaneous jets gives a nonempty coefficient open on which
all prescribed jets are nonzero. No generation or immersion assumption is needed.

Source: blueprint `lem-zl-bertini-finite-cover-curve.proof.md`, paragraph 2;
Stacks Project, Varieties, Tag 0FD6, proof's first-order evaluation calculation.
(blueprint: lem-zl-prescribed-point-nonzero-jet-open).

Proof: A closed point on a locally Noetherian scheme of positive pure dimension
cannot have a field stalk: its coheight would be zero, so it would be a generic
point, and its singleton would be an irreducible component of dimension zero.
Nakayama's lemma in the form of the cotangent-space criterion therefore gives a
nonzero cotangent space. A stalk frame identifies its tensor product with the
invertible stalk with the cotangent space, so every jet target is nonzero.
The ring map from k to each stalk is the composite of the coefficient scalar map,
section pullback and the germ map. Vanishing puts the framed germs in the maximal
ideal. Germs, passage to the cotangent space and tensoring with the frame vector
are linear for this scalar action, making the coefficient-to-jet map k-linear.
Choose a nonzero vector in every target and lift their tuple by surjectivity.
For each target choose a k-linear functional detecting its chosen vector, and
write its composite with the coefficient map as a linear polynomial. The finite
intersection of the basic opens of these polynomials contains the lifted
coefficient point. Every coefficient point in this open has nonzero jet at each
prescribed point. For empty S the intersection is the whole coefficient space.
-/
theorem exists_open_prescribedPoint_nonzeroJets
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : 2 ≤ d) (hdim : X.IsPureDimension d)
    (S : Finset X) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (j : X ⟶ Y)
    (hover : j ≫ f = X ↘ Spec (.of k))
    (M : Y.Modules) [M.IsInvertible] [((tensorPullback j).obj M).IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(M, ⊤))
    (hvan : ∀ a : I → k, prescribedPointVanishes ((tensorPullback j).obj M) S
      (tensorSectionsUnit j M (prescribedPointCombination f M s a)))
    (hjet : Function.Surjective (fun a : I → k ↦ fun x : S ↦
      prescribedPointJet ((tensorPullback j).obj M) x.val
        (tensorSectionsUnit j M (prescribedPointCombination f M s a)))) :
    ∃ O : (Spec (CommRingCat.of (MvPolynomial I k))).Opens,
      (O : Set (Spec (CommRingCat.of (MvPolynomial I k)))).Nonempty ∧
      ∀ a : I → k, Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (O : Set _) →
        ∀ x ∈ S, prescribedPointJet ((tensorPullback j).obj M) x
          (tensorSectionsUnit j M (prescribedPointCombination f M s a)) ≠ 0 := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let V := fun x : S ↦ PrescribedPointJet ((tensorPullback j).obj M) x.val
  let (x : S) : Nontrivial (V x) :=
    jetTarget_nontrivial d (by omega) hdim _ x.val (hclosed x.val x.property)
  have hlin (x : S) := jet_coefficients_linear f j M s x.val
    (fun a ↦ hvan a x.val x.property)
  let ρ := fun x : S ↦ (hlin x).choose
  let (x : S) : Module k (V x) := Module.compHom _ (ρ x)
  let L := fun x : S ↦ (hlin x).choose_spec.choose
  have hL (x : S) (a : I → k) : L x a = prescribedPointJet
      ((tensorPullback j).obj M) x.val
      (tensorSectionsUnit j M (prescribedPointCombination f M s a)) :=
    (hlin x).choose_spec.choose_spec a
  have hsurj : Function.Surjective (fun a ↦ fun x : S ↦ L x a) := by
    intro b
    obtain ⟨a, ha⟩ := hjet b
    exact ⟨a, funext fun x ↦ (hL x a).trans (congrFun ha x)⟩
  obtain ⟨O, hne, hO⟩ := linear_nonzero_open V L hsurj
  refine ⟨O, hne, ?_⟩
  intro a ha x hx hzero
  exact hO a ha ⟨x, hx⟩ ((hL ⟨x, hx⟩ a).trans hzero)

end

end AlgebraicGeometry
