/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Sheaf.Algebra.Module.LocalizedHomogeneousPiece
import Sheaf.Algebra.Module.HomogeneousLocalizationRetraction
import Sheaf.Algebra.Module.LocalizationScalarExtensionCoefficients
import Mathlib.Tactic.Ring

/-!
# Scalar extension of homogeneous localized module pieces

Source: Stacks Project, constructions.tex, Tag 01N2 (lemma-base-change-map-proj),
standard-open calculation, generalized to graded modules by the DAG's agent-supplied
fraction argument; algebra.tex, Tags 07JZ, 00DK and 00D2.
(blueprint: lem-sfb-graded-module-localization-scalar-extension)
-/

@[expose] public section

universe u v w t

open TensorProduct

namespace LocalizedModule

private theorem pow_smul_mem_piece
    {R : Type*} {A : Type*} {M : Type*}
    [CommRing R] [CommRing A] [AddCommGroup M]
    [Module R M] [Module A M]
    (𝓜 : ℤ → Submodule R M) (f : A) (d : ℤ)
    (hshift : ∀ i x, x ∈ 𝓜 i → f • x ∈ 𝓜 (d + i))
    (n : ℕ) (i : ℤ) (x : M) (hx : x ∈ 𝓜 i) :
    f ^ n • x ∈ 𝓜 (i + (n : ℤ) * d) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have h := hshift _ _ ih
    rw [pow_succ', mul_smul]
    have hi : i + ((n + 1 : ℕ) : ℤ) * d = d + (i + (n : ℤ) * d) := by
      push_cast
      ring
    rw [hi]
    exact h

private theorem exists_piece_submodule
    {R : Type*} {A : Type*} {M : Type*}
    [CommRing R] [CommRing A] [AddCommGroup M]
    [Algebra R A] [Module R M] [Module A M] [IsScalarTower R A M]
    (𝓜 : ℤ → Submodule R M) (f : A) (d j : ℤ)
    (hshift : ∀ i x, x ∈ 𝓜 i → f • x ∈ 𝓜 (d + i)) :
    ∃ H : Submodule R (LocalizedModule.Away f M),
      (H : Set (LocalizedModule.Away f M)) =
        homogeneousPieceAway (fun i ↦ (𝓜 i).toAddSubgroup) f d j := by
  refine ⟨{ carrier := homogeneousPieceAway (fun i ↦ (𝓜 i).toAddSubgroup) f d j
            zero_mem' := ?_
            add_mem' := ?_
            smul_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨m, x, hx, rfl⟩ ⟨n, y, hy, rfl⟩
    refine ⟨m + n, f ^ n • x + f ^ m • y, ?_, ?_⟩
    · apply (𝓜 _).add_mem
      · have hi : j + ((m + n : ℕ) : ℤ) * d = (j + (m : ℤ) * d) + (n : ℤ) * d := by
          push_cast
          ring
        rw [hi]
        exact pow_smul_mem_piece 𝓜 f d hshift n _ x hx
      · have hi : j + ((m + n : ℕ) : ℤ) * d = (j + (n : ℤ) * d) + (m : ℤ) * d := by
          push_cast
          ring
        rw [hi]
        exact pow_smul_mem_piece 𝓜 f d hshift m _ y hy
    · rw [mk_add_mk]
      congr 1
      apply Subtype.ext
      exact pow_add f m n
  · exact ⟨0, 0, (𝓜 _).zero_mem, zero_mk _⟩
  · rintro r _ ⟨m, x, hx, rfl⟩
    exact ⟨m, r • x, (𝓜 _).smul_mem r hx, (smul'_mk r x _).symm⟩

/-- Coefficient extension commutes with every homogeneous localized module piece.
The action on `S ⊗[R] M` is the scalar extension of the action of `A` on `M`,
extended to `S ⊗[R] A`; on pure tensors it is `(s ⊗ a) • (t ⊗ x) = st ⊗ (a • x)`.
The submodules `H` and `K` have exactly the existing homogeneous-fraction sets as
carriers, so their operations are inherited from ordinary module localization.
The equality on fractions specifies the comparison, including its normalization.

Source: Stacks Project, constructions.tex, Tag 01N2 (lemma-base-change-map-proj),
proof on standard opens, with the agent-supplied arbitrary graded-module refinement
in the DAG; algebra.tex, Tags 07JZ (module fractions), 00DK and 00D2 (tensor localization).
(blueprint: lem-sfb-graded-module-localization-scalar-extension)

Proof: Construct both homogeneous submodules by common-denominator addition. The
homogeneous localization retraction makes H → M_f split, hence S⊗H → S⊗M_f is
injective without flatness. Ordinary localization commutes with coefficient
extension; restrict that ambient equivalence to S⊗H. Its fraction formula shows
that the image lies in K. Every numerator in a base-changed homogeneous piece
lifts to a tensor of homogeneous numerators. Tensor induction, with fractions
of a fixed denominator, proves surjectivity. The restricted map is therefore
bijective, and retains the ambient comparison's normalized fraction formula. -/
theorem exists_gradedLocalization_scalarExtension_equiv
    {R : Type u} {S : Type v} {A : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing A] [AddCommGroup M]
    [Algebra R S] [Algebra R A] [Module R M] [Module A M] [IsScalarTower R A M]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule R M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (i : ℤ) (a : A) (x : M),
      a ∈ 𝒜 n → x ∈ 𝓜 i → a • x ∈ 𝓜 ((n : ℤ) + i))
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) (j : ℤ) :
    let ρ : (S ⊗[R] A) →ₐ[S] Module.End S (S ⊗[R] M) :=
      AlgHom.liftEquiv R S A _
        ((Module.End.baseChangeHom R S M).comp (Algebra.lsmul R R M))
    letI : Module (S ⊗[R] A) (S ⊗[R] M) := Module.compHom _ ρ.toRingHom
    letI : IsScalarTower S (S ⊗[R] A) (S ⊗[R] M) :=
      IsScalarTower.of_algebraMap_smul
        (fun s x ↦ congrArg (fun g : Module.End S (S ⊗[R] M) ↦ g x) (ρ.commutes s))
    ∃ (H : Submodule R (LocalizedModule.Away f M))
      (K : Submodule S (LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M))),
      (H : Set (LocalizedModule.Away f M)) =
        homogeneousPieceAway (fun i ↦ (𝓜 i).toAddSubgroup) f (d : ℤ) j ∧
      (K : Set (LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M))) =
        homogeneousPieceAway (fun i ↦ ((𝓜 i).baseChange S).toAddSubgroup)
          (1 ⊗ₜ[R] f : S ⊗[R] A) (d : ℤ) j ∧
      ∃ e : (S ⊗[R] H) ≃ₗ[S] K,
        ∀ (s : S) (m : ℕ) (x : M), x ∈ 𝓜 (j + (m : ℤ) * (d : ℤ)) →
          ∀ z : H, (z : LocalizedModule.Away f M) =
            mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          (e (s ⊗ₜ[R] z) :
            LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M)) =
            mk (s ⊗ₜ[R] x)
              (⟨(1 ⊗ₜ[R] f : S ⊗[R] A) ^ m, ⟨m, rfl⟩⟩ :
                Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A)) := by
  have _ := hd
  dsimp only
  let ρ : (S ⊗[R] A) →ₐ[S] Module.End S (S ⊗[R] M) :=
    AlgHom.liftEquiv R S A _
      ((Module.End.baseChangeHom R S M).comp (Algebra.lsmul R R M))
  let : Module (S ⊗[R] A) (S ⊗[R] M) := Module.compHom _ ρ.toRingHom
  let : IsScalarTower S (S ⊗[R] A) (S ⊗[R] M) :=
    IsScalarTower.of_algebraMap_smul
      (fun s x ↦ congrArg (fun g : Module.End S (S ⊗[R] M) ↦ g x) (ρ.commutes s))
  have hshift : ∀ i x, x ∈ 𝓜 i → f • x ∈ 𝓜 ((d : ℤ) + i) :=
    fun i x hx ↦ hsmul d i f x hf hx
  obtain ⟨H, hH⟩ := exists_piece_submodule 𝓜 f (d : ℤ) j hshift
  obtain ⟨p, hp⟩ := exists_homogeneousPieceAway_retraction 𝒜 𝓜 h𝓜 hsmul hf j H hH
  obtain ⟨e, he⟩ := exists_localization_scalarExtension_coefficients_equiv
    (R := R) (S := S) (M := M) f
  have hact (s : S) (x : M) :
      (1 ⊗ₜ[R] f : S ⊗[R] A) • (s ⊗ₜ[R] x) = s ⊗ₜ[R] (f • x) := by
    change (ρ (1 ⊗ₜ[R] f)) (s ⊗ₜ[R] x) = _
    simp only [ρ, AlgHom.liftEquiv_tmul, one_smul, AlgHom.comp_apply]
    exact LinearMap.baseChange_tmul (A := S) (f := Algebra.lsmul R R M f) s x
  have hshiftS : ∀ i x, x ∈ (𝓜 i).baseChange S →
      (1 ⊗ₜ[R] f : S ⊗[R] A) • x ∈ (𝓜 ((d : ℤ) + i)).baseChange S := by
    intro i x hx
    obtain ⟨x, rfl⟩ := hx
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      change (1 ⊗ₜ[R] f : S ⊗[R] A) • (s ⊗ₜ[R] (x : M)) ∈ _
      rw [hact]
      exact Submodule.tmul_mem_baseChange_of_mem s (hshift i x x.property)
    | add x y hx hy => simpa only [map_add, smul_add] using (Submodule.add_mem _ hx hy)
  obtain ⟨K, hK⟩ := exists_piece_submodule
    (fun i ↦ (𝓜 i).baseChange S) (1 ⊗ₜ[R] f : S ⊗[R] A) (d : ℤ) j hshiftS
  let g : (S ⊗[R] H) →ₗ[S]
      LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M) :=
    e.toLinearMap.comp (H.subtype.baseChange S)
  have hg : ∀ y, g y ∈ K := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s z =>
      have hz : (z : LocalizedModule.Away f M) ∈
          homogeneousPieceAway (fun i ↦ (𝓜 i).toAddSubgroup) f (d : ℤ) j := by
        rw [← hH]
        exact z.property
      obtain ⟨m, x, hx, hz⟩ := hz
      change g (s ⊗ₜ[R] z) ∈ (K : Set _)
      rw [hK]
      refine ⟨m, s ⊗ₜ[R] x, Submodule.tmul_mem_baseChange_of_mem s hx, ?_⟩
      change _ = e (s ⊗ₜ[R] (z : LocalizedModule.Away f M))
      rw [← hz, he]
    | add x y hx hy => simpa only [map_add] using K.add_mem hx hy
  let g' : (S ⊗[R] H) →ₗ[S] K := g.codRestrict K hg
  have hinj : Function.Injective g' := by
    intro x y hxy
    have hxy' : H.subtype.baseChange S x = H.subtype.baseChange S y :=
      e.injective (congrArg Subtype.val hxy)
    have hleft : (p.baseChange S).comp (H.subtype.baseChange S) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hp, LinearMap.baseChange_id]
    simpa only [← LinearMap.comp_apply, hleft, LinearMap.id_apply] using
      congrArg (p.baseChange S) hxy'
  have hsurj : Function.Surjective g' := by
    intro z
    have hz : (z : LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M)) ∈
        homogeneousPieceAway (fun i ↦ ((𝓜 i).baseChange S).toAddSubgroup)
          (1 ⊗ₜ[R] f : S ⊗[R] A) (d : ℤ) j := by
      rw [← hK]
      exact z.property
    obtain ⟨m, y, hy, hz⟩ := hz
    obtain ⟨y, rfl⟩ := hy
    have hpre : ∀ y : S ⊗[R] 𝓜 (j + (m : ℤ) * (d : ℤ)),
        ∃ w : S ⊗[R] H, g w =
          mk ((𝓜 (j + (m : ℤ) * (d : ℤ))).subtype.baseChange S y)
            (⟨(1 ⊗ₜ[R] f : S ⊗[R] A) ^ m, ⟨m, rfl⟩⟩ :
              Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp [g]⟩
      | tmul s x =>
        have hx : mk (x : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ∈ H := by
          change _ ∈ (H : Set (LocalizedModule.Away f M))
          rw [hH]
          exact ⟨m, x, x.property, rfl⟩
        refine ⟨s ⊗ₜ[R] ⟨_, hx⟩, ?_⟩
        exact he s m x
      | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        refine ⟨a + b, ?_⟩
        rw [map_add, ha, hb, map_add]
        rw [mk_add_mk, ← smul_add, mk_cancel_common_left]
    obtain ⟨w, hw⟩ := hpre y
    refine ⟨w, Subtype.ext ?_⟩
    exact hw.trans hz
  refine ⟨H, K, hH, hK, LinearEquiv.ofBijective g' ⟨hinj, hsurj⟩, ?_⟩
  intro s m x _ z hz
  change e (s ⊗ₜ[R] (z : LocalizedModule.Away f M)) = _
  rw [hz, he]

end LocalizedModule
