/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SegreTwist

/-!
# Very ample and ample invertible modules

An `𝒪_X`-module is *very ample* relative to `f : X ⟶ S` if it is the pullback of `𝒪(1)` along
a closed immersion of `X` into a projective space `ℙ(n; S)` over `S`; it is then invertible. An
invertible module on a `K`-scheme is *ample* if some positive tensor power of it is very ample;
since very ample modules come from *closed* immersions into projective space, this is ampleness
on a projective `K`-scheme (see the warning in the docstring of `AlgebraicGeometry.IsAmple`).

The Hilbert polynomial and the degree with respect to an ample module are in
`WeilConjectures/AlgebraicGeometry/Modules/Ample.lean`.

## Main definitions

- `AlgebraicGeometry.IsVeryAmple`, `AlgebraicGeometry.IsAmple`: very ample and ample modules.

## Main statements

- `AlgebraicGeometry.IsVeryAmple.isInvertible`: a very ample module is invertible.
- `AlgebraicGeometry.IsVeryAmple.tensorObj`, `AlgebraicGeometry.IsAmple.tensorObj`: tensor
  products of very ample, respectively ample, modules are very ample, respectively ample.
- `AlgebraicGeometry.IsAmple.tensorPow`: positive tensor powers of an ample module are ample.
- `AlgebraicGeometry.IsAmple.pullback`: the restriction of an ample module to a closed subscheme
  is ample.
- `AlgebraicGeometry.IsVeryAmple.pullback_of_field`, `AlgebraicGeometry.IsAmple.pullback_of_field`:
  very ampleness and ampleness are stable under field extension.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An `𝒪_X`-module `M` is *very ample* relative to `f : X ⟶ S` if there is a closed immersion
`i : X ⟶ ℙ(n; S)` over `S`, into a projective space with finitely many homogeneous
coordinates, with `i^* 𝒪(1) ≅ M`.

This is the "projective" variant of the notion: Hartshorne (II.5) and EGA II (4.4.2) only ask
for an immersion. The two agree when `f` is proper, since an immersion from a proper
`S`-scheme into the separated `S`-scheme `ℙ(n; S)` is closed, and every use of very ample
modules in the project is for a proper `f`.

This is the very ample part of blueprint `def-sc-ample` (with `S = Spec k`). -/
def IsVeryAmple {S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∃ (n : Type u) (i : X ⟶ ℙ(n; S)), Finite n ∧ IsClosedImmersion i ∧ i ≫ ℙ(n; S) ↘ S = f ∧
    Nonempty (ProjectiveSpace.twistRestrict i 1 ≅ M)

/-- **A very ample module is invertible**, being the pullback of the invertible module
`𝒪(1)`. -/
lemma IsVeryAmple.isInvertible {S : Scheme.{u}} {f : X ⟶ S} {M : X.Modules}
    (h : IsVeryAmple f M) : M.IsInvertible := by
  obtain ⟨n, i, -, -, -, ⟨e⟩⟩ := h
  exact Scheme.Modules.IsInvertible.of_iso e

/-- Very ampleness only depends on the isomorphism class of the module. -/
lemma IsVeryAmple.of_iso {S : Scheme.{u}} {f : X ⟶ S} {M N : X.Modules} (h : IsVeryAmple f M)
    (e : M ≅ N) : IsVeryAmple f N := by
  obtain ⟨n, i, hn, hi, hif, ⟨e'⟩⟩ := h
  exact ⟨n, i, hn, hi, hif, ⟨e' ≪≫ e⟩⟩

/-- **The restriction of a very ample module to a closed subscheme is very ample**: if `M` is
the pullback of `𝒪(1)` along a closed immersion `i`, then `g^* M` is its pullback along the
closed immersion `g ≫ i`. -/
lemma IsVeryAmple.pullback {S Z : Scheme.{u}} {f : X ⟶ S} {M : X.Modules} (h : IsVeryAmple f M)
    (g : Z ⟶ X) [IsClosedImmersion g] :
    IsVeryAmple (g ≫ f) ((Scheme.Modules.pullback g).obj M) := by
  obtain ⟨n, i, hn, hi, hif, ⟨e⟩⟩ := h
  exact ⟨n, g ≫ i, hn, inferInstance, by rw [Category.assoc, hif],
    ⟨(Scheme.Modules.pullbackComp g i).symm.app _ ≪≫ (Scheme.Modules.pullback g).mapIso e⟩⟩

/-- Blueprint `lem-chow-segre`: The Segre embedding is a closed immersion (the consequence that
`𝒪(1) ⊠ 𝒪(1)` is very ample, recorded in its detailed form).

**A tensor product of very ample modules is very ample.** If `M = i^* 𝒪(1)` and `N = j^* 𝒪(1)`
for closed immersions `i : X ⟶ ℙ(n; S)` and `j : X ⟶ ℙ(m; S)` over `S`, then `M ⊗ N` is the
pullback of `𝒪(1)` along the composite of the closed immersion `(i, j)` into
`ℙ(n; S) ×_S ℙ(m; S)` with the Segre embedding into `ℙ(n × m; S)`. -/
theorem IsVeryAmple.tensorObj {S : Scheme.{u}} {f : X ⟶ S} {M N : X.Modules}
    (hM : IsVeryAmple f M) (hN : IsVeryAmple f N) : IsVeryAmple f (M ⊗ N) := by
  obtain ⟨n, i, hn, hi, hif, ⟨e⟩⟩ := hM
  obtain ⟨m, j, hm, hj, hjf, ⟨e'⟩⟩ := hN
  let k : X ⟶ Limits.pullback (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) := pullback.lift i j (hif.trans hjf.symm)
  have : IsClosedImmersion (k ≫ pullback.fst _ _) := by rwa [pullback.lift_fst]
  have : IsClosedImmersion k := IsClosedImmersion.of_comp k (pullback.fst _ _)
  obtain ⟨t⟩ := ProjectiveSpace.nonempty_twistRestrict_segre_iso n m S
  obtain ⟨u⟩ := Scheme.Modules.nonempty_pullback_tensorObj_iso k
    (ProjectiveSpace.twistRestrict (pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)) 1)
    (ProjectiveSpace.twistRestrict (pullback.snd (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)) 1)
  refine ⟨n × m, k ≫ ProjectiveSpace.segre n m S, inferInstance, inferInstance,
    by simp [k, hif], ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp k _).symm.app _ ≪≫ (Scheme.Modules.pullback k).mapIso t ≪≫
    u ≪≫ (((Scheme.Modules.pullbackComp k _).app _ ≪≫
        (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app _ ≪≫ e) ⊗ᵢ
      ((Scheme.Modules.pullbackComp k _).app _ ≪≫
        (Scheme.Modules.pullbackCongr (pullback.lift_snd _ _ _)).app _ ≪≫ e'))

/-- **Positive tensor powers of a very ample module are very ample**, by
`AlgebraicGeometry.IsVeryAmple.tensorObj`. -/
theorem IsVeryAmple.tensorPow {S : Scheme.{u}} {f : X ⟶ S} {M : X.Modules}
    (hM : IsVeryAmple f M) : ∀ {k : ℕ}, 0 < k → IsVeryAmple f (M.tensorPow k)
  | 1, _ => hM.of_iso (ρ_ M).symm
  | k + 2, _ => hM.tensorObj (hM.tensorPow (Nat.succ_pos k))

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An `𝒪_X`-module `M` on a `K`-scheme `X` is *ample* if it is invertible and some positive tensor
power of it is very ample in the sense of `AlgebraicGeometry.IsVeryAmple`.

**Warning.** `AlgebraicGeometry.IsVeryAmple` asks for a *closed* immersion into a projective
space, so `IsAmple f M` means "`M` is ample and `X` is projective over `K`". It is the standard
notion (EGA II 4.5.3, Stacks `01PS`) when `f` is proper, which is the only case in which the
blueprint uses it, but an ample module on a non-proper `K`-scheme, such as `𝒪` on `𝔸¹_K`, does
not satisfy `IsAmple`. Statements such as Serre vanishing
(`AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensorObj_tensorPow`) hold without a
properness hypothesis for this reason.

This is also blueprint `def-sc-ample` and, as recorded in blueprint `rem-pc-sc-ample`, it is
used in its stated generality, for any proper scheme over a field. -/
def IsAmple (f : X ⟶ Spec (.of K)) (M : X.Modules) : Prop :=
  M.IsInvertible ∧ ∃ m : ℕ, 0 < m ∧ IsVeryAmple f (M.tensorPow m)

/-- An ample module is invertible. -/
lemma IsAmple.isInvertible {f : X ⟶ Spec (.of K)} {M : X.Modules} (h : IsAmple f M) :
    M.IsInvertible :=
  h.1

/-- **The restriction of an ample module to a closed subscheme is ample.** If `L^{⊗ n}` is the
pullback of `𝒪(1)` along a closed immersion `X ⟶ ℙ(m; K)`, then `(i^* L)^{⊗ n} ≅ i^* (L^{⊗ n})`
is its pullback along the closed immersion `Z ⟶ X ⟶ ℙ(m; K)` (Stacks, Properties of Schemes,
Section 28.26).

This is used in the proof of blueprint `lem-sc-ample-positive-degree`. -/
theorem IsAmple.pullback {Z : Scheme.{u}} {f : X ⟶ Spec (.of K)} {L : X.Modules}
    (hL : IsAmple f L) (i : Z ⟶ X) [IsClosedImmersion i] :
    IsAmple (i ≫ f) ((Scheme.Modules.pullback i).obj L) := by
  obtain ⟨hinv, m, hm, h⟩ := hL
  exact ⟨inferInstance, m, hm, (h.pullback i).of_iso
    (Scheme.Modules.nonempty_pullback_tensorPow_iso i L m).some⟩

/-- **Positive tensor powers of an ample module are ample.** If `L^{⊗ m}` is very ample, then
so is `(L^{⊗ m})^{⊗ k}` (`AlgebraicGeometry.IsVeryAmple.tensorPow`, via the Segre embedding), and
`(L^{⊗ m})^{⊗ k} ≅ L^{⊗ mk} ≅ (L^{⊗ k})^{⊗ m}`.

This is used in the proof of blueprint `lem-sc-mult-n-finite-kernel`. -/
theorem IsAmple.tensorPow {f : X ⟶ Spec (.of K)} {L : X.Modules} (hL : IsAmple f L) {k : ℕ}
    (hk : 0 < k) : IsAmple f (L.tensorPow k) := by
  obtain ⟨hinv, m, hm, hLm⟩ := hL
  exact ⟨inferInstance, m, hm, (hLm.tensorPow hk).of_iso ((L.tensorPowMulIso m k).symm ≪≫
    eqToIso (congrArg L.tensorPow (Nat.mul_comm m k)) ≪≫ L.tensorPowMulIso k m)⟩

/-- Blueprint `lem-sc-ample-tensor`: Tensor products of ample modules.

**A tensor product of ample modules is ample** (Stacks 0890). If `L^{⊗ a}` and `M^{⊗ b}` are
very ample, then so are `(L^{⊗ a})^{⊗ b} ≅ L^{⊗ ab}` and `(M^{⊗ b})^{⊗ a} ≅ M^{⊗ ab}`, hence also
their tensor product `(L ⊗ M)^{⊗ ab}`, by the Segre embedding
(`AlgebraicGeometry.IsVeryAmple.tensorObj`). -/
theorem IsAmple.tensorObj {f : X ⟶ Spec (.of K)} {L M : X.Modules} (hL : IsAmple f L)
    (hM : IsAmple f M) : IsAmple f (L ⊗ M) := by
  obtain ⟨hinvL, a, ha, hLa⟩ := hL
  obtain ⟨hinvM, b, hb, hMb⟩ := hM
  refine ⟨inferInstance, a * b, Nat.mul_pos ha hb,
    ((hLa.tensorPow hb).tensorObj (hMb.tensorPow ha)).of_iso ?_⟩
  exact ((L.tensorPowMulIso a b).symm ⊗ᵢ ((M.tensorPowMulIso b a).symm ≪≫
    eqToIso (congrArg M.tensorPow (Nat.mul_comm b a)))) ≪≫ (L.tensorPowTensorObjIso M _).symm

/-- **Very ampleness is stable under field extension.** If `M = i^* 𝒪(1)` for a closed
immersion `i : X ⟶ ℙ(n; k)`, then for a field extension `K/k` the base change `M_K` is the
pullback of `𝒪(1)` along the base change `i_K : X_K ⟶ ℙ(n; K)` of `i`, which is again a closed
immersion (Stacks 01JY).

(blueprint: `lem-pc-very-ample-ample`, `lem-pc-closed-imm-base-change`) -/
theorem IsVeryAmple.pullback_of_field {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}
    {M : X.Modules} (h : IsVeryAmple f M) (K : Type u) [Field K] [Algebra k K] :
    IsVeryAmple (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M) := by
  obtain ⟨n, i, hn, hi, hif, ⟨e⟩⟩ := h
  set g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have w : pullback.snd f g ≫ g = (pullback.fst f g ≫ i) ≫ ℙ(n; Spec (.of k)) ↘ Spec (.of k) := by
    rw [Category.assoc, hif, pullback.condition]
  let i' := ProjectiveSpace.liftBaseChange (pullback.snd f g) (pullback.fst f g ≫ i) w
  -- `i'` is the base change of `i` along `ℙ(n; K) ⟶ ℙ(n; k)`.
  have hpb : IsPullback i' (pullback.fst f g) (ProjectiveSpace.map n g) i := by
    refine IsPullback.of_right (h₂₂ := ℙ(n; Spec (.of k)) ↘ Spec (.of k))
      (h₁₂ := ℙ(n; Spec (.of K)) ↘ Spec (.of K)) (v₁₃ := g) ?_
      (ProjectiveSpace.liftBaseChange_map _ _ _) (ProjectiveSpace.isPullback_map n g).flip
    rw [ProjectiveSpace.liftBaseChange_over, hif]
    exact (IsPullback.of_hasPullback f g).flip
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback hpb.flip hi
  refine ⟨n, i', hn, this, ProjectiveSpace.liftBaseChange_over _ _ _, ⟨?_⟩⟩
  exact (Scheme.Modules.pullback i').mapIso (ProjectiveSpace.pullbackMapTwistIso n g 1).symm ≪≫
    (Scheme.Modules.pullbackComp i' (ProjectiveSpace.map n g)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (ProjectiveSpace.liftBaseChange_map _ _ _)).app _ ≪≫
    (Scheme.Modules.pullbackComp (pullback.fst f g) i).symm.app _ ≪≫
    (Scheme.Modules.pullback (pullback.fst f g)).mapIso e

/-- **Ampleness is stable under field extension**, by
`AlgebraicGeometry.IsVeryAmple.pullback_of_field` applied to a very ample tensor power.

(blueprint: `lem-pc-very-ample-ample`) -/
theorem IsAmple.pullback_of_field {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}
    {M : X.Modules} (h : IsAmple f M) (K : Type u) [Field K] [Algebra k K] :
    IsAmple (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M) := by
  obtain ⟨hinv, m, hm, hv⟩ := h
  exact ⟨inferInstance, m, hm, (hv.pullback_of_field K).of_iso
    (Scheme.Modules.nonempty_pullback_tensorPow_iso _ M m).some⟩

end AlgebraicGeometry
