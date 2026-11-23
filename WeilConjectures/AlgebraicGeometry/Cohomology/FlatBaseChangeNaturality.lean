/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyGluing

/-!
# The flat base change map on cohomology: naturality and bijectivity

Let `X` be a scheme over a commutative ring `R`, let `S` be an `R`-algebra and let
`X_S = X ×_{Spec R} Spec S`. For an `𝒪_X`-module `M` the canonical comparison map
`AlgebraicGeometry.Scheme.Modules.H.baseChange : S ⊗_R H^q(X, M) ⟶ H^q(X_S, M_S)` is natural in
`M`. When `R = k` is a field and `X` is quasi-compact and quasi-separated it is bijective for
quasi-coherent `M`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.H.map_pullback_baseChange_one_tmul`: naturality of the base
  change map.
- `AlgebraicGeometry.Scheme.Modules.H.bijective_baseChange`: flat base change along a field
  extension, for the canonical map.

## Implementation details

`AlgebraicGeometry.Scheme.Modules.nonempty_H_pullback_linearEquiv` only records that some linear
isomorphism `H^q(X_K, M_K) ≃ K ⊗_k H^q(X, M)` exists; its proof shows that the canonical map is
bijective, and that argument is repeated here so that the canonical map can be used.
-/

@[expose] public section

universe u

open CategoryTheory Function TopologicalSpace TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

section Naturality

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}

/-- **Naturality of the base change map on cohomology.** For a morphism `φ : M ⟶ N` of
`𝒪_X`-modules, the base change map `S ⊗_R H^q(X, -) ⟶ H^q(X_S, (-)_S)` commutes with the maps
induced by `φ` and by its pullback `φ_S : M_S ⟶ N_S`. -/
theorem H.map_pullback_baseChange_one_tmul (f : X ⟶ Spec (.of R)) {M N : X.Modules}
    (φ : M ⟶ N) (q : ℕ) (x : M.H q) :
    H.map ((pullback (baseChangeFst (S := S) f)).map φ) q
        (H.baseChange (S := S) f M q ((1 : S) ⊗ₜ (show HOver f M q from x))) =
      H.baseChange (S := S) f N q ((1 : S) ⊗ₜ (show HOver f N q from H.map φ q x)) := by
  have h : φ ≫ baseChangeUnit (S := S) f N =
      baseChangeUnit (S := S) f M ≫ (pushforward (baseChangeFst (S := S) f)).map
        ((pullback (baseChangeFst (S := S) f)).map φ) :=
    (pullbackPushforwardAdjunction (baseChangeFst (S := S) f)).unit.naturality φ
  have h' := coeff_naturality (baseChangeFst (S := S) f) (baseChangeUnit (S := S) f M)
    (baseChangeUnit (S := S) f N) φ ((pullback (baseChangeFst (S := S) f)).map φ) h
  change H.map _ q ((1 : S) • H.baseChangeLinear (S := S) f M q x) =
    (1 : S) • H.baseChangeLinear (S := S) f N q (H.map φ q x)
  rw [one_smul, one_smul]
  exact (sheafComparison_naturality _ _ _ _ _ _ h' q x).symm

end Naturality

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (K : Type u) [Field K] [Algebra k K]

/-- **The flat base change map on cohomology is bijective.** Let `X` be a quasi-compact
quasi-separated scheme over a field `k`, let `K/k` be a field extension and let `M` be a
quasi-coherent `𝒪_X`-module. Then the canonical `K`-linear comparison map
`K ⊗_k H^q(X, M) ⟶ H^q(X_K, M_K)` is bijective, where `X_K = X ×_{Spec k} Spec K` and `M_K` is
the pullback of `M` to `X_K`. -/
@[stacks 02KH]
theorem H.bijective_baseChange [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Bijective (H.baseChange (S := K) (X ↘ Spec (.of k)) M q) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  let P (U : X.Opens) : Prop :=
    ∀ (Y : Scheme.{u}) (j : Y ⟶ X) (_ : IsOpenImmersion j), j.opensRange = U →
      ∀ (N : Y.Modules) (_ : N.IsQuasicoherent) (n : ℕ),
        Function.Bijective (Modules.H.baseChange (S := K) (j ≫ X ↘ Spec (.of k)) N n)
  have hP : P ⊤ := by
    apply compact_open_induction_on (P := P) ⊤ isCompact_univ
    · intro Y j hj hjrange N hN n
      have : IsEmpty Y := ⟨fun y ↦ by
        have hy : j y ∈ j.opensRange := ⟨y, rfl⟩
        rw [hjrange] at hy
        exact hy⟩
      exact Modules.H.baseChange_bijective_of_isSeparated _ N n
    · intro U hU V ih Y j hj hjrange N hN n
      let A : Y.Opens := j ⁻¹ᵁ U
      let B : Y.Opens := j ⁻¹ᵁ V.1
      have hAimage : j ''ᵁ A = U := by
        rw [Hom.image_preimage_eq_opensRange_inf, hjrange, inf_eq_right.mpr le_sup_left]
      have hB : IsAffineOpen B :=
        V.2.preimage_of_isOpenImmersion j (hjrange.symm ▸ le_sup_right)
      have hAc : IsCompact (A : Set Y) :=
        j.isOpenEmbedding.isEmbedding.isCompact_iff.mpr (by
          change IsCompact (j ''ᵁ A : Set X)
          rw [hAimage]
          exact hU)
      have : CompactSpace A.toScheme := isCompact_iff_compactSpace.mp hAc
      have : QuasiSeparatedSpace Y := j.isOpenEmbedding.quasiSeparatedSpace
      have hIc : IsCompact ((A ⊓ B : Y.Opens) : Set Y) :=
        hAc.inter_of_isOpen hB.isCompact A.isOpen B.isOpen
      have : CompactSpace (A ⊓ B).toScheme := isCompact_iff_compactSpace.mp hIc
      have : IsAffine B.toScheme := hB
      have : (A ⊓ B).toScheme.IsSeparated := ⟨by
        rw [← Limits.terminal.comp_from (Y.homOfLE (inf_le_right : A ⊓ B ≤ B))]
        infer_instance⟩
      apply Modules.H.baseChange_bijective_of_openCover _ N A B ?_ ?_ ?_ ?_ n
      · change j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V.1 = ⊤
        rw [← j.preimage_sup, ← hjrange, j.preimage_opensRange]
      · intro r
        apply ih A.toScheme (A.ι ≫ j) inferInstance ?_ _ inferInstance r
        rw [Hom.opensRange_comp, Opens.opensRange_ι, hAimage]
      · intro r
        exact Modules.H.baseChange_bijective_of_isSeparated _ _ r
      · intro r
        exact Modules.H.baseChange_bijective_of_isSeparated _ _ r
  exact hP X (𝟙 X) inferInstance (Hom.opensRange_of_isIso _) M inferInstance q

/-- The flat base change map `K ⊗_k H^q(X, M) ⟶ H^q(X_K, M_K)` of
`AlgebraicGeometry.Scheme.Modules.H.baseChange`, for the `K`-module structure of the cohomology
of the `K`-scheme `X_K = X ×_{Spec k} Spec K`. -/
noncomputable def H.baseChangeField (M : X.Modules) (q : ℕ) :
    K ⊗[k] M.H q →ₗ[K] ((pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).H q where
  toFun x := H.baseChange (S := K) (X ↘ Spec (.of k)) M q x
  map_add' x y := map_add (H.baseChange (S := K) (X ↘ Spec (.of k)) M q) x y
  map_smul' a x := (H.baseChange (S := K) (X ↘ Spec (.of k)) M q).map_smul a x

/-- Naturality of `AlgebraicGeometry.Scheme.Modules.H.baseChangeField`. -/
theorem H.map_pullback_baseChangeField_one_tmul {M N : X.Modules} (φ : M ⟶ N) (q : ℕ)
    (x : M.H q) :
    H.map ((pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map φ) q
        (H.baseChangeField K M q (1 ⊗ₜ x)) =
      H.baseChangeField K N q (1 ⊗ₜ H.map φ q x) :=
  H.map_pullback_baseChange_one_tmul (S := K) (X ↘ Spec (.of k)) φ q x

/-- **Flat base change along a field extension, as a linear equivalence.** For a quasi-coherent
module `M` on a quasi-compact quasi-separated scheme `X` over `k`, the map
`AlgebraicGeometry.Scheme.Modules.H.baseChangeField` is bijective. -/
theorem H.bijective_baseChangeField [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Bijective (H.baseChangeField (k := k) K M q) :=
  H.bijective_baseChange (k := k) K M q

end BaseChange

end AlgebraicGeometry.Scheme.Modules
