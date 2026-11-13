/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition
import WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Testing geometric connectedness by finite separable extensions

## References

* Stacks Project, Tag 0389.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem invariant_clopen_eq_empty_or_univ
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [ConnectedSpace X]
    (U : Set ↥(pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
    (hU : IsClopen U)
    (hinv : ∀ σ : L ≃ₐ[k] L,
      (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' U = U) :
    U = ∅ ∨ U = Set.univ := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let p := pullback.fst (X ↘ Spec (.of k)) g
  have : Surjective g := ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have hp : Function.Surjective p := p.surjective
  obtain ⟨A, hA, hpreA⟩ := exists_closed_subset_of_galois_invariant k L X U hU.isClosed hinv
  have hinvc : ∀ σ : L ≃ₐ[k] L,
      (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' Uᶜ = Uᶜ := by
    intro σ
    have : IsIso (specAlgEquivOver σ).left := by
      change IsIso (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom))
      exact inferInstanceAs (IsIso (Spec.map σ.toRingEquiv.toCommRingCatIso.hom))
    have : IsIso (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) :=
      (isPullback_baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)).isIso_fst_of_isIso
    have hbij : Function.Bijective
        (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) := by
      simpa only [Function.Bijective, Function.Injective, Function.Surjective,
        Scheme.Hom.homeomorph_apply] using
        (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)).homeomorph.bijective
    rw [Set.image_compl_eq hbij, hinv σ]
  obtain ⟨B, hB, hpreB⟩ :=
    exists_closed_subset_of_galois_invariant k L X Uᶜ hU.compl.isClosed hinvc
  have hB_eq : B = Aᶜ := by
    apply Set.preimage_injective.mpr hp
    simpa only [p, g, Set.preimage_compl, hpreA] using hpreB
  have hAclopen : IsClopen A := ⟨hA, by simpa only [hB_eq, compl_compl] using hB.isOpen_compl⟩
  rcases isClopen_iff.mp hAclopen with h | h
  · left
    simpa only [h, Set.preimage_empty] using hpreA.symm
  · right
    simpa only [h, Set.preimage_univ] using hpreA.symm

/-- A scheme over a field is geometrically connected precisely when its base change to
every finite separable field extension is connected (Stacks, Tag 0389). -/
theorem GeometricallyConnected.iff_connectedSpace_finite_separable
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    GeometricallyConnected (Y ↘ Spec (.of k)) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [Algebra.IsSeparable k K],
        ConnectedSpace ↥(pullback (Y ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  constructor
  · intro h K _ _ _ _
    have := h
    exact pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace _ _
  · intro h
    let L := SeparableClosure k
    let f := Y ↘ Spec (.of k)
    let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
    have hYk := h k
    have : Nonempty Y :=
      ⟨(pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k))))
        (Nonempty.some hYk.toNonempty)⟩
    have hconn : ConnectedSpace ↥(pullback f g) := by
      apply connectedSpace_iff_clopen.mpr
      refine ⟨inferInstance, fun U hU ↦ ?_⟩
      by_contra! hne
      obtain ⟨K, hK, V, hV, hVne, hVcne, hVinv⟩ :=
        exists_finite_invariant_clopen_partition k L Y f U hU
          hne.1 (Set.nonempty_compl.mpr hne.2)
      have := hK
      let YK := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      let fK := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      let : YK.Over (Spec (.of K)) := ⟨fK⟩
      have : ConnectedSpace YK := h K
      rcases invariant_clopen_eq_empty_or_univ K L YK V hV hVinv with hV0 | hV1
      · exact hVne.ne_empty hV0
      · exact hVcne.ne_empty (by rw [hV1, Set.compl_univ])
    exact (geometricallyConnected_iff_of_fieldExtension (k := k) (k' := L) Y).mpr
      (GeometricallyConnected.of_connectedSpace_of_isSepClosed (pullback.snd f g))

end AlgebraicGeometry
