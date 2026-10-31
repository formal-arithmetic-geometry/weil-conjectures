/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.Connected.Clopen
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.BaseChangeField
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# An invariant clopen separation containing a connected base-changed image

Source: Stacks Project, Varieties, Tag 038C, `lemma-tricky`, first paragraph and
intersection/union construction; `equation-galois-action-base-change-kbar` for the action.
(blueprint: lem-trf-galois-connected-image-invariant-separation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- After interchanging the parts of a nontrivial clopen separation if necessary, intersecting
all Galois translates of the part containing the connected base-changed image produces a
nontrivial invariant clopen separation containing that image.

Source: Stacks Project, Varieties, Tag 038C, `lemma-tricky`, first paragraph and the
intersection/union construction, specialized to finite Galois extensions; the action is
`equation-galois-action-base-change-kbar`.
(blueprint: lem-trf-galois-connected-image-invariant-separation).

Proof:
1. The inverse images of A and B give a clopen partition of the connected, nonempty T_L
   (def-pc-scheme, def-weil-connected-scheme). Choose C = A or C = B containing its image I.
2. Spectrum functoriality and the fibre-product projections show that the base-change maps
   for automorphisms are invertible, compose in the opposite order, and commute with f_L
   (def-weil-affine-spectrum, def-pc-fibre-product, def-pc-base-change). Thus every translate
   of I equals I.
3. The group is finite by lem-weil-pbc-finite-galois-fixed-field. Each translate of C is
   clopen because the associated scheme automorphism is a homeomorphism. Their finite
   intersection P is clopen, and so is its complement Q.
4. Invariance of I gives I contained in P. The identity translate gives P contained in C.
   Hence P is nonempty, and Q contains the other nonempty part. The complement definition
   gives disjointness and union equal to the whole space.
5. Applying any automorphism to the intersection reindexes its translates by a permutation
   of the Galois group, with the opposite composition law from step 2. Thus P is invariant.
   Bijectivity preserves complements, so Q is invariant as well.
-/
theorem galois_connected_image_invariant_separation
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (T X : Scheme.{u}) [T.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of k))]
    [ConnectedSpace (T.baseChangeField k L)]
    (A B : Set (X.baseChangeField k L))
    (hA : IsClopen A) (hB : IsClopen B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Set.univ) :
    ∃ C P Q : Set (X.baseChangeField k L),
      (C = A ∨ C = B) ∧
      P = ⋂ σ : L ≃ₐ[k] L,
        (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' C ∧
      Q = Pᶜ ∧
      P.Nonempty ∧ Q.Nonempty ∧ IsClopen P ∧ IsClopen Q ∧
      Disjoint P Q ∧ P ∪ Q = Set.univ ∧
      Set.range (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
        (f.asOver (Spec (.of k)))).left) ⊆ P ∧
      P ⊆ C ∧
      ∀ σ : L ≃ₐ[k] L,
        (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' P = P ∧
        (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' Q = Q := by
  classical
  have hspec_one : specAlgEquivOver (1 : L ≃ₐ[k] L) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (RingHom.id L)) = 𝟙 _
    exact Spec.map_id _
  have hspec_mul (σ τ : L ≃ₐ[k] L) :
      specAlgEquivOver σ ≫ specAlgEquivOver τ = specAlgEquivOver (σ * τ) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom τ.toRingHom) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
  let a (Y : Scheme.{u}) [Y.Over (Spec (.of k))] (σ : L ≃ₐ[k] L) :
      Y.baseChangeField k L ⟶ Y.baseChangeField k L :=
    baseChangeMap (Y ↘ Spec (.of k)) (specAlgEquivOver σ)
  have hone (Y : Scheme.{u}) [Y.Over (Spec (.of k))] : a Y 1 = 𝟙 _ := by
    dsimp [a]
    rw [hspec_one, baseChangeMap_id]
    rfl
  have hmul (Y : Scheme.{u}) [Y.Over (Spec (.of k))] (σ τ : L ≃ₐ[k] L) :
      a Y σ ≫ a Y τ = a Y (σ * τ) := by
    dsimp [a]
    rw [← baseChangeMap_comp, hspec_mul]
  let e (Y : Scheme.{u}) [Y.Over (Spec (.of k))] (σ : L ≃ₐ[k] L) :
      Y.baseChangeField k L ≅ Y.baseChangeField k L :=
    { hom := a Y σ
      inv := a Y σ⁻¹
      hom_inv_id := by rw [hmul, mul_inv_cancel, hone]
      inv_hom_id := by rw [hmul, inv_mul_cancel, hone] }
  let F : T.baseChangeField k L ⟶ X.baseChangeField k L :=
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
      (f.asOver (Spec (.of k)))).left
  have hFfst : F ≫ pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.fst (T ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ f :=
    (baseChange_morphism_projections (f.asOver (Spec (.of k)))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))).1
  have hFsnd : F ≫ pullback.snd (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.snd (T ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    (baseChange_morphism_projections (f.asOver (Spec (.of k)))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))).2
  have hafst (Y : Scheme.{u}) [Y.Over (Spec (.of k))] (σ : L ≃ₐ[k] L) :
      a Y σ ≫ pullback.fst (Y ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.fst (Y ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    baseChangeMap_fst (Y ↘ Spec (.of k)) (specAlgEquivOver σ)
  have hasnd (Y : Scheme.{u}) [Y.Over (Spec (.of k))] (σ : L ≃ₐ[k] L) :
      a Y σ ≫ pullback.snd (Y ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.snd (Y ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ (specAlgEquivOver σ).left :=
    baseChangeMap_snd (Y ↘ Spec (.of k)) (specAlgEquivOver σ)
  have hnat (σ : L ≃ₐ[k] L) : a T σ ≫ F = F ≫ a X σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hFfst, ← Category.assoc, hafst]
      rw [Category.assoc, hafst, hFfst]
    · rw [Category.assoc, hFsnd, hasnd]
      rw [Category.assoc, hasnd, ← Category.assoc, hFsnd]
  have hnat_apply (σ : L ≃ₐ[k] L) (t : T.baseChangeField k L) :
      F (a T σ t) = a X σ (F t) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun g ↦ g t) (hnat σ)
  have hrange (σ : L ≃ₐ[k] L) : a X σ '' Set.range F = Set.range F := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨a T σ t, hnat_apply σ t⟩
    · rintro _ ⟨t, rfl⟩
      obtain ⟨t', ht'⟩ := (Scheme.homeoOfIso (e T σ)).surjective t
      refine ⟨F t', ⟨t', rfl⟩, ?_⟩
      exact (hnat_apply σ t').symm.trans (congrArg F ht')
  have hchoose : ∃ C D : Set (X.baseChangeField k L),
      (C = A ∨ C = B) ∧ IsClopen C ∧ D.Nonempty ∧ Disjoint C D ∧
      Set.range F ⊆ C := by
    let t : T.baseChangeField k L := Classical.choice inferInstance
    have ht : F t ∈ A ∪ B := by rw [hcover]; trivial
    have hconn := (isConnected_range F.continuous).isPreconnected
    rcases ht with ht | ht
    · exact ⟨A, B, Or.inl rfl, hA, hBne, hdisj,
        hconn.subset_isClopen hA ⟨F t, ⟨t, rfl⟩, ht⟩⟩
    · exact ⟨B, A, Or.inr rfl, hB, hAne, hdisj.symm,
        hconn.subset_isClopen hB ⟨F t, ⟨t, rfl⟩, ht⟩⟩
  obtain ⟨C, D, hCeq, hC, hD, hCD, hFC⟩ := hchoose
  let P : Set (X.baseChangeField k L) := ⋂ σ : L ≃ₐ[k] L, a X σ '' C
  have hFP : Set.range F ⊆ P := by
    intro x hx
    apply Set.mem_iInter.mpr
    intro σ
    rw [← hrange σ] at hx
    exact Set.image_mono hFC hx
  have hPC : P ⊆ C := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iInter.mp hx (1 : L ≃ₐ[k] L)
    rw [hone] at hxy
    change y = x at hxy
    exact hxy ▸ hy
  have hP : IsClopen P := by
    apply isClopen_iInter_of_finite
    intro σ
    change IsClopen ((Scheme.homeoOfIso (e X σ)) '' C)
    rw [(Scheme.homeoOfIso (e X σ)).image_eq_preimage_symm]
    exact hC.preimage (Scheme.homeoOfIso (e X σ)).symm.continuous
  have hPinv (τ : L ≃ₐ[k] L) : a X τ '' P = P := by
    calc
      a X τ '' P = ⋂ σ : L ≃ₐ[k] L, a X τ '' (a X σ '' C) :=
        Set.image_iInter (Scheme.homeoOfIso (e X τ)).bijective _
      _ = ⋂ σ : L ≃ₐ[k] L, a X (σ * τ) '' C := by
        apply Set.iInter_congr
        intro σ
        rw [Set.image_image]
        congr 1
        funext x
        exact (congrArg (fun g ↦ g x) (hmul X σ τ))
      _ = P := (mul_right_surjective τ).iInter_comp (fun σ : L ≃ₐ[k] L ↦ a X σ '' C)
  refine ⟨C, P, Pᶜ, hCeq, rfl, rfl, ?_, ?_, hP, hP.compl,
    disjoint_compl_right, Set.union_compl_self P, hFP, hPC, ?_⟩
  · obtain ⟨t⟩ := (inferInstance : Nonempty (T.baseChangeField k L))
    exact ⟨F t, hFP ⟨t, rfl⟩⟩
  · obtain ⟨x, hx⟩ := hD
    exact ⟨x, fun h ↦ Set.disjoint_left.mp hCD (hPC h) hx⟩
  · intro σ
    refine ⟨hPinv σ, ?_⟩
    change (Scheme.homeoOfIso (e X σ)) '' Pᶜ = Pᶜ
    rw [(Scheme.homeoOfIso (e X σ)).image_compl]
    exact congrArg (·ᶜ) (hPinv σ)

end AlgebraicGeometry
