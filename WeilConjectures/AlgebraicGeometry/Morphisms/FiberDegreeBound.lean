/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.FiniteOverField

/-!
# Bounded fibre degrees

For a morphism of schemes `f : X ⟶ Y` we define when an integer `n` bounds the degrees of the
fibres of `f` and when the fibres of `f` are universally bounded (Stacks, Tag 03J4). We also record
the permanence properties of finite morphisms.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.BoundsFiberDegree`: every fibre `X_y` is finite over `κ(y)` of
  degree `≤ n`.
- `AlgebraicGeometry.Scheme.Hom.HasUniversallyBoundedFibers`: some `n` bounds the fibre degrees.

## Main statements

- `AlgebraicGeometry.isFinite_permanence`: base change, affineness of the source and properness
  of composites for finite morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An integer `n` *bounds the degrees of the fibres* of `f : X ⟶ Y` if for every `y : Y` the
fibre `X_y` is finite over `κ(y)` and `dim_{κ(y)} Γ(X_y, 𝒪) ≤ n`.
(blueprint: `def-weil-pbc-fibre-degree-bound`, part (1)) -/
def Scheme.Hom.BoundsFiberDegree {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ y : Y, IsFinite (f.fiberToSpecResidueField y) ∧ (f.fiberToSpecResidueField y).finrankΓ ≤ n

/-- The fibres of `f : X ⟶ Y` are *universally bounded* if some integer `n` bounds the degrees
of the fibres of `f` (Stacks, Tag 03J4).
(blueprint: `def-weil-pbc-fibre-degree-bound`, part (2)) -/
def Scheme.Hom.HasUniversallyBoundedFibers {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ n : ℕ, f.BoundsFiberDegree n

/-- Permanence of finite morphisms: (a) finite morphisms are stable under base change, (b) the
source of a finite morphism to an affine scheme is affine, and (c) a finite morphism followed by
a proper morphism is proper (in particular a scheme finite over a proper `k`-scheme is proper
over `k`). (blueprint: `lem-weil-pbc-finite-morphism-permanence`) -/
theorem isFinite_permanence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    (∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y), IsFinite (pullback.snd f g)) ∧
    (IsAffine Y → IsAffine X) ∧
    (∀ {S : Scheme.{u}} (h : Y ⟶ S), IsProper h → IsProper (f ≫ h)) := by
  refine ⟨fun g ↦ inferInstance, fun _ ↦ isAffine_of_isAffineHom f, fun h _ ↦ inferInstance⟩

/-- If the source of an affine morphism `p : Z ⟶ U` is a finite coproduct of schemes `D j`, each
mapped isomorphically onto `U`, then every fibre of `p` has degree `|J|`.
(blueprint: `lem-weil-pbc-fiber-degree-split-cofan`) -/
theorem Scheme.Hom.fiberDegree_eq_nat_card_of_split_cofan {Z U : Scheme.{u}} (p : Z ⟶ U)
    [IsAffineHom p] {J : Type u} [Finite J] {D : J → Scheme.{u}} (i : ∀ j, D j ⟶ Z)
    (hc : IsColimit (Cofan.mk Z i)) (hiso : ∀ j, IsIso (i j ≫ p)) (x : U) :
    p.fiberDegree x = Nat.card J := by
  have := Fintype.ofFinite J
  let K := U.residueField x
  let s := U.fromSpecResidueField x
  let α (j : J) : Spec K ⟶ D j := s ≫ inv (i j ≫ p)
  have hα (j : J) : α j ≫ i j ≫ p = s := by simp [α]
  let a (j : J) : Spec K ⟶ p.fiber x := pullback.lift (α j ≫ i j) (𝟙 _) (by simp [hα])
  have ha₁ (j : J) : a j ≫ p.fiberι x = α j ≫ i j := pullback.lift_fst _ _ _
  have ha₂ (j : J) : a j ≫ p.fiberToSpecResidueField x = 𝟙 _ := pullback.lift_snd _ _ _
  have hpb (j : J) : IsPullback (a j) (α j) (p.fiberι x) (i j) := by
    refine IsPullback.of_right (h₁₂ := p.fiberToSpecResidueField x) (h₂₂ := p) (v₁₃ := s)
      ?_ (ha₁ j) (IsPullback.of_hasPullback p s).flip
    rw [ha₂ j]
    have := hiso j
    exact IsPullback.of_horiz_isIso ⟨by simp [hα]⟩
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts hc (Cofan.mk _ a)
    (Discrete.natTrans fun j ↦ α j.as) (p.fiberι x)
    (by ext j; simp [ha₁]) (NatTrans.Equifibered.of_discrete _) (fun j ↦ hpb j.as)
  have hSpec : IsColimit (Cofan.mk (Spec (.of (J → K)))
      fun j ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : J ↦ K) j))) :=
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr
      (inferInstanceAs (IsIso (sigmaSpec fun _ : J ↦ K)))).some
  let e := hc'.coconePointUniqueUpToIso hSpec
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (J → K))) ≫
      Spec.map (Iso.refl (CommRingCat.of K)).hom = p.fiberToSpecResidueField x := by
    refine Cofan.IsColimit.hom_ext hc' _ _ fun j ↦ ?_
    have h1 : a j ≫ e.hom =
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : J ↦ K) j)) :=
      hc'.comp_coconePointUniqueUpToIso_hom hSpec ⟨j⟩
    rw [Cofan.mk_inj, reassoc_of% h1, ha₂, Iso.refl_hom, Spec.map_id, Category.comp_id,
      ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of K)
  rw [Scheme.Hom.fiberDegree]
  refine (Scheme.Hom.finrankΓ_eq_of_iso (p.fiberToSpecResidueField x) _ e (Iso.refl _) he).trans
    ?_
  rw [Scheme.Hom.finrankΓ_SpecMap, Module.finrank_pi, Nat.card_eq_fintype_card]

/-- If a scheme `T` over a field `k` is covered by finitely many opens `W i`, each finite over `k`
of degree `≤ n i`, then `T` is finite over `k` of degree `≤ ∑ i, n i`.
(blueprint: `lem-weil-pbc-finite-open-cover-degree-sum`) -/
theorem finite_open_cover_degree_sum {k : Type u} [Field k] {T : Scheme.{u}}
    (t : T ⟶ Spec (.of k)) {m : ℕ} (W : Fin m → T.Opens) (hW : ⨆ i, W i = ⊤) (n : Fin m → ℕ)
    (hfin : ∀ i, IsFinite ((W i).ι ≫ t)) (hdeg : ∀ i, ((W i).ι ≫ t).finrankΓ ≤ n i) :
    IsFinite t ∧ t.finrankΓ ≤ ∑ i, n i := by
  have hmem (x : T) : ∃ i, x ∈ W i := by
    have hx : x ∈ (⨆ i, W i : T.Opens) := by simp [hW]
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  have hfd (i : Fin m) := finite_and_discreteTopology_of_isFinite ((W i).ι ≫ t)
  have : Finite T := by
    have hU : (Set.univ : Set T) = ⋃ i, (W i : Set T) := by
      ext x
      simpa using hmem x
    refine Set.finite_univ_iff.mp ?_
    rw [hU]
    exact Set.finite_iUnion fun i ↦ (@Set.finite_coe_iff _ _).mp (hfd i).1
  have : DiscreteTopology T := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun x ↦ ?_
    obtain ⟨i, hi⟩ := hmem x
    have := (hfd i).2
    have h := (W i).ι.isOpenEmbedding.isOpenMap {(⟨x, hi⟩ : W i)} (isOpen_discrete _)
    rwa [Set.image_singleton] at h
  have hT : IsAffine T := inferInstance
  let _ := t.ΓAlgebra
  let _ (i : Fin m) := ((W i).ι ≫ t).ΓAlgebra
  have hWfin (i : Fin m) : Module.Finite (CommRingCat.of k) Γ(W i, ⊤) := by
    have := finite_sections_top_of_isFinite ((W i).ι ≫ t)
    rwa [Scheme.Hom.appLE_top_top] at this
  let r : Γ(T, ⊤) →ₐ[CommRingCat.of k] Π i, Γ(W i, ⊤) :=
    Pi.algHom _ _ fun i ↦ { (W i).ι.appTop.hom with commutes' := fun _ ↦ rfl }
  have hr : Function.Injective r := by
    intro a b hab
    refine T.sheaf.eq_of_locally_eq' (fun i ↦ (W i).ι ''ᵁ ⊤) ⊤ (fun i ↦ homOfLE le_top) ?_ a b
      fun i ↦ congrFun hab i
    simp [Scheme.Opens.ι_image_top, hW]
  have hTfin : Module.Finite (CommRingCat.of k) Γ(T, ⊤) :=
    Module.Finite.of_injective r.toLinearMap hr
  refine ⟨?_, ?_⟩
  · refine (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := t)).mpr ⟨hT, ?_⟩
    have h1 : RingHom.Finite ((Scheme.ΓSpecIso (.of k)).inv ≫ t.appTop).hom := hTfin
    have h2 : t.appTop = (Scheme.ΓSpecIso (.of k)).hom ≫
        ((Scheme.ΓSpecIso (.of k)).inv ≫ t.appTop) := by simp
    rw [h2, CommRingCat.hom_comp]
    exact h1.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom).2)
  · calc t.finrankΓ ≤ Module.finrank (CommRingCat.of k) (Π i, Γ(W i, ⊤)) :=
          LinearMap.finrank_le_finrank_of_injective (f := r.toLinearMap) hr
      _ = ∑ i, ((W i).ι ≫ t).finrankΓ := Module.finrank_pi_fintype _
      _ ≤ ∑ i, n i := Finset.sum_le_sum fun i _ ↦ hdeg i

end AlgebraicGeometry
