/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.Sites.FinitelyContractible

/-!
# Finitely contractible objects of the small pro-étale site

An object of the small pro-étale site whose underlying scheme is the spectrum of a
w-contractible ring is finitely contractible: every covering sieve contains a finite cover by
pairwise disjoint open immersions (Stacks 0990). Every object of the affine pro-étale site admits
a surjection from such an object.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.isFinitelyContractible_of_iso`: the spectrum of a
  w-contractible ring is finitely contractible.
- `AlgebraicGeometry.Scheme.AffineProEt.exists_surjective_isFinitelyContractible`: every object
  of the affine pro-étale site is the target of a surjection from an object which is finitely
  contractible in the pro-étale site.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable {T : Scheme.{u}}

/-- Variant of `AlgebraicGeometry.Scheme.ProEt.exists_disjoint_cover_of_comp_sigmaDesc_eq_id`
keeping track of the index type of the cover. -/
lemma exists_disjoint_cover_of_comp_sigmaDesc_eq_id' {W : T.ProEt} {κ : Type u}
    {V : κ → Scheme.{u}} (v : ∀ j, V j ⟶ W.left) (s : W.left ⟶ ∐ V)
    (hs : s ≫ Sigma.desc v = 𝟙 _) (S : Sieve W)
    (hS : ∀ j {Y : T.ProEt} (a : Y ⟶ W) (b : Y.left ⟶ V j), b ≫ v j = a.left → S a) :
    ∃ (Y : κ → T.ProEt) (f : ∀ i, Y i ⟶ W),
      Sieve.ofArrows Y f ∈ topology T W ∧ (∀ i, S (f i)) ∧ (∀ i, Mono (f i)) ∧
      ∀ i j, i ≠ j → ∀ (Z : T.ProEt) (a : Z ⟶ Y i) (b : Z ⟶ Y j), a ≫ f i = b ≫ f j →
        ⊥ ∈ topology T Z := by
  let O (j : κ) : W.left.Opens := s ⁻¹ᵁ (Sigma.ι V j).opensRange
  have hO (j : κ) : Set.range ((O j).ι ≫ s).base ⊆ Set.range (Sigma.ι V j).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨fun j ↦ ofOpenImmersion W (O j).ι, fun j ↦ ofOpenImmersionHom W (O j).ι,
    ?_, fun j ↦ hS j _ (IsOpenImmersion.lift (Sigma.ι V j) ((O j).ι ≫ s) (hO j)) ?_,
    fun j ↦ ?_, ?_⟩
  · refine mem_topology_of_openImmersion _ (fun j ↦ (O j).ι) (fun x ↦ ?_)
      (fun j ↦ Sieve.ofArrows_mk _ _ j)
    obtain ⟨j, y, hy⟩ := (sigmaOpenCover V).exists_eq (s x)
    refine ⟨j, ?_⟩
    rw [Opens.range_ι]
    exact ⟨y, hy⟩
  · rw [← Sigma.ι_desc v j, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hs,
      Category.comp_id]
    rfl
  · refine (ProEt.forget T ⋙ CategoryTheory.Over.forget T).mono_of_mono_map ?_
    exact inferInstanceAs (Mono (O j).ι)
  · intro i j hij Z a b hab
    have : IsEmpty Z.left := by
      refine ⟨fun z ↦ ?_⟩
      have hab' : a.left ≫ (O i).ι = b.left ≫ (O j).ι := congrArg (fun g ↦ g.left) hab
      have hi : (a.left ≫ (O i).ι).base z ∈ O i := by
        exact (Opens.range_ι (O i)).subset ⟨a.left z, rfl⟩
      have hj : (a.left ≫ (O i).ι).base z ∈ O j := by
        rw [hab']
        exact (Opens.range_ι (O j)).subset ⟨b.left z, rfl⟩
      exact (disjoint_opensRange_sigmaι V i j hij).le_bot ⟨hi, hj⟩
    exact bot_mem_topology Z

/-- **Stacks 0990.** An object of the small pro-étale site whose underlying scheme is the
spectrum of a w-contractible ring is finitely contractible: every covering sieve contains a
finite cover by pairwise disjoint open immersions. -/
@[stacks 0990]
theorem isFinitelyContractible_of_iso {W : T.ProEt} {R : CommRingCat.{u}}
    [IsWContractibleRing R] (e : W.left ≅ Spec R) :
    (topology T).IsFinitelyContractible W := by
  intro S hS
  obtain ⟨P, hP, hPS⟩ := mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (mem_precoverage_iff.1 hP)
  have : IsAffine W.left := .of_isIso e.hom
  obtain ⟨𝒱, g, _, _⟩ := Cover.QuasiCompact.exists_hom.{u + 1, u} 𝒰
  have hmem (i : 𝒰.I₀) : P.map (ProEt.forget T ⋙ CategoryTheory.Over.forget T) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.1 (hmem i)
  -- Reindex the finite affine refinement by a type in `Type u`.
  let ε : ULift.{u} (Fin (Nat.card 𝒱.I₀)) ≃ 𝒱.I₀ := Equiv.ulift.trans (Finite.equivFin _).symm
  let v (k : ULift.{u} (Fin (Nat.card 𝒱.I₀))) := 𝒱.f (ε k)
  have : WeaklyEtale (Sigma.desc v) := IsZariskiLocalAtSource.sigmaDesc fun k ↦ 𝒱.map_prop _
  have : Surjective (Sigma.desc v) := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨k, hk⟩ := ε.surjective (𝒱.idx x)
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [v]
    rw [hk]
    exact 𝒱.covers x
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_isWContractibleRing (Sigma.desc v ≫ e.hom)
  obtain ⟨Y, f, hf, hfS, hmono, hdisj⟩ :=
    exists_disjoint_cover_of_comp_sigmaDesc_eq_id' v (e.hom ≫ s) ?_ S ?_
  · let ε' : Fin (Nat.card 𝒱.I₀) ≃ ULift.{u} (Fin (Nat.card 𝒱.I₀)) := Equiv.ulift.symm
    refine ⟨Fin (Nat.card 𝒱.I₀), fun k ↦ Y (ε' k), fun k ↦ f (ε' k),
      ⟨inferInstance, ?_, fun k ↦ hmono _, fun i j hij Z a b hab ↦
        hdisj _ _ (ε'.injective.ne hij) Z a b hab⟩, fun k ↦ hfS _⟩
    refine (topology T).superset_covering (fun Z g hg ↦ ?_) hf
    obtain ⟨_, c, _, ⟨k⟩, rfl⟩ := hg
    obtain ⟨k', rfl⟩ := ε'.surjective k
    exact Sieve.downward_closed _
      (Sieve.ofArrows_mk (fun k ↦ Y (ε' k)) (fun k ↦ f (ε' k)) k') c
  · rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hs]
    simp
  · intro j Y b c hbc
    have ha' (i : 𝒰.I₀) : (a i).left = eqToHom (hZ i) ≫ 𝒰.f i := hZa i
    let d : Y.left ⟶ (Z (g.s₀ (ε j))).left := c ≫ g.h₀ (ε j) ≫ eqToHom (hZ _).symm
    have hd : d ≫ (a (g.s₀ (ε j))).left = b.left := by
      rw [← hbc, ha', Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, g.w₀]
      rfl
    have hb : b = MorphismProperty.Over.homMk d (by
        rw [← MorphismProperty.Over.w (a (g.s₀ (ε j))), ← Category.assoc, hd]
        exact MorphismProperty.Over.w b) ≫ a (g.s₀ (ε j)) :=
      MorphismProperty.Over.Hom.ext hd.symm
    rw [hb]
    exact S.downward_closed (hPS _ _ (ha _)) _

end ProEt

namespace AffineProEt

variable {S : Scheme.{u}}

/-- **Stacks 0990, affine form.** Every object `U` of the affine pro-étale site admits a
surjection `W ⟶ U` from an object which is finitely contractible in the pro-étale site: take
`W = Spec A'` for a faithfully flat, ind-étale and w-contractible `Γ(U)`-algebra `A'`. -/
theorem exists_surjective_isFinitelyContractible (U : S.AffineProEt) :
    ∃ (W : S.AffineProEt) (q : W ⟶ U), Surjective q.left ∧
      (ProEt.topology S).IsFinitelyContractible ((toProEt S).obj W) := by
  obtain ⟨A', hCRA, hAlgA, hIndA, hFFA, hWCA⟩ :=
    exists_isWContractibleRing (Γ(U.left, ⊤) : Type u)
  let := hCRA
  let := hAlgA
  have := hIndA
  have := hFFA
  have := hWCA
  let φA : Γ(U.left, ⊤) ⟶ CommRingCat.of A' :=
    CommRingCat.ofHom (algebraMap (Γ(U.left, ⊤)) A')
  have hφA : φA.hom.IndEtale :=
    (RingHom.IndEtale.algebraMap_iff (R := (Γ(U.left, ⊤) : Type u)) A').mpr hIndA
  let q₀ : Spec (CommRingCat.of A') ⟶ U.left := Spec.map φA ≫ U.left.isoSpec.inv
  have hq₀ : proAffineEtale q₀ :=
    (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr (proAffineEtale_Spec_iff.mpr hφA)
  let W : S.AffineProEt := mk (q₀ ≫ U.hom) (proAffineEtale.comp_mem _ _ hq₀ U.prop)
  let q : W ⟶ U := MorphismProperty.Over.homMk q₀ rfl trivial
  have hq₀surj : Function.Surjective q₀.base := by
    intro x
    obtain ⟨y, hy⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (B := A') (U.left.isoSpec.hom.base x)
    refine ⟨y, ?_⟩
    have h1 : q₀.base y = U.left.isoSpec.inv.base ((Spec.map φA).base y) := rfl
    have h2 : (Spec.map φA).base y =
        PrimeSpectrum.comap (algebraMap (Γ(U.left, ⊤)) A') y := rfl
    have h3 : U.left.isoSpec.inv.base (U.left.isoSpec.hom.base x) =
        (U.left.isoSpec.hom ≫ U.left.isoSpec.inv).base x := rfl
    have h4 : (U.left.isoSpec.hom ≫ U.left.isoSpec.inv).base x = x := by
      rw [Iso.hom_inv_id]
      simp
    rw [h1, h2, hy, h3, h4]
  have : IsWContractibleRing (CommRingCat.of A') := hWCA
  exact ⟨W, q, ⟨hq₀surj⟩,
    ProEt.isFinitelyContractible_of_iso (R := CommRingCat.of A') (Iso.refl _)⟩

end AffineProEt

end AlgebraicGeometry.Scheme
