/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.CoefficientHeartStratificationDefs
import all Sheaf.Paper.FiniteEtaleLocallyFreeModels
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport

/-!
# Lisse restriction to common refinements

Source: blueprint common-stratification clause (2).
(blueprint: new-det-lem-coefficient-heart-common-stratification-lisse).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem lisse_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) :
    IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj M) := by
  exact CondensedRing.locFree_pullback Λ f M hM

private theorem finitePresentation_fromPoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hP : Mod.IsFinitelyPresented Λ P) :
    Mod.IsFinitelyPresented (condensedRingObj Λ X) (((upperStarFromPoint X).mapMod Λ).obj P) := by
  let F := (upperStarFromPoint X).mapMod Λ
  let e : F.obj (Mod.regular Λ) ≅ Mod.regular (condensedRingObj Λ X) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  obtain ⟨n, m, f, ⟨i⟩⟩ := hP
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let en (n : ℕ) : F.obj (Mod.finiteFree Λ n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let f' := (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private theorem constantModel_lfp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hC a
  have h := fp_of_iso (finitePresentation_fromPoint Λ (C.X a) P hP) e.symm
  have h' := fp_of_iso h ((CondensedRing.normalizedPullbackIso Λ (C.f a)).app M)
  exact fp_of_comap (inv (condensedPullbackHom Λ (C.f a))) h'

private theorem lisse_of_raw_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ a,
      Mod.IsFree ((upperStar Ab.{u + 1} (C.f a)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (C.f a)).mapMod (condensedRingObj Λ X)).obj M)) :
    IsLisseCoefficientModule Λ M := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun a ↦ CondensedRing.free_standardPullback Λ (C.f a) M (hC a)⟩

private theorem lfp_lisse
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X))
    (hp : IsLocallyFinitelyPresented (condensedRingObj (coefficientHeartRingObj Λ) X) M) :
    IsLisseCoefficientModule (coefficientHeartRingObj Λ) M := by
  apply lisse_of_raw_free
  rcases hΛ with ⟨E, hE, rfl⟩ | rfl
  · exact finite_lf ℓ ⟨E, hE⟩ X M hp
  · exact algcl_lf ℓ X M hp

attribute [local irreducible] IsLisseCoefficientModule
  CondensedRing.upperStarComp
  CondensedRing.upperStarLowerStarAdjunction

private theorem lfp_range_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S T : Scheme.{u}}
    (i : S ⟶ X) [IsImmersion i] (j : T ⟶ X)
    (hji : Set.range j ⊆ Set.range i)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ S)
      ((CondensedRing.upperStar Λ i).obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ T)
      ((CondensedRing.upperStar Λ j).obj M) := by
  have hraw := lfp_of_comap (inv (condensedPullbackHom Λ i))
    (lfp_of_iso hM ((CondensedRing.normalizedPullbackIso Λ i).app M))
  have ht := localFinitePresentation_upperStar_of_range_subset
    i j hji (condensedRingObj Λ X) M hraw
  exact lfp_of_iso (lfp_comap (inv (condensedPullbackHom Λ j)) ht)
    ((CondensedRing.normalizedPullbackIso Λ j).app M).symm

private theorem lisse_on_refined_stratum
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] {X S T : Scheme.{u}}
    [IsNoetherian X]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (i : S ⟶ X) [IsImmersion i] (j : T ⟶ X) [IsImmersion j]
    (hji : Set.range j ⊆ Set.range i)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X))
    (hM : HasFiniteConstantLocalModel (coefficientHeartRingObj Λ) S
      ((CondensedRing.upperStar (coefficientHeartRingObj Λ) i).obj M)) :
    IsLisseCoefficientModule (coefficientHeartRingObj Λ)
      ((CondensedRing.upperStar (coefficientHeartRingObj Λ) j).obj M) := by
  have : TopologicalSpace.NoetherianSpace T :=
    j.isEmbedding.isInducing.noetherianSpace
  exact lfp_lisse ℓ Λ T hΛ _
    (lfp_range_restriction (coefficientHeartRingObj Λ) i j hji M
      (constantModel_lfp (coefficientHeartRingObj Λ) S _ hM))

/-- Lisse modules restrict to every locally closed refinement, including its given scheme
structure. Source: blueprint det-lem-coefficient-heart-common-stratification, steps (5)--(6),
and the finite-presentation pullback and immersion-range arguments of
`CondensedConstructibleSerre.lean` and `ProEtaleModuleLfpImmersionTransport.lean`.
(blueprint: new-det-lem-coefficient-heart-common-stratification-lisse).

Proof: base change a trivializing cover to prove that lisse modules stay lisse under any
scheme pullback. A finite constant local model is locally finitely presented: inverse
image from the point preserves regular modules, finite direct sums and cokernels, so it
preserves a finite presentation. Transport the presentation across the model isomorphism
and the normalized coefficient-pullback comparison.

For a refined stratum T with image contained in an adapted stratum S, undo the
normalized coefficient comparison to get local finite presentation over the raw
inverse-image ring on S. Apply the existing immersion-range transfer theorem. It
forms T times_X S and reflects local finite presentation through the surjective
closed immersion to T. Normalize the coefficient comparison on T again. This gives
local finite presentation of the actual restriction, without a factorization T to S.

The underlying space of T is Noetherian because its immersion into X is an embedding.
For each of the finite-subfield and algebraic-closure coefficient cases, the existing
local-triviality lemma makes every locally finitely presented module on T pro-etale
locally finite free. Transport its raw pullbacks to normalized coefficient pullbacks.
This is the required lisse cover. Empty schemes and rank zero are included by the
existing finite-presentation and covering lemmas.
-/
theorem coefficientHeart_commonStratification_lisse
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (X : Scheme.{u}) [IsNoetherian X]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ) :
    (∀ (S T : Scheme.{u}) (i : S ⟶ X), IsImmersion i →
      ∀ j : T ⟶ S, IsImmersion j →
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj
        (coefficientHeartRingObj Λ) S),
        IsLisseCoefficientModule (coefficientHeartRingObj Λ) M →
          IsLisseCoefficientModule (coefficientHeartRingObj Λ) ((CondensedRing.upperStar
            (coefficientHeartRingObj Λ) j).obj M)) ∧
    (∀ (P R : X.FiniteLocallyClosedStratification)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj
        (coefficientHeartRingObj Λ) X)),
      (∀ a : Fin P.n,
        HasFiniteConstantLocalModel (coefficientHeartRingObj Λ) (P.domain a)
          ((CondensedRing.upperStar (coefficientHeartRingObj Λ) (P.immersion a)).obj M)) →
      (∀ a : Fin R.n, ∃ b : Fin P.n, R.stratum a ⊆ P.stratum b) →
        ∀ a : Fin R.n,
          IsLisseCoefficientModule (coefficientHeartRingObj Λ) ((CondensedRing.upperStar
            (coefficientHeartRingObj Λ) (R.immersion a)).obj M)) := by
  constructor
  · intro S T i hi j hj M hM
    exact lisse_pullback _ j M hM
  · intro P R M hM hR a
    obtain ⟨b, hb⟩ := hR a
    have : IsImmersion (P.immersion b) := P.isImmersion b
    have : IsImmersion (R.immersion a) := R.isImmersion a
    apply lisse_on_refined_stratum ℓ Λ hΛ (P.immersion b) (R.immersion a) _ M (hM b)
    simpa only [P.range_immersion, R.range_immersion] using hb

end AlgebraicGeometry.ProEtale
