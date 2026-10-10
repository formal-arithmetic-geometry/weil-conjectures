/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.LocalRetract
public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.Defs

/-!
# Dualizable complexes are locally bounded above, with bounded above duals

Let `K ∈ D(X_proét, Λ)` be dualizable. By the local retract statement
(`AlgebraicGeometry.ProEtale.exists_sieve_retract`), `K` is locally a retract of a bounded
complex, hence locally bounded above, and so is its dual. This file packages this as the
pullback-stable property `IsBoundedDualizable b b' K` (`K` has a right dual `D`, with `K` and `D`
vanishing above `b` and `b'`), which holds locally at every dualizable `K`
(`AlgebraicGeometry.ProEtale.isLocally_isBoundedDualizable`). Such a `K` has a perfect top part in
degrees `≥ b + 1` (`AlgebraicGeometry.ProEtale.IsBoundedDualizable.hasPerfectTop`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Derived pullbacks preserve objects vanishing above a degree: they commute with the
cohomology sheaves. -/
lemma isLE_leftDerivedUpperStar_obj {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) (b : ℤ)
    [K.IsLE b] : (L((g)^*[ModuleCat.{u + 1} Λ]).obj K).IsLE b := by
  rw [isLE_iff]
  intro i hi
  exact ((g)^*[ModuleCat.{u + 1} Λ].map_isZero (K.isZero_of_isLE b i hi)).of_iso
    ((leftDerivedUpperStarHomologyFunctorIso _ g i).app K).symm

/-- An object which is a retract of an object vanishing above `b` vanishes above `b`. -/
lemma isLE_of_retract {Y : Scheme.{u}}
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (s : K ⟶ K') (r : K' ⟶ K) (hsr : s ≫ r = 𝟙 K) (b : ℤ) [K'.IsLE b] : K.IsLE b := by
  rw [isLE_iff]
  intro i hi
  let H := homologyFunctor (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) i
  have : Mono (H.map s) := (IsSplitMono.mk' ⟨H.map r, by rw [← H.map_comp, hsr, H.map_id]⟩).mono
  exact IsZero.of_mono (H.map s) (K'.isZero_of_isLE b i hi)

/-- `K` *is dualizable with bounds `b`, `b'`* if it has a right dual `D`, with `K` vanishing
above `b` and `D` vanishing above `b'`. -/
def IsBoundedDualizable (b b' : ℤ) {Y : Scheme.{u}}
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) : Prop :=
  ∃ (D : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (_ : ExactPairing K D), K.IsLE b ∧ D.IsLE b'

namespace IsBoundedDualizable

variable {b b' : ℤ} {Y : Scheme.{u}}

lemma of_iso {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') (h : IsBoundedDualizable b b' K) : IsBoundedDualizable b b' K' := by
  obtain ⟨D, _, hK, hD⟩ := h
  refine ⟨D, exactPairingCongrLeft e.symm, ?_, hD⟩
  exact TStructure.t.isLE_of_iso e b

lemma isDualizable {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
    (ModuleCat.{u + 1} Λ))} (h : IsBoundedDualizable b b' K) : IsDualizable K := by
  obtain ⟨D, _, -, -⟩ := h
  exact ⟨⟨D, inferInstance⟩⟩

/-- Bounded dualizable objects are stable under derived pullback along weakly étale
morphisms, which are monoidal. -/
lemma upperStar {Z : Scheme.{u}} (g : Z ⟶ Y) [WeaklyEtale g]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (h : IsBoundedDualizable b b' K) :
    IsBoundedDualizable b b' (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨D, _, hK, hD⟩ := h
  let _ := monoidalLeftDerivedUpperStar (ModuleCat.{u + 1} Λ) g
  exact ⟨_, ExactPairing.map L((g)^*[ModuleCat.{u + 1} Λ]) K D,
    isLE_leftDerivedUpperStar_obj g K b, isLE_leftDerivedUpperStar_obj g D b'⟩

/-- A bounded dualizable object `K`, vanishing above `b`, has a perfect top part in degrees
`≥ b + 1`, with zero constant complex. -/
lemma hasPerfectTop {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (h : IsBoundedDualizable b b' K) : HasPerfectTop K (b + 1) := by
  obtain ⟨-, -, hK, -⟩ := h
  obtain ⟨M, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have hE (i : ℤ) : IsZero ((0 : CochainComplex (ModuleCat.{u + 1} Λ) ℤ).X i) :=
    (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
  have hcE (i : ℤ) : IsZero ((((constantSheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} Λ)).mapHomologicalComplex _).obj 0).X i) :=
    (constantSheaf _ _).map_isZero (hE i)
  refine ⟨M, 0, 0, b, ⟨e⟩, fun i ↦ (hcE i).mono _ |>.elim, fun i hi ↦ ?_, ?_, ?_, fun i ↦ ?_⟩
  · exact isIso_of_source_target_iso_zero _ ((hcE i).isoZero) ((M.isZero_of_isStrictlyLE b i
      (by lia)).isoZero)
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i _ ↦ hE i
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i _ ↦ hE i
  · have := ModuleCat.subsingleton_of_isZero (hE i)
    exact ⟨inferInstance, inferInstance⟩

end IsBoundedDualizable

/-- **Dualizable complexes are locally bounded.** A dualizable `K ∈ D(X_proét, Λ)` is locally
bounded dualizable: `K` and its dual are locally retracts of bounded complexes, generated by
finitely many sections (`AlgebraicGeometry.ProEtale.exists_sieve_retract`). -/
theorem isLocally_isBoundedDualizable {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
  have hret {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
      (hK : IsDualizable K) : ∃ R ∈ Scheme.ProEt.topology X (terminalProEt X), ∀ ⦃V : X.ProEt⦄
        (f : V ⟶ terminalProEt X), R f → ∃ B, (L((V.hom)^*[ModuleCat.{u + 1} Λ]).obj K).IsLE B := by
    obtain ⟨R, hR, h⟩ := exists_sieve_retract hK _ (Q.objObjPreimageIso K).symm
    refine ⟨R, hR, fun V f hf ↦ ?_⟩
    obtain ⟨m, p, x, hx⟩ := h f hf
    let N := ((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj (Q.objPreimage K)
    obtain ⟨r, hr⟩ := hx (generatedSubcomplex N p x) (generatedSubcomplexι N p x)
      (fun i ↦ (HomologicalComplex.eval _ _ i).map_mono _)
      (exists_generatedSubcomplexι_f_app_eq N p x)
    let B := ∑ k, |p k| + 1
    have : (generatedSubcomplex N p x).IsStrictlyLE B :=
      isStrictlyLE_generatedSubcomplex N p x B fun k ↦ by
        have := Finset.single_le_sum (f := fun k ↦ |p k|) (fun _ _ ↦ abs_nonneg _)
          (Finset.mem_univ k)
        have := le_abs_self (p k)
        dsimp only at *
        lia
    have : (Q.obj N).IsLE B := isLE_of_retract r _ hr B
    exact ⟨B, TStructure.t.isLE_of_iso (L((V.hom)^*[ModuleCat.{u + 1} Λ]).mapIso
      (Q.objObjPreimageIso K).symm ≪≫ leftDerivedUpperStarQObjIso V.hom _).symm B⟩
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ :=
    _root_.DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ))
  let := BraidedCategory.exactPairing_swap K Kᘁ
  obtain ⟨R₁, hR₁, h₁⟩ := hret ⟨⟨Kᘁ, inferInstance⟩⟩
  obtain ⟨R₂, hR₂, h₂⟩ := hret (K := Kᘁ) ⟨⟨K, inferInstance⟩⟩
  refine IsLocally.of_mem_topology ((Scheme.ProEt.topology X).intersection_covering hR₁ hR₂)
    fun V f ⟨hf₁, hf₂⟩ ↦ ?_
  obtain ⟨B₁, hB₁⟩ := h₁ f hf₁
  obtain ⟨B₂, hB₂⟩ := h₂ f hf₂
  have : WeaklyEtale V.hom := V.prop
  let _ := monoidalLeftDerivedUpperStar (ModuleCat.{u + 1} Λ) V.hom
  exact ⟨B₁, B₂, _, ExactPairing.map L((V.hom)^*[ModuleCat.{u + 1} Λ]) K Kᘁ, hB₁, hB₂⟩

end AlgebraicGeometry.ProEtale
