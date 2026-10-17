/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import Mathlib.Topology.Sets.CompactOpenCovered

/-!
# Locally constant pro-étale sheaves are of étale origin

Constant sheaves are stable under the pullbacks of pro-étale sheaves and under the comparison
pullback `ν^*`, both being left adjoint to the global sections. Hence a pro-étale sheaf which is
constant on the members of a pro-étale covering family is, over a quasi-compact quasi-separated
scheme, constant on the members of a finite covering family by quasi-compact quasi-separated
morphisms, so it is of étale origin
(`AlgebraicGeometry.ProEtale.essImage_comparisonUpperStar_of_isLocallyConstant`), being of étale
origin being local for such families
(`AlgebraicGeometry.ProEtale.essImage_comparisonUpperStar_of_cover`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The pullback of a constant pro-étale sheaf is constant: both `constantSheaf ⋙ g^*` and
`constantSheaf` are left adjoint to the global sections, as `Γ ∘ g_* ≅ Γ`. -/
noncomputable def constantSheafCompUpperStarIso {Z W : Scheme.{u}} (g : Z ⟶ W) :
    constantSheaf (Scheme.ProEt.topology W) A ⋙ ProEtale.upperStar A g ≅
      constantSheaf (Scheme.ProEt.topology Z) A :=
  (((constantSheafΓAdj (Scheme.ProEt.topology W) A).comp
      (ProEtale.upperStarLowerStarAdjunction A g)).ofNatIsoRight
    (globalSectionsLowerStarIso A g)).leftAdjointUniq
    (constantSheafΓAdj (Scheme.ProEt.topology Z) A)

/-- The comparison pullback `ν^*` sends constant étale sheaves to constant pro-étale sheaves:
`constantSheaf ⋙ ν^*` and `constantSheaf` are both left adjoint to the global sections, as the
inclusion of sites sends the terminal object `X` of `X_ét` to the terminal object of `X_proét`.
-/
noncomputable def constantSheafCompComparisonUpperStarIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology A ⋙ ν^*(X)[A] ≅
      constantSheaf (Scheme.ProEt.topology X) A :=
  (((constantSheafAdj X.smallEtaleTopology A (Scheme.Etale.isTerminalMkId X)).comp
      (comparisonAdjunction A X)).ofNatIsoRight
    ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso A
      X.smallEtaleTopology (Scheme.ProEt.topology X)
        (op (Scheme.Etale.mk (𝟙 X))))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology X) A (Scheme.ProEt.isTerminalMkId X))

variable {A}

/-- Constant pro-étale sheaves are of étale origin. -/
lemma essImage_comparisonUpperStar_constantSheaf (X : Scheme.{u}) (M : A) :
    (comparisonUpperStar A X).essImage
      ((constantSheaf (Scheme.ProEt.topology X) A).obj M) :=
  ⟨_, ⟨(constantSheafCompComparisonUpperStarIso A X).app M⟩⟩

/-- A finite jointly surjective family of quasi-compact weakly étale morphisms is a pro-étale
covering family. -/
lemma ofArrows_mem_proetalePrecoverage_of_finite {X : Scheme.{u}} {S : Type*} [Finite S]
    {V : S → Scheme.{u}} (p : ∀ s, V s ⟶ X) [∀ s, WeaklyEtale (p s)]
    [∀ s, QuasiCompact (p s)] (hp : ∀ x, ∃ s, x ∈ Set.range (p s)) :
    Presieve.ofArrows V p ∈ Scheme.proetalePrecoverage X := by
  refine ⟨?_, (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2
    ⟨hp, fun s ↦ inferInstance⟩⟩
  let E : PreZeroHypercover X := ⟨S, V, p⟩
  change E.presieve₀ ∈ Scheme.qcPrecoverage X
  rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact ⟨fun {U} hU ↦ .of_finite_of_isSpectralMap (fun s ↦ (p s).isSpectralMap)
    (fun x _ ↦ hp x) U.2 hU.isCompact⟩

/-- **Locally constant pro-étale sheaves are of étale origin** over a quasi-compact
quasi-separated scheme. -/
theorem essImage_comparisonUpperStar_of_isLocallyConstant [Etale.HasCohomologyContinuity A]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {F : Sheaf (Scheme.ProEt.topology X) A} {ι : Type*} {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (h : ∀ i, ∃ M : A, Nonempty ((ProEtale.upperStar A (g i)).obj F ≅
      (constantSheaf (Scheme.ProEt.topology (W i)) A).obj M)) :
    (comparisonUpperStar A X).essImage F := by
  have hge (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hg (.mk i)
  let E : PreZeroHypercover X := ⟨ι, W, g⟩
  have : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.1
    ((show Scheme.proetalePrecoverage ≤ Scheme.qcPrecoverage from inf_le_left) _ hg)
  obtain ⟨N, a, W', hW, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact E
    (U := ⊤) isCompact_univ
  let V (s : Fin N) : Scheme.{u} := (W' s).toScheme
  have (s : Fin N) : IsAffine (V s) := hW s
  let p (s : Fin N) : V s ⟶ X := (W' s).ι ≫ g (a s)
  have hsurj (x : X) : ∃ s, x ∈ Set.range (p s) := by
    have : x ∈ ⋃ i, E.f (a i) '' (W' i : Set _) := by rw [hcov]; trivial
    obtain ⟨i, w, hw, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_image] using this
    exact ⟨i, ⟨w, hw⟩, rfl⟩
  refine essImage_comparisonUpperStar_of_cover p
    (ofArrows_mem_proetalePrecoverage_of_finite p hsurj) F fun s ↦ ?_
  obtain ⟨M, ⟨e⟩⟩ := h (a s)
  exact essImage_comparisonUpperStar_of_iso
    ((ProEtale.upperStarComp A (W' s).ι (g (a s))).app F ≪≫
      (ProEtale.upperStar A (W' s).ι).mapIso e ≪≫
      (constantSheafCompUpperStarIso A (W' s).ι).app M).symm
    (essImage_comparisonUpperStar_constantSheaf _ M)

end AlgebraicGeometry.ProEtale
