/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.Comparison.EssImage
public import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GlobalSections

/-!

# Constructible sheaves on the small pro-étale site

This file defines the intrinsic notion of constructibility of sheaves of `Λ`-modules on the
small pro-étale site of a scheme `X` (blueprint `def-weil-finite-torsion-constructibility`): a
sheaf is constructible if, on the strata of a stratification of `X`, it is locally constant with
finite stalks. Locally constant with finite stalks means that the pullbacks along the members
of a pro-étale covering family are constant sheaves of finite `Λ`-modules.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant`: locally constant with finite
  stalks.
- `AlgebraicGeometry.ProEtale.IsConstructible`: constructible.

## Main statements

- `AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_comparisonUpperStar_obj`: the comparison
  pullback `ν^*` of a finite locally constant étale sheaf is locally constant with finite stalks.
- `AlgebraicGeometry.ProEtale.isConstructible_comparisonUpperStar_obj`: `ν^*` preserves
  constructibility.
- `ProEtale.isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`
  (`lem-sf-proetale-constructible-origin` (i)): a pro-étale sheaf is constructible if and only if
  it is `ν^*` of a constructible étale sheaf.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `def-weil-finite-torsion-constructibility`: a sheaf `F` of `Λ`-modules on the
small pro-étale site of `X` is *locally constant with finite stalks* if there is a pro-étale
covering family `g i : W i ⟶ X` such that every pullback `(g i)^* F` is the constant sheaf of a
finite `Λ`-module. -/
def IsFiniteLocallyConstant {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
    Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
      ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty (((g i)^*[ModuleCat.{u + 1} Λ]).obj F ≅
          (constantSheaf (Scheme.ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)

/-- Blueprint `def-weil-finite-torsion-constructibility`: a sheaf `F` of `Λ`-modules on the
small pro-étale site of `X` is *constructible* if there is a finite partition of `X` into
locally closed constructible subschemes on each of which the restriction of `F` is locally
constant with finite stalks. -/
def IsConstructible {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ S : Stratification X, ∀ i : Fin S.n,
    IsFiniteLocallyConstant Λ (((S.immersion i))^*[ModuleCat.{u + 1} Λ].obj F)

section Comparison

variable {Λ}

/-- Being locally constant with finite stalks is invariant under isomorphism. -/
theorem isFiniteLocallyConstant_of_iso {X : Scheme.{u}}
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    (hF : IsFiniteLocallyConstant Λ F) : IsFiniteLocallyConstant Λ G := by
  obtain ⟨ι, W, g, hg, h⟩ := hF
  refine ⟨ι, W, g, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e'⟩⟩ := h i
  exact ⟨M, hM, ⟨((g i)^*[ModuleCat.{u + 1} Λ]).mapIso e.symm ≪≫ e'⟩⟩

/-- Being constructible is invariant under isomorphism. -/
theorem isConstructible_of_iso {X : Scheme.{u}}
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    (hF : IsConstructible Λ F) : IsConstructible Λ G :=
  have ⟨S, hS⟩ := hF
  ⟨S, fun i ↦ isFiniteLocallyConstant_of_iso
    (((S.immersion i))^*[ModuleCat.{u + 1} Λ].mapIso e) (hS i)⟩

/-- The scheme `X`, with the identity, is a terminal object of its small étale site. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Etale.isTerminalMkId (X : Scheme.{u}) :
    IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom (fun V ↦ MorphismProperty.Over.homMk V.hom) fun V f ↦
    MorphismProperty.Over.Hom.ext <| by
      change f.left = V.hom
      rw [← MorphismProperty.Over.w f]
      exact (Category.comp_id _).symm

variable (Λ) in
/-- The comparison pullback `ν^*` sends constant étale sheaves to constant pro-étale sheaves:
`constantSheaf ⋙ ν^*` and `constantSheaf` are both left adjoint to the global sections, as the
inclusion of sites sends the terminal object `X` of `X_ét` to the terminal object `X` of
`X_proét`. -/
noncomputable def comparisonUpperStarConstantSheafIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙ ν^*(X)[ModuleCat.{u + 1} Λ] ≅
      constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) (Etale.isTerminalMkId X)).comp
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)).ofNatIsoRight
    ((toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso (ModuleCat.{u + 1} Λ)
      X.smallEtaleTopology (Scheme.ProEt.topology X)
        (op (Scheme.Etale.mk (𝟙 X))))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) (ProEt.isTerminalMkId X))

/-- The comparison pullback `ν^*` of a finite locally constant étale sheaf is locally constant
with finite stalks. An étale cover trivialising `G` is a pro-étale cover, `ν^*` commutes with the
pullbacks along its members and sends constant sheaves to constant sheaves; the values of the
constant sheaves are finite on the nonempty members, as `G` has finitely generated stalks and `Λ`
is finite. -/
theorem isFiniteLocallyConstant_comparisonUpperStar_obj [Finite Λ] {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteLocallyConstant Λ ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) := by
  obtain ⟨⟨𝒰₀, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  let 𝒰 := 𝒰₀.nonemptyMembers
  refine ⟨ULift.{u + 1} 𝒰.I₀, fun i ↦ 𝒰.X i.down, fun i ↦ 𝒰.f i.down, ?_, ?_⟩
  · have h : Presieve.ofArrows (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.X i.down)
        (fun i ↦ 𝒰.f i.down) = 𝒰.presieve₀ := by
      refine le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩) fun _ _ ⟨i⟩ ↦ ?_
      exact Presieve.ofArrows.mk (ι := ULift.{u + 1} 𝒰.I₀) (Y := fun i ↦ 𝒰.X i.down) ⟨i⟩
    rw [h]
    exact etalePrecoverage_le_proetalePrecoverage _ 𝒰.mem₀
  · rintro ⟨⟨i, hi⟩⟩
    have hc : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰₀.f i)).obj G).IsConstant
        (𝒰₀.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar _ (𝒰₀.etalePrecoverageToEtale i) G).mp (h𝒰 i)
    obtain ⟨M, ⟨e⟩⟩ :=
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰₀.f i)).obj G).mem_essImage_of_isConstant
    have : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
        ((constantSheaf (𝒰₀.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
      have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (𝒰₀.f i) G
      IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) e.symm
    have : Nonempty (𝒰₀.X i) := hi
    have : Module.Finite Λ M := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := 𝒰₀.X i) M
    exact ⟨M, Module.finite_of_finite Λ,
      ⟨(comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) (𝒰₀.f i)).app G ≪≫
        (ν^*(𝒰₀.X i)[ModuleCat.{u + 1} Λ]).mapIso e.symm ≪≫
        (comparisonUpperStarConstantSheafIso Λ (𝒰₀.X i)).app M⟩⟩

/-- The comparison pullback `ν^*` of a constructible étale sheaf is constructible: on the strata
of a stratification for `G`, it is `ν^*` of a finite locally constant sheaf, `ν^*` commuting with
the pullbacks to the strata. -/
theorem isConstructible_comparisonUpperStar_obj [Finite Λ] {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsConstructible Λ ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := G)
  refine ⟨S, fun i ↦ ?_⟩
  have := hS i
  exact isFiniteLocallyConstant_of_iso
    ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) (S.immersion i)).app G).symm
    (isFiniteLocallyConstant_comparisonUpperStar_obj _)

/-- The immersions of the strata of a stratification are quasi-compact: the strata are
constructible, and a constructible subset of an affine scheme is quasi-compact. -/
instance _root_.AlgebraicGeometry.Scheme.Stratification.quasiCompact_immersion {X : Scheme.{u}}
    (S : Stratification X) (i : Fin S.n) : QuasiCompact (S.immersion i) := by
  have hV (V : X.affineOpens) : IsCompact ((S.immersion i).base ⁻¹' (V : Set X)) := by
    have : IsAffine (V : X.Opens) := V.2
    have hc : IsCompact ((V : X.Opens).ι.base ⁻¹' S.stratum i) := by
      have := isCompact_iInter_of_isConstructible (X := (V : X.Opens).toScheme)
        (s := fun _ : Unit ↦ (V : X.Opens).ι.base ⁻¹' S.stratum i) fun _ ↦
          (S.isConstructible_stratum i).preimage_of_isOpenEmbedding
            (V : X.Opens).ι.isOpenEmbedding
      rwa [Set.iInter_const] at this
    rw [(S.immersion i).isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range,
      S.range_immersion]
    have := hc.image (V : X.Opens).ι.continuous
    rwa [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm] at this
  refine ⟨fun U hU hUc ↦ ?_⟩
  obtain ⟨s, hs, rfl⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens).1 ⟨hUc, hU⟩
  rw [Set.preimage_iUnion₂]
  exact hs.isCompact_biUnion fun V _ ↦ hV V

/-- A pro-étale sheaf locally constant with finite stalks is of étale origin: it is so locally,
constant sheaves being of étale origin, and being of étale origin is local for the pro-étale
topology (`comparisonUpperStar_essImage_of_mem_proetalePrecoverage`). -/
theorem comparisonUpperStar_essImage_of_isFiniteLocallyConstant {X : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (hF : IsFiniteLocallyConstant Λ F) : (ν^*(X)[ModuleCat.{u + 1} Λ]).essImage F := by
  obtain ⟨ι, W, g, hg, h⟩ := hF
  refine comparisonUpperStar_essImage_of_mem_proetalePrecoverage g hg F fun i ↦ ?_
  obtain ⟨M, -, ⟨e⟩⟩ := h i
  exact ⟨_, ⟨(comparisonUpperStarConstantSheafIso Λ (W i)).app M ≪≫ e.symm⟩⟩

/-- A constructible pro-étale sheaf is of étale origin: its pullbacks to the strata are, and the
immersions of the strata are quasi-compact and jointly surjective
(`comparisonUpperStar_essImage_of_finite`). -/
theorem comparisonUpperStar_essImage_of_isConstructible {X : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (hF : IsConstructible Λ F) : (ν^*(X)[ModuleCat.{u + 1} Λ]).essImage F := by
  obtain ⟨S, hS⟩ := hF
  refine comparisonUpperStar_essImage_of_finite S.immersion (fun x ↦ ?_) F fun i ↦
    comparisonUpperStar_essImage_of_isFiniteLocallyConstant (hS i)
  have hx : x ∈ ⋃ i, S.stratum i := S.iUnion_stratum_eq_univ ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  exact ⟨i, (S.range_immersion i).symm ▸ hi⟩

variable (Λ) in
/-- Blueprint `lem-sf-proetale-constructible-origin`: Constructible pro-étale coefficients are
of étale origin, clause (i).

At a finite coefficient ring `Λ`, the comparison pullback `ν^*` induces an equivalence between
the constructible sheaves of `Λ`-modules on the small étale site of `T` and the constructible
sheaves on its small pro-étale site. As `ν^*` is fully faithful
(`AlgebraicGeometry.ProEtale.full_comparisonUpperStar`,
`AlgebraicGeometry.ProEtale.faithful_comparisonUpperStar`), this says that a pro-étale sheaf is
constructible if and only if it is `ν^*` of a constructible étale sheaf. That `ν^*` preserves
constructibility is `isConstructible_comparisonUpperStar_obj`; the essential surjectivity is the
content of the lemma. -/
theorem isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj [Finite Λ]
    {T : Scheme.{u}} {F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)} :
    IsConstructible Λ F ↔
      ∃ G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), Scheme.IsConstructibleSheaf G ∧
        Nonempty ((ν^*(T)[ModuleCat.{u + 1} Λ]).obj G ≅ F) := by
  refine ⟨fun _ ↦ sorry, fun ⟨G, hG, ⟨e⟩⟩ ↦ ?_⟩
  exact isConstructible_of_iso e (isConstructible_comparisonUpperStar_obj G)

variable (Λ) in
/-- A constructible pro-étale sheaf is `ν^*` of a constructible étale sheaf
(`lem-sf-proetale-constructible-origin` (i)). -/
theorem exists_isConstructibleSheaf_iso_comparisonUpperStar_obj [Finite Λ] {T : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)} (hF : IsConstructible Λ F) :
    ∃ G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), Scheme.IsConstructibleSheaf G ∧
      Nonempty ((ν^*(T)[ModuleCat.{u + 1} Λ]).obj G ≅ F) :=
  (isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ).1 hF

end Comparison

end AlgebraicGeometry.ProEtale
