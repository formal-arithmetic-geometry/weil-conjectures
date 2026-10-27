/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Cospecialization
import WeilConjectures.ConstructibleSheaf.SpecializationCriterion

/-! # Constructible cospecialization criterion over arbitrary schemes

The constructible-topology proof of the specialization criterion works over arbitrary
schemes: its chosen etale neighbourhood is affine, hence spectral.
(blueprint: lem-sfb-constructible-cospecialization-local-system).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Local form of the specialization criterion.** Let `Y` be any scheme, `Λ`
noetherian and `G` a constructible sheaf of `Λ`-modules on `Y` all of whose cospecialization
maps are bijective. Then every point of `Y` lies in the image of an étale morphism `W ⟶ Y`
along which `G` pulls back to a constant sheaf. -/
private theorem exists_etale_constant_of_cospecialization
    [IsNoetherianRing Λ] {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G]
    (hG : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) {Ω' : Type u}
      [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s),
      Function.Bijective (cospecializationMap s t (ModuleCat.{u + 1} Λ) G).hom)
    (y : Y) :
    ∃ (W : Scheme.{u}) (i : W ⟶ Y), Etale i ∧ y ∈ Set.range i.base ∧
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G).IsConstant W.smallEtaleTopology := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  -- the stalk at a geometric point over `y` is finitely presented
  let s := Y.algClosurePoint y
  let M := ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G
  have : Module.Finite Λ M := moduleFinite_sheafFiber_of_isConstructibleSheaf G s
  have : Module.FinitePresentation Λ M := Module.finitePresentation_of_finite _ _
  -- spread the identity of `M` out to an affine pointed étale neighbourhood `(V, v)`
  obtain ⟨c, α, hα⟩ := exists_comp_toPresheafFiber_eq_id G s
  let V := c.obj.1
  have : IsAffine V.left := c.2
  have : Etale V.hom := V.prop
  let ψ := constantSheafSpread G V M α
  have : IsConstructibleSheaf ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G) :=
    IsConstructibleSheaf.upperStar V.hom G
  have : IsConstructibleSheaf
      ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    isConstructibleSheaf_constantSheaf M
  have : IsConstructibleSheaf (kernel ψ) := IsConstructibleSheaf.kernel ψ
  have : IsConstructibleSheaf (cokernel ψ) := IsConstructibleSheaf.cokernel ψ
  let Z := stalkZeroLocus (kernel ψ) ∩ stalkZeroLocus (cokernel ψ)
  let leg := (strictLocalizationConeAll s).π.app ((AffinePointedEtaleNeighborhood.ι s).obj c)
  -- at the geometric points coming from the strict localization, `ψ` is the cospecialization
  -- map on stalks, hence invertible
  have key (p : strictLocalization s) : leg.base p ∈ Z := by
    let t := (strictLocalization s).algClosurePoint p
    have hr : IsIso ((pointSmallEtale (t ≫ leg)).sheafFiber.map ψ) := by
      refine isIso_sheafFiber_map_constantSheafSpread G V M α (t ≫ leg)
        (q := t ≫ strictLocalizationToBase s) ((Category.assoc _ _ _).trans
          (congrArg (t ≫ ·) (strictLocalizationConeAll_π_app_hom s _)))
        ((cospecializationNeighborhoodFunctor s t).obj
          ((AffinePointedEtaleNeighborhood.ι s).obj c)).2 rfl ?_
      have e : α ≫ (pointSmallEtale (t ≫ strictLocalizationToBase s)).toPresheafFiber V
          ((cospecializationNeighborhoodFunctor s t).obj
            ((AffinePointedEtaleNeighborhood.ι s).obj c)).2 G.obj =
          cospecializationMap s t (ModuleCat.{u + 1} Λ) G := by
        erw [← toPresheafFiber_cospecializationMap s t _ G
          ((AffinePointedEtaleNeighborhood.ι s).obj c)]
        exact (Category.assoc _ _ _).symm.trans ((congrArg
          (· ≫ cospecializationMap s t (ModuleCat.{u + 1} Λ) G) hα).trans (Category.id_comp _))
      rw [e, ConcreteCategory.isIso_iff_bijective]
      exact hG s t
    obtain ⟨hK, hC⟩ := (isIso_sheafFiber_map_iff ψ (t ≫ leg)).1 hr
    have hpt : (t ≫ leg).base (IsLocalRing.closedPoint _) = leg.base p :=
      congrArg leg.base (algClosurePoint_base (strictLocalization s) p _)
    exact ⟨hpt ▸ mem_stalkZeroLocus_of_isZero_sheafFiber _ _ hK,
      hpt ▸ mem_stalkZeroLocus_of_isZero_sheafFiber _ _ hC⟩
  -- so the stalks of the kernel and cokernel vanish near the base point `v₀` of `V`
  let v₀ := c.obj.2.left.base (IsLocalRing.closedPoint _)
  have hZ (w : V.left) (hw : w ⤳ v₀) : w ∈ Z := by
    obtain ⟨p, hp⟩ := exists_strictLocalizationConeAll_π_app_base_eq s
      ((AffinePointedEtaleNeighborhood.ι s).obj c) hw
    exact hp ▸ key p
  have : SpectralSpace V.left := {}
  have hZo : IsOpen[constructibleTopology V.left] Z :=
    @IsOpen.inter V.left (constructibleTopology V.left) _ _
      (isOpen_constructibleTopology_stalkZeroLocus (kernel ψ))
      (isOpen_constructibleTopology_stalkZeroLocus (cokernel ψ))
  obtain ⟨O, hO, hv₀, hOZ⟩ := exists_isOpen_subset_of_isOpen_constructibleTopology hZo hZ
  let U : V.left.Opens := ⟨O, hO⟩
  refine ⟨U, U.ι ≫ V.hom, inferInstance, ⟨⟨v₀, hv₀⟩, ?_⟩, ?_⟩
  · have h : c.obj.2.left ≫ V.hom = s := CategoryTheory.Over.w c.obj.2
    exact (congrArg (fun f ↦ f.base (IsLocalRing.closedPoint _)) h).trans
      (algClosurePoint_base _ _ _)
  -- on `U` the morphism `ψ` is an isomorphism
  have hiso : IsIso ((U.ι)^*[ModuleCat.{u + 1} Λ].map ψ) := by
    refine isIso_of_isIso_sheafFiber_map _ fun z ↦ ?_
    let a := U.toScheme.algClosurePoint z
    have hz : (a ≫ U.ι).base (IsLocalRing.closedPoint _) ∈ Z := by
      rw [Scheme.Hom.comp_apply, algClosurePoint_base]
      exact hOZ z.2
    have h₁ : IsIso ((pointSmallEtale (a ≫ U.ι)).sheafFiber.map ψ) :=
      (isIso_sheafFiber_map_iff ψ (a ≫ U.ι)).2 ⟨hz.1 _ _ rfl, hz.2 _ _ rfl⟩
    have h₂ : IsIso ((pointSmallEtale a).sheafFiber.map ((U.ι)^*[ModuleCat.{u + 1} Λ].map ψ)) :=
      (NatIso.isIso_map_iff (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.ι a) ψ).2 h₁
    exact (NatIso.isIso_map_iff ((pointSmallEtale a).uliftSheafFiberIso _) _).2 h₂
  exact Sheaf.isConstant_of_iso _
    ((upperStarComp (ModuleCat.{u + 1} Λ) U.ι V.hom).app G ≪≫
      (asIso ((U.ι)^*[ModuleCat.{u + 1} Λ].map ψ)).symm ≪≫
      (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) U.ι).app M)

/-- **A constructible specialization criterion for local constancy.**
Let `Y` be any scheme, `Λ` a noetherian ring and `G` a
constructible sheaf of `Λ`-modules on the small étale site of `Y`. If for every geometric point
`s` of `Y` and every geometric point `t` of the strict localization `Y_(s)` the cospecialization
map `G_s ⟶ G_t` (`AlgebraicGeometry.Scheme.cospecializationMap`) is bijective, then `G` is
finite locally constant.

Source: the constructible-topology proof of
`WeilConjectures/ConstructibleSheaf/SpecializationCriterion.lean`. The proof uses
only that the chosen etale neighbourhood is affine and that the kernel and cokernel
are constructible; it does not require a Noetherian base. Spread the finitely presented
stalk, use cospecialization to show bijectivity at all generizations, and shrink using
the constructible open vanishing loci of the kernel and cokernel. These neighbourhoods
form an etale cover. This generalizes the source theorem by removing its unused
locally Noetherian base hypothesis; the stronger constructibility hypothesis is retained.
(blueprint: lem-sfb-constructible-cospecialization-local-system). -/
theorem isFiniteLocallyConstantSheaf_of_constructible_bijective_cospecialization
    [IsNoetherianRing Λ] {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G]
    (hG : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) {Ω' : Type u}
      [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s),
      Function.Bijective (cospecializationMap s t (ModuleCat.{u + 1} Λ) G).hom) :
    IsFiniteLocallyConstantSheaf G := by
  choose W i hi hy hc using exists_etale_constant_of_cospecialization G hG
  let 𝒰 : Cover.{u} etalePrecoverage Y := Cover.mkOfCovers Y W i (fun y ↦ ⟨y, hy y⟩) hi
  have hlc : IsLocallyConstantSheaf G :=
    ⟨⟨⟨𝒰, fun y ↦ (isConstant_over_iff_upperStar _ _ G).2 (hc y)⟩⟩⟩
  exact
    { toIsLocallyConstantSheaf := hlc
      toIsFiniteSheaf := ⟨fun _ _ _ s ↦ (ModuleCat.isFinitelyGenerated_iff _).2
        (moduleFinite_sheafFiber_of_isConstructibleSheaf G s)⟩ }

end AlgebraicGeometry.Scheme
