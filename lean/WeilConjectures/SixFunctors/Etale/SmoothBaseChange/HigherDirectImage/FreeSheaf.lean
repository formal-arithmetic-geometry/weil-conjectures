/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheafShiftedHom

/-! Free sheaf cohomology, filtered colimits, and pullback. -/

@[expose] public section

universe u w

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

open Scheme Etale

section FilteredColimit

variable (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]

/-- On a quasi-compact quasi-separated scheme, the cohomology `Hⁿ(Z, -)` of abelian sheaves
commutes with filtered colimits, by `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`. -/
lemma Etale.preservesColimitsOfShape_functorH (n : ℕ) (J : Type (u + 1)) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J (Sheaf.functorH.{u + 1, u + 1} Z.smallEtaleTopology n) := by
  refine ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨?_⟩⟩⟩
  obtain ⟨h₁, h₂⟩ := Scheme.H_map_isColimit_of_isFiltered_of_large Z hc n
  have : ReflectsColimitsOfShape J (forget AddCommGrpCat.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget AddCommGrpCat.{u + 1})
    (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun j x y hxy ↦ ?_))
  · obtain ⟨j, y, rfl⟩ := h₁ x
    exact ⟨j, y, rfl⟩
  · have hxy' : Sheaf.H.map (c.ι.app j) n x = Sheaf.H.map (c.ι.app j) n y := hxy
    obtain ⟨k, φ, hk⟩ := h₂ j (x - y) (by rw [map_sub, hxy', sub_self])
    refine ⟨k, φ, ?_⟩
    change Sheaf.H.map (K.map φ) n x = Sheaf.H.map (K.map φ) n y
    rw [← sub_eq_zero, ← map_sub]
    exact hk

/-- On a quasi-compact quasi-separated scheme `Z`, the cohomology `Hom(Λ_Z[0], N[0]⟦n⟧)` of a
sheaf of `Λ`-modules is the cohomology of its underlying abelian sheaf, naturally in `N`. -/
noncomputable def Etale.shiftedHomFunctorFreeSheafIso (n : ℕ) :
    Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) n ≅
      Etale.forget₂Sheaf Λ Z ⋙ Sheaf.functorH.{u + 1, u + 1} Z.smallEtaleTopology n :=
  NatIso.ofComponents
    (fun N ↦ ((Etale.shiftedHomFunctorObjAddEquivExt Λ _ N n).trans
      (AddEquiv.ofBijective (Etale.extFreeSheafToH Λ N n)
        (Etale.bijective_extFreeSheafToH Λ n N))).toAddCommGrpIso)
    (fun {N N'} g ↦ by
      ext f
      change Etale.extFreeSheafToH Λ N' n (Etale.shiftedHomFunctorObjAddEquivExt Λ _ N' n
          ((Etale.shiftedHomFunctor Λ _ n).map g f)) =
        Sheaf.H.map ((Etale.forget₂Sheaf Λ Z).map g) n
          (Etale.extFreeSheafToH Λ N n (Etale.shiftedHomFunctorObjAddEquivExt Λ _ N n f))
      rw [Etale.shiftedHomFunctorObjAddEquivExt_naturality, Etale.extFreeSheafToH_comp_mk₀])

/-- In negative degrees `q`, there are no shifted morphisms `A[0] ⟶ N[0]⟦q⟧`. -/
lemma Etale.isZero_shiftedHomFunctor_obj_of_neg {Z : Scheme.{u}}
    (A N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℤ} (hq : q < 0) :
    IsZero ((Etale.shiftedHomFunctor Λ A q).obj N) := by
  have : DerivedCategory.Plus.TStructure.t.IsGE
      ((shiftFunctor _ q).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) (-q) :=
    DerivedCategory.Plus.TStructure.t.isGE_shift _ 0 q (-q) (by omega)
  have : Subsingleton ((Etale.shiftedHomFunctor Λ A q).obj N) := ⟨fun a b ↦
    (DerivedCategory.Plus.TStructure.t.zero (show (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      (shiftFunctor _ q).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj N) from a) 0 (-q)
        (by omega)).trans
    (DerivedCategory.Plus.TStructure.t.zero (show (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      (shiftFunctor _ q).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj N) from b) 0 (-q)
        (by omega)).symm⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

end FilteredColimit

/-- Blueprint `lem-weil-pbc-cohomology-filtered-colimit` (subsection `sk-prop-h2`): Filtered
colimits of étale cohomology. Let `Z` be a quasi-compact and quasi-separated scheme. Then étale
cohomology `N ↦ Hᵠ(Z, N) = Hom(Λ_Z[0], N[0]⟦q⟧)` with coefficients in sheaves of `Λ`-modules
commutes with filtered colimits: `colim Hᵠ(Z, N_a) ≅ Hᵠ(Z, colim N_a)`.

The same statement for abelian sheaves is
`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`. As in the blueprint, there is no
restriction on the size of the filtered category beyond that of the coefficients: it may be any
filtered category in `Type (u + 1)`, the universe of the sheaves of `Λ`-modules.

The proof identifies the functor with abelian sheaf cohomology of the underlying abelian sheaf
(`AlgebraicGeometry.Etale.shiftedHomFunctorFreeSheafIso`) in nonnegative degrees; in negative
degrees it vanishes. -/
@[stacks 03Q6]
theorem Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject (Z : Scheme.{u})
    [CompactSpace Z] [QuasiSeparatedSpace Z] (q : ℤ) (J : Type (u + 1)) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J
      (Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) q) := by
  rcases le_or_gt 0 q with hq | hq
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    have := Etale.preservesColimitsOfShape_functorH Z n J
    exact preservesColimitsOfShape_of_natIso (Etale.shiftedHomFunctorFreeSheafIso Λ Z n).symm
  · have hz (N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
      Etale.isZero_shiftedHomFunctor_obj_of_neg Λ
        ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) N hq
    exact ⟨fun {K} ↦ ⟨fun {c} _ ↦ ⟨
      { desc s := (hz c.pt).to_ s.pt
        fac _ _ := (hz _).eq_of_src _ _
        uniq _ _ _ := (hz _).eq_of_src _ _ }⟩⟩⟩

/-- An isomorphism `A ≅ A'` identifies the functors `N ↦ Hom(A[0], N[0]⟦q⟧)` and
`N ↦ Hom(A'[0], N[0]⟦q⟧)`. -/
noncomputable def Etale.shiftedHomFunctorMapIso {Z : Scheme.{u}}
    {A A' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : A ≅ A') (q : ℤ) :
    Etale.shiftedHomFunctor Λ A q ≅ Etale.shiftedHomFunctor Λ A' q :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q)
    (preadditiveCoyoneda.mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e).symm.op)

section Pullback

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- An étale `Y`-scheme `W`, as an étale scheme over itself extended along its structure
morphism, is `W`. -/
noncomputable def Etale.overMapFinalObjectIso (W : Y.Etale) :
    (MorphismProperty.Over.map ⊤ W.prop).obj (Etale.finalObject W.left) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _) rfl

/-- The functor `N ↦ Hom((h^* Λ[W])[0], N[0]⟦q⟧)` is the cohomology functor of `W ×_X Y`
precomposed with restriction. -/
noncomputable def Etale.shiftedHomFunctorUpperStarFreeSheafIso (W : X.Etale) (q : ℤ) :
    Etale.shiftedHomFunctor Λ ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W)) q ≅
      (((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).hom)^*[ModuleCat.{u + 1} Λ] ⋙
        Etale.shiftedHomFunctor Λ
          ((Etale.freeSheaf Λ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left).obj
            (Etale.finalObject _)) q :=
  Etale.shiftedHomFunctorMapIso Λ (Etale.upperStarFreeSheafIso Λ h W ≪≫
    (Etale.freeSheaf Λ Y).mapIso (Etale.overMapFinalObjectIso _).symm ≪≫
    (Etale.etaleLowerShriekFreeSheafIso Λ _ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).prop
      (Etale.finalObject _)).symm) q ≪≫
  Etale.etaleLowerShriekShiftedHomIso Λ _ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).prop
    _ q

end Pullback

end AlgebraicGeometry
