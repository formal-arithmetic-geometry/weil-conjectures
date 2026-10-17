/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.FiniteMorphism
public import WeilConjectures.ConstructibleSheaf.FiniteTypePushforward
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction

/-!
# Constructibility on the projective line from constant coefficients on curves

Let `S` be of finite type over a field `k` and `Λ` a finite ring. This file reduces the
constructibility of the higher direct images along `π : ℙ¹_S ⟶ S`
(`thm-fin-projective-line-constructible`) to the case of constant coefficients with finite
values on projective families of curves (`cor-fin-projective-curve-finite-group`), following the
blueprint proof.

A constructible sheaf `Q` on `ℙ¹_S` embeds into a finite direct sum `G = ⨁ᵢ (hᵢ)_* Mᵢ` of
direct images of constant sheaves with finite values along finite morphisms `hᵢ : Yᵢ ⟶ ℙ¹_S`
(`lem-fin-finite-type-pushforward-embedding`). The sheaf `G` is constructible, and
`Rπ_*((hᵢ)_* Mᵢ) = R(hᵢ ≫ π)_* Mᵢ` since `(hᵢ)_*` is exact. Over an affine base, `hᵢ ≫ π` is
projective (`lem-fin-finite-over-projective`), and its geometric fibres are finite over projective
lines, so have dimension at most one. The resolution principle
`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_exists_mono` concludes; the general base
is covered by affine opens, over which `ℙ¹` restricts to the projective line.

## Main statements

- `AlgebraicGeometry.Etale.topologicalKrullDim_pullback_le_one_of_isFinite`: a scheme finite over
  `ℙ¹_S` has geometric fibres of dimension at most one over `S`.
- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_projectiveLine_of_isAffine`: the
  reduction over an affine base.
- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_projectiveLine_of_constantSheaf`: the
  reduction over a base of finite type over `k`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme ProjectiveSpace

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-- **Geometric fibres of finite covers of `ℙ¹`.** If `h : Y ⟶ ℙ¹_S` is finite, every fibre of
`Y ⟶ S` over a point `Spec Ω ⟶ S` with values in a field has dimension at most one: it is finite
over the projective line `ℙ¹_Ω`, being the base change of `h`. -/
lemma topologicalKrullDim_pullback_le_one_of_isFinite {S Y : Scheme.{u}}
    (h : Y ⟶ ProjectiveLine S) [IsFinite h] (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ S) :
    topologicalKrullDim (pullback (h ≫ ProjectiveLine S ↘ S) s : Scheme.{u}) ≤ 1 := by
  have w : pullback.snd (h ≫ ProjectiveLine S ↘ S) s ≫ s =
      (pullback.fst (h ≫ ProjectiveLine S ↘ S) s ≫ h) ≫ ProjectiveLine S ↘ S := by
    rw [Category.assoc, ← pullback.condition]
  have hφ := isPullback_liftBaseChange _ (IsPullback.of_hasPullback (h ≫ ProjectiveLine S ↘ S) s) w
  have : IsFinite (liftBaseChange _ _ w) := MorphismProperty.of_isPullback hφ inferInstance
  exact ((liftBaseChange _ _ w).topologicalKrullDim_le_of_locallyQuasiFinite).trans
    (topologicalKrullDim_projectiveLine_le_one Ω)

/-- A constant sheaf of `Λ`-modules with finite value is constructible. -/
lemma isConstructibleSheaf_constantSheaf {X : Scheme.{u}} (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsConstructibleSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  (isFiniteLocallyConstantSheaf_constantSheaf M).isConstructibleSheaf

/-- **Reduction of `𝒞(ℙ¹_S ⟶ S)` to curves, over an affine base.** Let `S` be affine and of
finite type over `k`. Suppose that for every projective morphism `f : Y ⟶ S` whose geometric
fibres have dimension at most one, and every finite `Λ`-module `M`, the higher direct images
`Rᵠf_* M` of the constant sheaf `M` are constructible. Then `𝒞(ℙ¹_S ⟶ S)` holds. -/
theorem hasConstructibleDirectImages_projectiveLine_of_isAffine {S : Scheme.{u}} [IsAffine S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (h : ∀ {Y : Scheme.{u}} (f : Y ⟶ S) {n : Type u} [Finite n] (i : Y ⟶ ℙ(n; S))
      [IsClosedImmersion i] (_ : i ≫ ℙ(n; S) ↘ S = f)
      (_ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
      (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ),
      IsConstructibleSheaf ((homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          ((singleFunctor _ 0).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))) :
    HasConstructibleDirectImages Λ (ProjectiveLine S ↘ S) := by
  have : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S ≫ aS)
  have : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S ≫ aS)
  have : IsNoetherian (ProjectiveLine S) := {}
  refine hasConstructibleDirectImages_of_exists_mono _ fun Q hQ ↦ ?_
  obtain ⟨r, Y, g, _, M, _, φ, _⟩ :=
    exists_mono_biproduct_lowerStar_of_locallyOfFiniteType Λ (ProjectiveLine S ↘ S ≫ aS) Q
  let G : Fin r → Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun i ↦
    ((g i)_*[ModuleCat.{u + 1} Λ]).obj
      ((constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))
  have hG (i : Fin r) : IsConstructibleSheaf (G i) :=
    have := isConstructibleSheaf_constantSheaf (X := Y i) (M i)
    IsConstructibleSheaf.lowerStar_of_isFinite (g i) _
  refine ⟨⨁ G, φ, inferInstance, IsConstructibleSheaf.biproduct G, ?_⟩
  let P := (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).inverseImage
    (R((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ]))
  have hP (i : Fin r) : P ((singleFunctor _ 0).obj (G i)) := by
    obtain ⟨m, _, j, _, hj⟩ :=
      exists_isClosedImmersion_of_isFinite (ProjectiveLine S ↘ S) (𝟙 _) (Category.id_comp _) (g i)
    exact (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).prop_of_iso
      (rightDerivedLowerStarSingleLowerStarIso (g i) _ _).symm fun q ↦
        h _ j hj (fun Ω _ _ s ↦ topologicalKrullDim_pullback_le_one_of_isFinite (g i) Ω s) (M i) q
  exact P.prop_of_iso (((singleFunctor _ 0).mapBiproduct G).symm)
    (P.prop_of_iso (biproduct.isoProduct _).symm (P.prop_pi _ hP))

/-- **Reduction of `𝒞(ℙ¹_S ⟶ S)` to curves.** Let `S` be of finite type over `k` and `Λ` a
finite ring killed by an integer invertible in `k`. Suppose that for every scheme `T` of finite
type over `k`, every projective morphism `f : Y ⟶ T` whose geometric fibres have dimension at
most one, and every finite `Λ`-module `M`, the higher direct images `Rᵠf_* M` of the constant
sheaf `M` are constructible (this is `cor-fin-projective-curve-finite-group`). Then
`𝒞(ℙ¹_S ⟶ S)` holds (`thm-fin-projective-line-constructible`). -/
theorem hasConstructibleDirectImages_projectiveLine_of_constantSheaf
    [HasInvertibleExponent Λ (Spec (.of k))] {S : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (h : ∀ (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
      [HasInvertibleExponent Λ T] {Y : Scheme.{u}} (f : Y ⟶ T) {n : Type u} [Finite n]
      (i : Y ⟶ ℙ(n; T)) [IsClosedImmersion i] (_ : i ≫ ℙ(n; T) ↘ T = f)
      (_ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T),
        topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
      (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ),
      IsConstructibleSheaf ((homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          ((singleFunctor _ 0).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))) :
    HasConstructibleDirectImages Λ (ProjectiveLine S ↘ S) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  intro F hF q
  refine IsConstructibleSheaf.of_iSup_eq_top (fun U : S.affineOpens ↦ (U : S.Opens))
    (iSup_affineOpens_eq_top S) _ fun U ↦ ?_
  have : IsAffine (U : S.Opens) := U.2
  have : HasInvertibleExponent Λ (U : S.Opens) := .of_hom ((U : S.Opens).ι ≫ aS)
  have := hasConstructibleDirectImages_projectiveLine_of_isAffine (Λ := Λ) ((U : S.Opens).ι ≫ aS)
    (h _ ((U : S.Opens).ι ≫ aS)) _
    (IsConstructibleSheaf.upperStar (ProjectiveSpace.map _ (U : S.Opens).ι) F) q
  exact IsConstructibleSheaf.of_iso
    (upperStarHomologyRightDerivedLowerStarIso (isPullback_map _ (U : S.Opens).ι) F q).symm

end Etale

end AlgebraicGeometry
