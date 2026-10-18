/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation

import Sheaf.AlgebraicGeometry.ProjectiveLineConstructible
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
import WeilConjectures.ConstructibleSheaf.ExtensionByZero

/-!
# Constructibility of projective direct images

For a finite ring `Λ` killed by an integer invertible in a field `k`, this file proves that
every projective morphism `f` between schemes of finite type over `k` satisfies `𝒞(f)`: its
higher direct images preserve constructibility.

- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_projectiveLine`
  (`thm-fin-projective-line-constructible`): the projective line `ℙ¹_S ⟶ S`, by resolving a
  constructible sheaf by finite pushforwards of constant sheaves and using the case of curves;
- `AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_projectiveLine`
  (`lem-finrepair-projective-from-line`): from the projective line to all projective morphisms,
  through `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S` (finite and surjective) and composition;
- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isClosedImmersion`
  (`thm-fin-projective-constructibility-complete`).

A morphism `f : X ⟶ S` is projective (`def-pc-projective-morphism`) if it is the composite of a
closed immersion `X ⟶ ℙ(N; S)`, for a finite type `N` of homogeneous coordinates, with the
structure morphism; quasi-compactness is automatic here, `S` being Noetherian.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

private theorem constructibleDirectImages_closedImmersion
    {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}}
    [IsNoetherian Y] (p : X ⟶ Y) [IsClosedImmersion p] :
    HasConstructibleDirectImages Λ p := by
  intro F hF
  have : IsConstructibleSheaf F := hF
  have : IsConstructibleSheaf ((p)_*[ModuleCat.{u + 1} Λ].obj F) :=
    IsConstructibleSheaf.lowerStar_of_isClosedImmersion_of_quasiCompact p F
  let e : (R((p)_*[ModuleCat.{u + 1} Λ])).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((p)_*[ModuleCat.{u + 1} Λ].obj F) :=
    (rightDerivedFunctorLowerStarIsoMapDerivedCategory _ p).app _ ≪≫
      (((p)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F
  exact (DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y).prop_of_iso e.symm
    (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0).2

/-- Blueprint `thm-fin-projective-line-constructible`: Constructible coefficients on the
projective line.

Let `S` be of finite type over a field `k`, and let `Λ` be a finite ring killed by an integer
invertible in `k`. For every constructible sheaf `F` of `Λ`-modules on `ℙ¹_S`, every higher
direct image `Rᵠπ_* F` along `π : ℙ¹_S ⟶ S` is constructible. -/
theorem hasConstructibleDirectImages_projectiveLine [HasInvertibleExponent Λ (Spec (.of k))]
    {S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] :
    HasConstructibleDirectImages Λ (ProjectiveLine S ↘ S) := by
  let : S.Over (Spec (.of k)) := ⟨aS⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of k)) := by
    change LocallyOfFiniteType aS
    infer_instance
  have : QuasiCompact (S ↘ Spec (.of k)) := by
    change QuasiCompact aS
    infer_instance
  obtain ⟨n, hn, hΛ, hu⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Spec (.of k))
  have hc : IsSmoothBaseChangeCoefficients n Λ (Spec (.of k)) :=
    ⟨hn, inferInstance, hΛ, hu⟩
  intro F hF q
  have hcF := isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine
    k S n Λ hc F ((Scheme.isConstructibleEtaleModuleSheaf_iff F).2 hF) q
  have hC : IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (ProjectiveLine S ↘ S)).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff _).1 hcF
  have : IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus ⋙
          _root_.DerivedCategory.Plus.ι).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
    exact hC
  exact IsConstructibleSheaf.of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)))

/-- Blueprint `lem-finrepair-projective-from-line`: Projective constructibility from
projective-line constructibility.

Suppose `𝒞(ℙ¹_T ⟶ T)` holds for every scheme `T` of finite type over `k`. Then `𝒞(f)` holds for
every projective morphism `f : X ⟶ S` with `S` of finite type over `k`: here `f` is the
composite of a closed immersion `e : X ⟶ ℙ(N; S)` with the structure morphism. -/
theorem HasConstructibleDirectImages.of_projectiveLine
    (h : ∀ (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT],
      HasConstructibleDirectImages Λ (ProjectiveLine T ↘ T))
    {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) (N : Type u) [Finite N] (e : X ⟶ ℙ(N; S)) [IsClosedImmersion e]
    (he : e ≫ ℙ(N; S) ↘ S = f) : HasConstructibleDirectImages Λ f := by
  classical
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  have : IsLocallyNoetherian ℙ(N; S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(N; S) ↘ S)
  have : CompactSpace ℙ(N; S) :=
    QuasiCompact.compactSpace_of_compactSpace (ℙ(N; S) ↘ S)
  have : IsNoetherian ℙ(N; S) := {}
  have hp : HasConstructibleDirectImages Λ (ℙ(N; S) ↘ S) := by
    cases isEmpty_or_nonempty N with
    | inl hN =>
      have : IsEmpty N := hN
      exact constructibleDirectImages_closedImmersion _
    | inr hN =>
      have : Nonempty N := hN
      have hproper : ∀ m, IsProper (ProjectiveSpace.projectiveLinePowProj m S) := by
        intro m
        induction m with
        | zero => change IsProper (𝟙 S); infer_instance
        | succ m ih =>
          change IsProper ((ProjectiveLine (ProjectiveSpace.projectiveLinePow m S) ↘
            ProjectiveSpace.projectiveLinePow m S) ≫ ProjectiveSpace.projectiveLinePowProj m S)
          have := ih
          infer_instance
      have hpow : ∀ m, HasConstructibleDirectImages Λ
          (ProjectiveSpace.projectiveLinePowProj m S) := by
        intro m
        induction m with
        | zero => exact constructibleDirectImages_closedImmersion (𝟙 S)
        | succ m ih =>
          have := hproper m
          exact (h _ (ProjectiveSpace.projectiveLinePowProj m S ≫ aS)).comp ih
      obtain ⟨m, σ, hfin, hsurj, hσ⟩ :=
        ProjectiveSpace.exists_isFinite_surjective_projectiveLinePow N S
      have := hfin
      have := hsurj
      apply HasConstructibleDirectImages.of_comp_of_isFinite ((ℙ(N; S) ↘ S) ≫ aS) _ σ
      rw [hσ]
      exact hpow m
  rw [← he]
  exact (constructibleDirectImages_closedImmersion e).comp hp

/-- Blueprint `thm-fin-projective-constructibility-complete`: Projective direct-image
constructibility.

Let `Λ` be a finite ring killed by an integer invertible in the field `k`. Every projective
morphism `f : X ⟶ S` with `S` of finite type over `k` (so `f` is the composite of a closed
immersion `e : X ⟶ ℙ(N; S)` with the structure morphism) satisfies `𝒞(f)`. -/
theorem hasConstructibleDirectImages_of_isClosedImmersion
    [HasInvertibleExponent Λ (Spec (.of k))] {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) (N : Type u) [Finite N]
    (e : X ⟶ ℙ(N; S)) [IsClosedImmersion e] (he : e ≫ ℙ(N; S) ↘ S = f) :
    HasConstructibleDirectImages Λ f :=
  HasConstructibleDirectImages.of_projectiveLine
    (fun _ aT _ _ ↦ hasConstructibleDirectImages_projectiveLine aT) aS f N e he

end Etale

end AlgebraicGeometry
