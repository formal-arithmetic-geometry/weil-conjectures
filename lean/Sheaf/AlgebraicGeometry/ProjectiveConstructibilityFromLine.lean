/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation
import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.ExtensionByZero
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-!
# Projective constructibility from the projective line

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-projective-from-line.md`
(blueprint: lem-finrepair-projective-from-line).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Closed pushforward is exact and preserves constructibility. The target is locally
Noetherian, so its open complement is quasi-compact. -/
private theorem constructibleHigherDirectImages_closed
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hS : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) [IsClosedImmersion f] :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  intro q F hF
  rw [Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf] at hF ⊢
  have := hF
  let p := lowerStar (ModuleCat.{u + 1} Λ) f
  let e := p.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≪≫
    (p.mapDerivedCategoryPlusSingleFunctor 0).app F
  cases q with
  | zero =>
    have : Scheme.IsConstructibleSheaf (p.obj F) :=
      Scheme.IsConstructibleSheaf.lowerStar_of_isClosedImmersion_of_quasiCompact f F
    let e0 : higherDirectImage Λ f 0 F ≅ p.obj F :=
      (DerivedCategory.Plus.homologyFunctor _ 0).mapIso e ≪≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app (p.obj F)
    exact Scheme.IsConstructibleSheaf.of_iso e0.symm
  | succ q =>
    let eq : higherDirectImage Λ f (q + 1) F ≅
        (DerivedCategory.Plus.homologyFunctor _ (q + 1)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (p.obj F)) :=
      (DerivedCategory.Plus.homologyFunctor _ (q + 1)).mapIso e
    have hz : Limits.IsZero ((DerivedCategory.Plus.homologyFunctor _ (q + 1)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (p.obj F))) := by
      change Limits.IsZero ((_root_.DerivedCategory.homologyFunctor _ (q + 1)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (p.obj F)))
      exact (_root_.DerivedCategory.isLE_iff _ 0).1 inferInstance _ (by omega)
    exact Scheme.IsConstructibleSheaf.of_isZero (hz.of_iso eq)

/-- Invertibility of the annihilator pulls back along the map on global sections. -/
private theorem coefficients_pullback (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) (hS : IsSmoothBaseChangeCoefficients N Λ S) :
    IsSmoothBaseChangeCoefficients N Λ X := by
  refine ⟨hS.1, hS.2.1, hS.2.2.1, ?_⟩
  simpa using hS.2.2.2.map (f.appTop.hom)

/-- If every projective-line projection over a finite-type `k`-scheme satisfies `C`,
then every projective morphism between finite-type `k`-schemes satisfies `C`.
All coefficient-bearing schemes satisfy the fixed coefficient convention.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-projective-from-line.md`
(blueprint: lem-finrepair-projective-from-line).

Proof:
1. Use the source library's recursive `projectiveLinePow` and its projection.
   Properness of projective-space projections gives finite type at every stage;
   composition gives finite type over `k`. Pull back the coefficient convention.
2. A closed immersion has exact direct image by finite-direct-image exactness.
   Since its target is locally Noetherian, its open complement is quasi-compact,
   so closed pushforward preserves constructibility. Compare the finite-value and
   finite-stalk predicates. Its derived image of a sheaf in degree zero is the
   ordinary pushforward in degree zero, and has zero homology in positive degrees.
3. Induct on the tower, using step 2 for the identity and the projective-line
   hypothesis followed by `hasConstructibleHigherDirectImages_comp` at each successor.
4. Choose the global closed projective embedding. For a nonempty finite coordinate
   type, `ProjectiveSpace.exists_isFinite_surjective_projectiveLinePow` supplies
   the finite surjective cover, including the dimension-zero case. Apply
   `hasConstructibleHigherDirectImages_of_finite_surjective` and step 3.
   For an empty coordinate type projective space is empty, so its projection is a
   closed immersion and step 2 applies.
5. Compose the closed embedding with the projective-space projection by
   `hasConstructibleHigherDirectImages_comp`. -/
theorem hasConstructibleHigherDirectImages_of_projectiveLine
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hline : ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      (hP : IsSmoothBaseChangeCoefficients N Λ (ProjectiveSpace (ULift.{u} (Fin 2)) T))
      (hT : IsSmoothBaseChangeCoefficients N Λ T),
      @HasConstructibleHigherDirectImages k _ N Λ _ _
        (ProjectiveSpace (ULift.{u} (Fin 2)) T) T _ _
        (inferInstanceAs (LocallyOfFiniteType
          ((ProjectiveSpace (ULift.{u} (Fin 2)) T ↘ T) ≫ T ↘ Spec (.of k))))
        (inferInstanceAs (QuasiCompact
          ((ProjectiveSpace (ULift.{u} (Fin 2)) T ↘ T) ≫ T ↘ Spec (.of k))))
        _ _ hP hT (ProjectiveSpace (ULift.{u} (Fin 2)) T ↘ T))
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hS : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) [IsProjective f] :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  classical
  let Z := fun n ↦ ProjectiveSpace.projectiveLinePow n S
  let a := fun n ↦ ProjectiveSpace.projectiveLinePowProj n S ≫ S ↘ Spec (.of k)
  have hft (n : ℕ) : LocallyOfFiniteType (a n) := by
    induction n with
    | zero => simpa [a, ProjectiveSpace.projectiveLinePowProj] using
        inferInstanceAs (LocallyOfFiniteType (S ↘ Spec (.of k)))
    | succ n ih =>
      dsimp [a, ProjectiveSpace.projectiveLinePowProj]
      rw [Category.assoc]
      exact locallyOfFiniteType_comp _ _ (hg := ih)
  have hqc (n : ℕ) : QuasiCompact (a n) := by
    induction n with
    | zero => simpa [a, ProjectiveSpace.projectiveLinePowProj] using
        inferInstanceAs (QuasiCompact (S ↘ Spec (.of k)))
    | succ n ih =>
      dsimp [a, ProjectiveSpace.projectiveLinePowProj]
      rw [Category.assoc]
      have : QuasiCompact (a n) := ih
      exact quasiCompact_comp _ _
  let instOver (n : ℕ) : (Z n).Over (Spec (.of k)) := ⟨a n⟩
  have instFT (n : ℕ) : LocallyOfFiniteType (Z n ↘ Spec (.of k)) := hft n
  have instQC (n : ℕ) : QuasiCompact (Z n ↘ Spec (.of k)) := hqc n
  let hZ (n : ℕ) : IsSmoothBaseChangeCoefficients N Λ (Z n) :=
    coefficients_pullback N Λ (ProjectiveSpace.projectiveLinePowProj n S) hS
  have hpow (n : ℕ) : HasConstructibleHigherDirectImages k N Λ (hZ n) hS
      (ProjectiveSpace.projectiveLinePowProj n S) := by
    induction n with
    | zero =>
      change HasConstructibleHigherDirectImages k N Λ (hZ 0) hS (𝟙 S)
      have : IsClosedImmersion (𝟙 S) := inferInstance
      exact constructibleHigherDirectImages_closed k N Λ (hZ 0) hS (𝟙 S)
    | succ n ih =>
      exact hasConstructibleHigherDirectImages_comp k N Λ (hZ (n + 1)) (hZ n) hS
        (ProjectiveLine (Z n) ↘ Z n) (ProjectiveSpace.projectiveLinePowProj n S)
        (hline (Z n) (hZ (n + 1)) (hZ n)) ih
  obtain ⟨n, hn, i, hi, rfl⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  have : Finite n := hn
  have : IsClosedImmersion i := hi
  have : LocallyOfFiniteType (ProjectiveSpace n S ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType ((ProjectiveSpace n S ↘ S) ≫ S ↘ Spec (.of k)))
  have : QuasiCompact (ProjectiveSpace n S ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact ((ProjectiveSpace n S ↘ S) ≫ S ↘ Spec (.of k)))
  let hP : IsSmoothBaseChangeCoefficients N Λ (ProjectiveSpace n S) :=
    coefficients_pullback N Λ (ProjectiveSpace n S ↘ S) hS
  have hp : HasConstructibleHigherDirectImages k N Λ hP hS (ProjectiveSpace n S ↘ S) := by
    cases isEmpty_or_nonempty n with
    | inl hn =>
      have : IsEmpty (ProjectiveSpace n S) := inferInstance
      exact constructibleHigherDirectImages_closed k N Λ hP hS (ProjectiveSpace n S ↘ S)
    | inr hn =>
      obtain ⟨m, σ, hfinite, hsurj, hσ⟩ :=
        ProjectiveSpace.exists_isFinite_surjective_projectiveLinePow n S
      have : IsFinite σ := hfinite
      have : Surjective σ := hsurj
      apply hasConstructibleHigherDirectImages_of_finite_surjective k N Λ hP hS (hZ m)
        (ProjectiveSpace n S ↘ S) σ
      rw [hσ]
      exact hpow m
  exact hasConstructibleHigherDirectImages_comp k N Λ hX hP hS i
    (ProjectiveSpace n S ↘ S) (constructibleHigherDirectImages_closed k N Λ hX hP i) hp

end AlgebraicGeometry.Etale
