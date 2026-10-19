/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction

/-! # An explicit tower of projective-line/open adjunctions

Source: blueprint cor-amb-affine-space-adjunction, proof steps 1--3 and 5--6.
(blueprint: def-amb-affine-space-adjunction-tower).
The functors are concrete composites; no existence theorem chooses their data.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The coordinate set used by the affine-space statement. -/
noncomputable abbrev ambientAffine (S : Scheme.{u}) (d : ℕ) := AffineSpace (ULift.{u} (Fin d)) S

/-- Split off the last coordinate. -/
def ambientCoordinateEquiv (d : ℕ) :
    ULift.{u} (Fin d) ⊕ PUnit.{u + 1} ≃ ULift.{u} (Fin (d + 1)) where
  toFun := Sum.elim (fun i ↦ ⟨i.down.castSucc⟩) (fun _ ↦ ⟨Fin.last d⟩)
  invFun i := if h : i.down.val < d then Sum.inl ⟨⟨i.down.val, h⟩⟩ else Sum.inr PUnit.unit
  left_inv := by
    rintro (⟨i⟩ | ⟨⟩)
    · simp
    · simp
  right_inv := by
    intro ⟨i⟩
    dsimp
    split
    · rfl
    · change (⟨Fin.last d⟩ : ULift (Fin (d + 1))) = ⟨i⟩
      congr 1
      apply Fin.ext
      simp only [Fin.val_last]
      omega

/-- Polynomial-coordinate identification with the affine line over the preceding space. -/
noncomputable def ambientSuccessorIso (S : Scheme.{u}) (d : ℕ) :
    ambientAffine S (d + 1) ≅ AffineSpace PUnit.{u + 1} (ambientAffine S d) :=
  AffineSpace.reindexIso S (ambientCoordinateEquiv d) ≪≫ AffineSpace.sumIso S

/-- The standard open chart used at the successor step. -/
noncomputable def ambientSuccessorChart (S : Scheme.{u}) (d : ℕ) :
    ambientAffine S (d + 1) ⟶ ProjectiveLine (ambientAffine S d) :=
  (ambientSuccessorIso S d).hom ≫ ProjectiveLine.affineChart (ambientAffine S d)

instance (S : Scheme.{u}) (d : ℕ) : IsOpenImmersion (ambientSuccessorChart S d) := by
  unfold ambientSuccessorChart
  infer_instance

/-- The chart followed by the two projections is the affine-space projection. -/
lemma ambientSuccessorChart_over (S : Scheme.{u}) (d : ℕ) :
    ambientSuccessorChart S d ≫ (ProjectiveLine (ambientAffine S d) ↘ ambientAffine S d) ≫
      (ambientAffine S d ↘ S) = (ambientAffine S (d + 1) ↘ S) := by
  simp only [ambientSuccessorChart, ambientSuccessorIso, Iso.trans_hom,
    Category.assoc, ProjectiveLine.affineChart_over_assoc,
    AffineSpace.sumIso_hom_over_over, AffineSpace.reindexIso_hom,
    AffineSpace.reindex_over]

instance ambientAffine_isNoetherian (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    IsNoetherian (ambientAffine S d) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (ambientAffine S d ↘ S)
  have := QuasiCompact.compactSpace_of_compactSpace (ambientAffine S d ↘ S)
  exact ⟨⟩

/-- At dimension zero, use exact sum extension along the isomorphism to the base. -/
noncomputable def ambientTowerLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A (ambientAffine S d) ⥤ DerivedCategoryModule A S
  | 0 => (etaleLowerShriek (ModuleCat.{u + 1} A) (ambientAffine S 0 ↘ S)
      inferInstance).mapDerivedCategory
  | d + 1 => (openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (ambientSuccessorChart S d)).mapDerivedCategory ⋙
      ordinaryFinitePushforward A (ProjectiveLine (ambientAffine S d) ↘ ambientAffine S d) ⋙
      ambientTowerLeft A S d

/-- The reversed composite of the projective-line and open right adjoints. -/
noncomputable def ambientTowerRight (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A S ⥤ DerivedCategoryModule A (ambientAffine S d)
  | 0 => (upperStar (ModuleCat.{u + 1} A) (ambientAffine S 0 ↘ S)).mapDerivedCategory
  | d + 1 => (ambientTowerRight A N hA S d ⋙ ordinaryFiniteP1Right A N hA
      (ambientAffine S d)) ⋙
      (upperStar (ModuleCat.{u + 1} A) (ambientSuccessorChart S d)).mapDerivedCategory

/-- Compose the open and projective-line adjunctions at each coordinate.
Source: blueprint cor-amb-affine-space-adjunction, proof steps 2, 3, 5 and 6.
(blueprint: def-amb-affine-space-adjunction-tower). -/
theorem nonempty_ambientTowerAdjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty (ambientTowerLeft A S d ⊣ ambientTowerRight A N hA S d) := by
  induction d with
  | zero => exact ⟨derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      (ambientAffine S 0 ↘ S) inferInstance⟩
  | succ d ih =>
    obtain ⟨adj⟩ := ih
    have hT : IsUnit (N : Γ(ambientAffine S d, ⊤)) := by
      simpa only [map_natCast] using hS.map (ambientAffine S d ↘ S).appTop.hom
    obtain ⟨p1, _⟩ := exists_projectiveLineFullAdjunction N hN A hA (ambientAffine S d) hT
    exact ⟨(derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      (ambientSuccessorChart S d)).comp (p1.comp adj)⟩

/-- The explicit zero equation for the right tower. -/
lemma ambientTowerRight_zero (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) :
    ambientTowerRight A N hA S 0 =
      (upperStar (ModuleCat.{u + 1} A) (ambientAffine S 0 ↘ S)).mapDerivedCategory := rfl

/-- The explicit successor equation for the right tower. -/
lemma ambientTowerRight_succ (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) (d : ℕ) :
    ambientTowerRight A N hA S (d + 1) =
      (ambientTowerRight A N hA S d ⋙ ordinaryFiniteP1Right A N hA (ambientAffine S d)) ⋙
        (upperStar (ModuleCat.{u + 1} A) (ambientSuccessorChart S d)).mapDerivedCategory := rfl

attribute [irreducible] ambientTowerRight

end AlgebraicGeometry.Etale
