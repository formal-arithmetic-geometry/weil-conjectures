/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Paper.PowerTorsionSheafLimitModels
import Sheaf.Paper.PowerTorsionKoszulUnit
import Sheaf.Paper.PowerTorsionKoszulRoosExchange
import Sheaf.Paper.PowerTorsionKoszulQuotientCompleteness
import all Sheaf.Paper.IntegralOperationsWellDefined

/-! # Canonical completeness of limits of power-torsion sheaf complexes -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PrincipalKoszulStrictReplacement (uniformizer)

namespace WeilConjectures.PowerTorsionLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (T : AlgebraicGeometry.Scheme.{t})

/-- Canonical completeness, including the signed double-Roos interchange and the actual
quotient-reduction projections. The left-tensor Koszul presentation is identified with
the paper's right-tensor presentation by the standard signed tensor symmetry.

Source: blueprint main-20261015, sk-lem-sp-tower, completeness sentence;
Bhatt--Scholze Lemmas 3.5.4--3.5.7
(blueprint: lem-sp-power-torsion-sheaf-limit-complete).

Proof:
1. Obtain the natural unit and the single-complex nilpotent-action calculation from
lem-sp-left-koszul-nilpotent-unit. Apply the latter at each level with its own exponent.
2. Exact countable products imply that the strict Roos image of this levelwise
quasi-isomorphism is a quasi-isomorphism, by integralOperationsRoosQuasiIsoInvariant.
3. Use lem-sp-left-koszul-roos-exchange for beta, its signed coordinates and the
finite Koszul tensor exchange gamma. Its strict augmentation identity says that
Roos of the levelwise unit followed by beta and Roos of gamma inverse is the actual
unit of Roos Q. The last two maps are isomorphisms, proving that this unit is a
quasi-isomorphism. No common nilpotence exponent occurs.
4. Apply lem-sp-left-koszul-quotient-completeness to that arbitrary Roos complex.
It supplies one flat-term K-flat resolution, the actual quotient-limit comparison,
all canonical projection equations, the distinguished Roos triangle, and integral
derived completeness. Assemble these witnesses with the natural unit and beta. -/
theorem power_torsion_sheaf_limit_complete
    (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (hQ : ∀ n : ℕ, ∃ r : ℕ, 1 ≤ r ∧
      ∀ (a : ℤ) (U : T.ProEtᵒᵖ) (x : ((Q.obj (op n)).X a).val.obj U),
        (@id ((completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
          ((uniformizer l E T).val U)) ^ r • x = 0) :
    ∃ η : 𝟭 (CochainComplex (integralTowerModules l E T) ℤ) ⟶ completion l E T,
      (∀ P, η.app P = unit l E T P) ∧
      (∀ n : ℕ, QuasiIso (unit l E T (Q.obj (op n)))) ∧
      ∃ (β : (roos l E T).obj (Q ⋙ completion l E T) ≅
          (roos l E T).obj (columns l E T Q)),
        (∀ (p q : Bool) (k : ℤ) (n j : ℕ),
          β.hom.f k ≫ columnCoordinate l E T Q p q k n j =
            if p && q then -rowCoordinate l E T Q p q k n j
            else rowCoordinate l E T Q p q k n j) ∧
        (∀ (k : ℤ) (n j : ℕ),
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q false false k n j =
            coordinateZero l E T Q k n ≫
              (koszulRepresentativeAugmentation
                (completedIntegralCommRingSheafUnrestricted l E T)
                (Q.obj (op n)) (uniformizer l E T) j).f k ∧
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q true false k n j =
            coordinateOne l E T Q k n ≫
              (koszulRepresentativeAugmentation
                (completedIntegralCommRingSheafUnrestricted l E T)
                (Q.obj (op n)) (uniformizer l E T) j).f (k - 1) ∧
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q false true k n j = 0 ∧
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q true true k n j = 0) ∧
        QuasiIso (unit l E T ((roos l E T).obj Q)) ∧
        ∃ (P : (IntegralOnSlice.Good l E T none).FullSubcategory)
          (f : P.obj ⟶ (roos l E T).obj Q)
          (eP : DerivedCategory.Q.obj P.obj ≅ DerivedCategory.Q.obj ((roos l E T).obj Q))
          (s : DerivedCategory.Q.obj ((completion l E T).obj ((roos l E T).obj Q)) ≅
            DerivedCategory.Q.obj ((roos l E T).obj
              ((IntegralOnSlice.tower l E T none).obj P.obj))),
          QuasiIso f ∧ eP.hom = DerivedCategory.Q.map f ∧
          DerivedCategory.Q.map (unit l E T ((roos l E T).obj Q)) ≫ s.hom =
            eP.inv ≫ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none P.obj) ∧
          (∀ j : ℕ,
            DerivedCategory.Q.map (unit l E T ((roos l E T).obj Q)) ≫ s.hom ≫
                DerivedCategory.Q.map (evaluation l E T
                  ((IntegralOnSlice.tower l E T none).obj P.obj) j) =
              eP.inv ≫ DerivedCategory.Q.map
                (((IntegralOnSlice.augmentation l E T none).app P.obj).app (op j))) ∧
          (∃ (hprod : HasProduct (fun j : ℕ ↦
                (IntegralOnSlice.derivedTower l E T none P).obj (op j))),
            (fun [_hp : HasProduct (fun j : ℕ ↦
                (IntegralOnSlice.derivedTower l E T none P).obj (op j))] ↦
            ∃ (p : DerivedCategory.Q.obj ((roos l E T).obj Q) ⟶
                ∏ᶜ fun j : ℕ ↦ (IntegralOnSlice.derivedTower l E T none P).obj (op j))
            (δ : (∏ᶜ fun j : ℕ ↦
                (IntegralOnSlice.derivedTower l E T none P).obj (op j)) ⟶
              (DerivedCategory.Q.obj ((roos l E T).obj Q))⟦(1 : ℤ)⟧),
            IsDerivedLimitTriangle
              (fun j : ℕ ↦ (IntegralOnSlice.derivedTower l E T none P).map
                (homOfLE j.le_succ).op) (DerivedCategory.Q.obj ((roos l E T).obj Q)) p δ ∧
            ∀ j : ℕ, p ≫ Pi.π _ j = eP.inv ≫ DerivedCategory.Q.map
              (((IntegralOnSlice.augmentation l E T none).app P.obj).app (op j)))
              (_hp := hprod)) ∧
          IntegralOnSlice.IsComplete l E T none
            (DerivedCategory.Q.obj ((roos l E T).obj Q)) := by
  obtain ⟨η, hη, hnil⟩ := left_koszul_nilpotent_unit l E T
  have hlevel (n : ℕ) : QuasiIso (unit l E T (Q.obj (op n))) := by
    obtain ⟨r, hr, hkill⟩ := hQ n
    exact hnil (Q.obj (op n)) r hr hkill
  obtain ⟨β, hβ, hcoords, γ, hunit⟩ :=
    left_koszul_roos_exchange l E T η hη Q
  let α := Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η
  have hα (n : ℕ) : QuasiIso (α.app (op n)) := by
    change QuasiIso (𝟙 _ ≫ η.app (Q.obj (op n)))
    rw [Category.id_comp, hη]
    exact hlevel n
  have hroos : QuasiIso ((roos l E T).map α) :=
    integralOperationsRoosQuasiIsoInvariant l E T α hα
  have hu : QuasiIso (unit l E T ((roos l E T).obj Q)) := by
    rw [← hunit]
    change QuasiIso ((roos l E T).map α ≫ β.hom ≫ (roos l E T).map γ.inv)
    infer_instance
  refine ⟨η, hη, hlevel, β, hβ, hcoords, hu, ?_⟩
  exact left_koszul_quotient_completeness l E T ((roos l E T).obj Q) hu

end WeilConjectures.PowerTorsionLimit
