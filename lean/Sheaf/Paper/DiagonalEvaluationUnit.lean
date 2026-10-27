/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.Paper.CanonicalSheafExt

/-! # The underlying unit of evaluated simultaneous reduction
Source: diagonal tower system proof, steps (2) and (4).
(blueprint: lem-sfb-diagonal-evaluation-unit). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  diagonalDerivedSingleCounit diagonalScalarExtension diagonalForget diagonalScalarAdjunction

section
variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  {ℓ : ℕ} {L : A ⥤ B} (U : B ⥤ A) [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L) (n : ℕ)

/-- Evaluate a strict system and forget its coefficient action.
Source: diagonal tower system proof, step (4)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
abbrev diagonalEvaluationForget : (ℕᵒᵖ ⥤ B) ⥤ A :=
  (evaluation ℕᵒᵖ B).obj (op n) ⋙ U

/-- The ordinary quotient unit before deriving it.
Source: diagonal tower system proof, step (2)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
def diagonalEvaluationQuotient : 𝟭 A ⟶ D.ordinary.E ⋙ diagonalEvaluationForget U n :=
  ad.unit ≫ Functor.whiskerRight (D.ordinary.π n) U

/-- A unit of evaluated reduction, normalized on complexes by the universal
counit. This records an actual natural transformation, rather than a collection
of unrelated maps on extension groups. The last field is its degree-zero
specialization, retaining the specified single-complex comparisons.
Source: diagonal tower system proof, steps (2) and (4)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
structure DiagonalEvaluationUnit where
  unit : 𝟭 (DerivedCategory A) ⟶ D.T ⋙ (diagonalEvaluationForget U n).mapDerivedCategory
  complexes : ∀ K : CochainComplex A ℤ,
    unit.app (DerivedCategory.Q.obj K) ≫
        (diagonalEvaluationForget U n).mapDerivedCategory.map (D.ε.app K) ≫
        (diagonalEvaluationForget U n).mapDerivedCategoryFactors.hom.app
          ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app K ≫
          (NatTrans.mapHomologicalComplex (diagonalEvaluationQuotient U ad D n)
            (.up ℤ)).app K)
  single : ∀ S : A,
    unit.app ((DerivedCategory.singleFunctor A 0).obj S) ≫
        (diagonalEvaluationForget U n).mapDerivedCategory.map
          (diagonalDerivedSingleCounit ℓ L D S) ≫
        ((diagonalEvaluationForget U n).mapDerivedCategorySingleFunctor 0).hom.app
          (D.ordinary.E.obj S) =
      (DerivedCategory.singleFunctor A 0).map
        (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S))

end

section FiniteForgetting
attribute [local semireducible] diagonalForget

/-- Restricting a finite module to p-adic scalars retains its underlying abelian sheaf.
Source: diagonal tower proof, step (4)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
@[irreducible] def diagonalFiniteForgetIso (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    cartierForget (diagonalResidue.{u} ℓ n) W ≅
      diagonalFiniteToPadic ℓ n W ⋙ diagonalForget ℓ W :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    rfl)

/-- The inverse of the finite forgetting comparison transports an underlying-map
HEq into the corresponding ordinary equality.
Source: diagonal tower proof, step (4)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
theorem diagonalFiniteForgetIso_transport (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (S : DiagonalAb W)
    (Q : Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (q : S ⟶ (diagonalForget ℓ W).obj ((diagonalFiniteToPadic ℓ n W).obj Q))
    (g : S ⟶ (cartierForget (diagonalResidue.{u} ℓ n) W).obj Q) (h : HEq q g) :
    q ≫ (diagonalFiniteForgetIso ℓ n W).inv.app Q = g := by
  unfold diagonalFiniteForgetIso
  simpa only [NatIso.ofComponents_inv_app, Iso.refl_inv, Category.comp_id] using! eq_of_heq h

end FiniteForgetting

/-- Evaluating simultaneous reduction has its quotient-normalized underlying unit.

Source: diagonal tower system proof, steps (2) and (4)
(blueprint: lem-sfb-diagonal-evaluation-unit).

Proof: resolve an abelian-sheaf complex by a termwise flat K-flat complex P.
Scalar extension to the constant p-adic ring is flat. Reduction at level n is
computed by P tensor Z/ell^(n+1), and the integral quotient map gives its unit.
The universal left-derived counit is invertible on P. Compose its inverse with
the quotient map, using the exact evaluation-and-forgetting comparison.
Comparison maps of K-flat resolutions commute with the quotient maps; their
quasi-isomorphisms remain quasi-isomorphisms after reduction. Thus these maps
descend to a natural transformation on the unbounded derived category.
Computing on a resolution of any K and using naturality of the universal
counit proves the complexes equation. Specialize to the single complex of S
and insert the single-complex comparison isomorphisms to obtain single.
On K-flat representatives the counit is invertible, so complexes determines
the unit there; essential surjectivity of such representatives gives uniqueness.
Neither Kummer exactness nor any choice of a roots system is involved. -/
theorem diagonal_evaluation_unit_exists (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) (n : ℕ) :
    Nonempty (DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) := by sorry

end AlgebraicGeometry.ProEtale
