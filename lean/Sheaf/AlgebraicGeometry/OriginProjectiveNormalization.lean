/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module
public import Sheaf.AlgebraicGeometry.OriginBoundaryCounitData

/-!
Geometric parts of the origin comparison.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2, and sk-prop-an Step 5(d).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors

section
universe oC oD vC vD
variable {C : Type oC} {D : Type oD} [Category.{vC} C] [Category.{vD} D]
/-- The two normalization equations, with category instances shared before specialization.
Source: rank-one Thom Step 2 (blueprint: lem-pur-origin-projective-normalization). -/
def originNormalizationEquations (G : C ⥤ D) {B X K U : C} {R : D}
    (b : B ⟶ K) (e : X ⟶ B) (unit : U ⟶ B) (chern : U ⟶ K)
    (eta : R ⟶ G.obj U) (lambda : R ≅ G.obj X) : Prop :=
  unit ≫ b = chern ∧ lambda.hom ≫ G.map e = eta ≫ G.map unit
end

/-- Positive projective Chern and section-one normalization for a fixed boundary pair.
Source: rank-one Thom Step 2; Stacks 03FD and 03PL
(blueprint: lem-pur-origin-projective-normalization). -/
structure OriginProjectiveNormalization (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (d : OriginBoundaryCounitData A N hA S) where
  chern : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
    (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  sourceIso : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj (ModuleCat.of A A) ≅
    (originCompactSections A S).obj
      ((DerivedCategory.singleFunctor _ 0).obj (originAffineSheaf A S))
  divisor_iso : Nonempty (Scheme.Modules.dual (ProjectiveLine.infinity S).ker.toModules ≅
    ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)
  divisor_transition : Nonempty (ProjectiveLine.TwistData S 1
    (Scheme.Modules.dual (ProjectiveLine.infinity S).ker.toModules))
  chern_normalization : ordinaryFiniteP1ChernSpec A N hA S d.hP chern
  normalizations : originNormalizationEquations (originSections A (ProjectiveLine S))
    (originBoundaryArrow A N hA (ProjectiveLine S) _ d.projectiveClass)
    (originSupportCounit A S d.restriction)
    ((DerivedCategory.singleFunctor _ 0).map
      (supportedConstantUnit A (ProjectiveLine.infinity S))) chern
    (originConstantSectionsUnit A (ProjectiveLine S)) sourceIso

/-- Positive divisor Chern normalization and compact-point section normalization.
Source: rank-one Thom Step 2; Stacks 03FD, 03PL and 0D6E
(blueprint: lem-pur-origin-projective-normalization).
Proof: on D(x0) and D(x1), the ideal of [1:0] has frames t and 1.
Their dual frames have transition g0=t^(-1)g1. Identify them with the standard frames
of the positive twist O(1); these local identifications glue and provide TwistData.
The canonical divisor section has coordinates t and 1, so it is x1. Define the Chern
arrow by Yoneda precomposition of the fixed projective boundary by the constant unit.
The exact Ext realization gives unit_boundary. Exact coefficient forgetting and the
coefficient-unit identity identify its finite class with the Kummer class of O(D),
hence with that of O(1). For source_normalization, the constant section followed by the
closed-point unit is invertible by compact-point-source normalization: global sections
of the finite point pushforward are the point's coefficient module, and the unit sends
one to one. The two canonical constant-pullback comparisons differ by an automorphism,
which preserves invertibility. The localization unit on a single complex equals the
canonical sections augmentation. Compose this invertible section map with the inverse
of derived sections of d.counit_iso to define sourceIso. This proves exactly its stated
normalization. No generator is chosen from a mere existence theorem. -/
theorem origin_projective_normalization (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (N : ℕ) (hN : 0 < N) (hΩ : IsUnit (N : Ω))
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (d : OriginBoundaryCounitData A N hA (Spec (.of Ω))) :
    Nonempty (OriginProjectiveNormalization A N hA (Spec (.of Ω)) d) := by sorry

end AlgebraicGeometry.Etale
