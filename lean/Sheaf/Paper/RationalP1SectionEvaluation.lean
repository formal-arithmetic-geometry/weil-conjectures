/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module

public import Sheaf.Paper.RationalP1AmbientComposites
public import Sheaf.Paper.RationalTatePullback

/-! # Evaluating an arbitrary kernel on the projective diagonal

Source: the first identity in the rational projective-line triangle proof, the section
and projection calculation after the trace has been transported to the first projection.
(blueprint: lem-sfb-rational-p1-section-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso

/-- Change the second direct-image path to the first by conjugating the canonical
pullback comparison. Source: blueprint First identity, `Rq_*Rp₂* = Rq_*Rp₁*`
(blueprint: lem-sfb-rational-p1-section-evaluation). -/
@[irreducible]
def firstPathComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    moduleObjectDerivedPushforward Λ (secondProjection Y) ⋙
        moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y) ≅
      moduleObjectDerivedPushforward Λ (firstProjection Y) ⋙
        moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y) := by
  unfold moduleObjectDerivedPushforward
  exact (conjugateIsoEquiv
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y)))
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (secondProjection Y)))
    (condensedAmbientPullbackComparison Λ (square Y))).symm

/-- Express a diagram functional in the fixed native first direct image.
Source: the full-unit-normalized derived model in the First identity
(blueprint: lem-sfb-rational-p1-section-evaluation). -/
@[irreducible]
def firstNativeFunctional
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (t : d.R₁.R.obj N ⟶ unit Λ (ProjectiveLine Y)) :
    (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N ⟶
      unit Λ (ProjectiveLine Y) := by
  unfold moduleObjectDerivedPushforward firstProjection
  exact (eqToIso d.p₁_canonical).inv.app N ≫ t

set_option maxHeartbeats 800000 in
-- Keep the native functor sources fixed while constructing the prefix.
/-- The supported-kernel insertion, with its source and target fixed before direct image.
Source: blueprint First identity, the section followed by the diagonal tensor comparison
(blueprint: lem-sfb-rational-p1-section-evaluation). This is the literal section paste,
followed by the second direct image of the tensor comparison and the supported kernel arrow. -/
@[irreducible]
def firstKernelInsertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N) :
    M ⟶ (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N) :=
  (pushSectionIso Λ Y).hom.app M ≫
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
      ((diagonalTensorIso Λ Y M).hom ≫
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
          ((supportedUnitIso Λ Y).hom ≫ α)))

set_option maxHeartbeats 800000 in
-- The terminal functional has the native path objects as its declared endpoints.
/-- Change direct-image paths and evaluate a first-projection functional.
Source: blueprint First identity, the functional after trace base change
(blueprint: lem-sfb-rational-p1-section-evaluation). The arrows are the conjugate path
comparison, the inverse projection, identity tensor the given native functional,
identity tensor singleUnitIso, and the right unitor, in that order. -/
@[irreducible]
def firstTerminalFunctional
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (t : d.R₁.R.obj N ⟶ unit Λ (ProjectiveLine Y))
    (hp : IsIso (projectionMap Λ (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N)) ⟶
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M :=
  (firstPathComparison Λ Y).hom.app
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N) ≫
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      (@inv _ _ _ _ (projectionMap Λ (firstProjection Y) M N) hp ≫
        (M ◁ firstNativeFunctional Λ Y L d N t) ≫
        (M ◁ (singleUnitIso Λ (ProjectiveLine Y)).hom) ≫ (ρ_ M).hom)

attribute [local irreducible] coefficient line diagram secondLineComparison

set_option maxHeartbeats 800000 in
-- Elaborate the native projection and the two canonical direct-image paths.
/-- The section calculation with an arbitrary kernel arrow and an arbitrary functional.
It uses neither a Tate pullback comparison nor a trace base-change equation. In particular,
no integration equation for `d` is used.

Source: current blueprint, sec-six-functors-basics/sk-prop-p1-adjunction-rational/
sk-prop-p1-adjunction-rational-triangle.proof.md, First identity, final three sentences
(blueprint: lem-sfb-rational-p1-section-evaluation).

Proof: Naturality of the conjugate path comparison moves the kernel arrow across it.
Naturality of the first projection map moves that arrow outside the first direct image;
cancel the projection with its specified inverse. Apply the section projection identity
for the diagonal and first projection to the inverse diagonal tensor comparison. The
canonical pullback section comparisons and their conjugates identify the two paths from
M to the first direct image of its supported tensor. This gives the right unitor inverse
tensored with the canonical supported-unit section. The full universal-unit normalization
of d.R₁ and the ordinary composition normalization of d.support₁ identify that section
with singleUnitIso.inv followed by d.support₁.hom. Move the arbitrary functional outside
by projection naturality. Functoriality and tensor functoriality combine the remaining
three coefficient arrows. The two unitors give exactly the displayed right-hand side.
This works for a zero kernel, a zero functional, and the coefficient-unit kernel, and
uses invertibility only of the projection at N. -/
theorem first_section_tensor_evaluation
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules (coefficient l c).X X) (d : Diagram (coefficient l c).X Y L)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (N : DerivedCategory (Modules (coefficient l c).X (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
      (source (coefficient l c).X Y) ⟶ N)
    (t : d.R₁.R.obj N ⟶ unit (coefficient l c).X (ProjectiveLine Y))
    (hp : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (firstKernelInsertion (coefficient l c).X Y M N α) ≫
      firstTerminalFunctional (coefficient l c).X Y L d M N t hp =
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      ((ρ_ M).inv ≫ (M ◁
        ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫ d.support₁.hom ≫
          d.R₁.R.map α ≫ t ≫ (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom)) ≫
        (ρ_ M).hom) := by sorry

end AlgebraicGeometry.ProEtale.RationalP1
