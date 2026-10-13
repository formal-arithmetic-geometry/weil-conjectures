/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Normalized scalar inverse-image composition

Source: Stacks Project, Sheaves, Tags 008I and 0097.
(blueprint: lem-sc-scalar-inverse-image-composition-coherence).
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Composition of inverse images, normalized by their adjunction units.
Source: Stacks Project, Tag 008I, lemma-pullback-composition.
(blueprint: lem-sc-scalar-inverse-image-composition-coherence). -/
def scalarInverseImageCompIso (k : Type w) [Field k]
    {A B C : Scheme.{w}} (a : A ⟶ B) (b : B ⟶ C) :
    scalarInverseImage (k := k) (a ≫ b) ≅
      scalarInverseImage (k := k) b ⋙ scalarInverseImage (k := k) a :=
  ((TopologicalSpace.Opens.map (a ≫ b).base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) _ _).leftAdjointUniq
    (((TopologicalSpace.Opens.map b.base).sheafAdjunctionContinuous (ModuleCat.{w} k) _ _).comp
      ((TopologicalSpace.Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{w} k) _ _))

attribute [local instance] Sheaf.monoidalCategory

/-- The normalized inverse-image comparison respects constant units and module coefficients.
Source: Stacks Project, Tags 008I and 0097, composition of pullback adjunctions.
(blueprint: lem-sc-scalar-inverse-image-composition-coherence).

Proof: The comparison of left adjoints identifies the composite adjunction unit with the
successive units. For the first equality, use the constant-sheaf adjunction: each side
is adjoint to the map sending a constant scalar to the same scalar section. Naturality
of the constant-sheaf comparison and the unit identity therefore identify them.
For the second equality, apply the inverse-image hom equivalence and evaluate on every
open set and every section of F. The characterization of scalarPullbackCoefficient
replaces each adjoint by the tensor-pullback unit. The defining left-adjoint uniqueness
identity for scalarPullbackCompIso identifies the successive tensor units with the
composite tensor unit. The inverse-image comparison has the identical unit identity.
Thus both adjoints have equal components, and sheaf morphism extensionality and the
injectivity of the hom equivalence give the second equality. These arguments apply to
zero coefficients, empty schemes and identity arrows without cancellation of sections.
-/
theorem scalarInverseImageCompIso_coherence
    (k : Type w) [Field k] (A B C : Scheme.{w})
    (fA : A ⟶ Spec (CommRingCat.of k)) (fB : B ⟶ Spec (CommRingCat.of k))
    (fC : C ⟶ Spec (CommRingCat.of k)) (a : A ⟶ B) (b : B ⟶ C)
    (ha : a ≫ fB = fA) (hb : b ≫ fC = fB) (F : C.Modules) :
    (scalarInverseUnitIso (a ≫ b)).inv ≫
        (scalarInverseImageCompIso k a b).hom.app (𝟙_ (KSheaf C k)) =
      (scalarInverseUnitIso a).inv ≫
        (scalarInverseImage a).map (scalarInverseUnitIso b).inv ∧
    (scalarInverseImageCompIso k a b).hom.app (scalarSheaf fC F) ≫
        (scalarInverseImage a).map (scalarPullbackCoefficient fC fB b hb F) ≫
        scalarPullbackCoefficient fB fA a ha ((tensorPullback b).obj F) ≫
        scalarHom fA ((scalarPullbackCompIso a b).app F).inv =
      scalarPullbackCoefficient fC fA (a ≫ b)
        (by rw [Category.assoc, hb, ha]) F := by sorry

end
end AlgebraicGeometry.Scheme.Modules
