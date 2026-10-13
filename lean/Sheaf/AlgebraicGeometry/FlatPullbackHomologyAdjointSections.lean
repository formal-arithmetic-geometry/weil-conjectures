/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeSectionComplex

/-! # Adjunction on section homology

Source: Stacks Project, Cohomology of Sheaves, Tags 01E4 and 02N7
(blueprint: lem-weil-pbc-flat-pullback-homology-adjoint-sections).
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- Passing from an adjoint map of complexes to homology commutes with the canonical
class map on every open. This statement involves no resolution or augmentation.
Source: Stacks Project, Cohomology, Tags 02N7 and 01E4
(blueprint: lem-weil-pbc-flat-pullback-homology-adjoint-sections).

Proof: Write c for the termwise adjoint of q. The complex adjunction gives
q = eta_K followed by g_*c in every degree. A section cocycle s on V therefore
maps to c(1 tensor eta(s)) on the inverse image of V. Flatness makes tensor
pullback exact, so its homology comparison identifies the class of this
cocycle with the image of 1 tensor eta([s]) in g^*H^p(K). Apply the unit formula
of exists_tensorPullbackAdjunction to H^p(K); the adjoint of H^p(c) sends the
class of s to the class of q(s). The definition of sectionCohomologyTheta
uses the sheafification unit and the exact sheafification homology comparison.
Their naturality identifies these cocycle class maps with sectionHomologyClass.
Every section-complex homology class is represented by a cocycle, and boundaries
map to boundaries. Thus the two displayed additive-group morphisms agree, also
in degree zero (where the incoming boundary is zero) and on the empty open. -/
theorem flatPullbackHomologyAdjoint_sections {X Y : Scheme.{u}} (g : X ⟶ Y) [Flat g]
    (K : CochainComplex Y.Modules ℕ) (L : CochainComplex X.Modules ℕ)
    (q : K ⟶ ((pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
    (V : Y.Opens) (p : ℕ) :
    sectionHomologyClass K V p ≫
      Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
        (((K.sc p).mapHomologyIso (tensorPullback g)).inv ≫
          (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℕ) p).map
            (((Classical.choose (exists_tensorPullbackAdjunction g)).mapHomologicalComplex
              (ComplexShape.up ℕ)).homEquiv _ _ |>.symm q))) V =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        (pushforwardComplexSections g q V) ≫ sectionHomologyClass L (g ⁻¹ᵁ V) p := by
  sorry

end AlgebraicGeometry.Scheme.Modules
