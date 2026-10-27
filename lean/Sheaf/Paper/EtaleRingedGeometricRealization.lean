/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.EtaleRingedDerivedIdentificationData

/-! # The ordinary geometric realization on lifted étale sites -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction CategoryTheory.ConstantModuleDerivedProjection
namespace AlgebraicGeometry.Etale.RingedProjectionIdentification

/-- Realize the transported étale geometric and fixed-scalar adjunctions by actual
constant-ring scalar extension, including its normalized ordinary comparison.
Source: Stacks Project, sites-modules.tex, Tags 03CY, 03EL and 04JC, and
sites-cohomology.tex, Tag 07A4
(blueprint: lem-pur-etale-ringed-geometric-realization).
Proof: transport the native set, ring and module inverse images through the displayed
site equivalences. The inverse image of the constant ring is identified with the
constant ring by the map preserving every constant section. Construct its module
inverse image by scalar extension, with insertion m ↦ 1 tensor m. The ring isomorphism
contracts this extension; it identifies its underlying abelian sheaf with ordinary
inverse image and makes that inverse image exact. Construct direct image by the
underlying geometric direct image and its induced scalar action. The scalar-extension
Hom adjunction forgets to the set Hom adjunction. Restricting the action to constant
sections gives the transported fixed-scalar direct image; its left adjoint is the
transported fixed-scalar inverse image with the displayed adjunction. The normalized
ordinary comparisons follow from constant-scalar geometric adjunction comparison.
Exactness follows from finite-limit preservation of geometric inverse image and
colimit preservation of a left adjoint. This works also for the zero ring and the
identity scheme morphism; it uses no finiteness hypothesis on the coefficients. -/
theorem etale_ringed_geometric_realization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ d : GeometricData (topology Y) (topology X) Λ,
      d.inverse = (presentationEquivalence Y (Type (u + 1))).inverse ⋙
        Scheme.etaleSetPullback f ⋙ (presentationEquivalence X (Type (u + 1))).functor ∧
      d.direct = transportedDirect f (Type (u + 1)) ∧
      HEq d.geometric
        ((presentationEquivalence Y (Type (u + 1))).symm.toAdjunction.comp
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (X.smallGrothendieckTopology @Etale)).comp
              (presentationEquivalence X (Type (u + 1))).toAdjunction)) ∧
      ∃ (hL : d.pullA = transportedInverse f (ModuleCat.{u + 1} Λ))
        (hR : d.pushA = transportedDirect f (ModuleCat.{u + 1} Λ)),
        HEq d.fixedAdj
          ((nativeEquivalence Y Λ).symm.toAdjunction.comp
            ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).comp
              (nativeEquivalence X Λ).toAdjunction)) ∧
        ∃ _x : ExactData d, Nonempty (OrdinaryIdentification d) := by
  sorry

end AlgebraicGeometry.Etale.RingedProjectionIdentification
