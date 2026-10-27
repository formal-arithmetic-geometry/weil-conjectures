/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.UnitRealizationScalarNormalization
public import Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
import Sheaf.AlgebraicGeometry.UnitAffineComparisonTransport
import Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization

/-! # Normalization of affine realization for the structure module -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] RingedSpace.moduleCohomology tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

/-- The affine realization for the unit module, normalized on actual structural
functions and on the canonical raw classes. No properness, smoothness, curve,
Noetherian or local-freeness assumption enters this change of coefficients.

Source: Stacks Project, Etale Cohomology, Tags 03P2 and 03Q8; Sheaves, Tags 0096
and 0097.
(blueprint: new-unit-affine-cohomology-etale-realization)

Proof: Transport the ordinary affine comparison family through pullback symmetry and
structural-unit normalization. Apply the existing affine cohomology etale realization
with this transported family, retaining its coherent-class action and linearity.
Normalize that given coherent realization to actual structural functions. -/
theorem exists_unitAffineCohomologyEtaleRealization {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (E : S.Modules) [E.IsQuasicoherent]
    (e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g ≃ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E))
    (e_natural : ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
      (hT : IsAffine T) (hT' : IsAffine T')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g),
      e T' (h ≫ g) hT' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) g h x) =
      coherentEdgeRho g h E (e T g hT x)) :
    ∃ Φ : unitRealizationImage f ≅
          liftedCoherentEtaleSheaf E,
      UnitRealizationScalar f E Φ := by
  classical
  obtain ⟨c, hc, hn⟩ := exists_unitAffineComparisonTransport f E e e_natural
  obtain ⟨action, Φ, _, ha, hl, _, _⟩ :=
    exists_affineCohomologyEtaleModuleRealization f (SheafOfModules.unit X.ringCatSheaf)
      E 1 c hc hn
  exact exists_unitRealizationScalar_of_coherentAction f E action Φ ha hl

end
end AlgebraicGeometry.Scheme.Modules
