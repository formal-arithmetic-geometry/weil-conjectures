/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
public import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData
import Sheaf.AlgebraicGeometry.UnitAffineComparisonTransportCore
import Sheaf.AlgebraicGeometry.UnitAffineComparisonTransportNaturality

/-! # Transport of a natural affine structural cohomology comparison -/

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

attribute [-instance] unitAffineSectionsModule unitAffineCohomModule
  unitAffineForgetCohomModule unitAffineHModule unitAffineForgetModule

private theorem unitAffineComparisonFamily_scalar {X S : Scheme.{u}} (f : X ⟶ S)
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
      (∀ (V : S.Etale) [IsAffine V.left] (a : Γ(V.left, ⊤))
        (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
          (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)),
        unitAffineComparisonFamily f E e e_natural V ((pullback.fst V.hom f).appTop a • x) =
        a • unitAffineComparisonFamily f E e e_natural V x) := by
  intro V hV a x
  unfold unitAffineComparisonFamily
  exact unitAffineComparison_smul f V E (e V.left V.hom hV) a x

/-- Change the factor order and unit coefficient in a natural affine comparison family.
This result concerns ordinary coherent cohomology only; it asserts no etale higher-image
realization or scalar action on such an image.

Source: Stacks Project, Cohomology, Tag 0ATM; Sheaves, Tags 0096 and 0097.
(blueprint: new-unit-affine-comparison-transport).

Proof: For T over S let sigma identify T times_S X with X times_S T. Normalize both
pulled-back unit coefficients with the actual adjoint maps to the structural unit,
transport structural-unit cohomology by sigma inverse, and undo the normalization on
X times_S T. Compose this additive equivalence with the given linear comparison.
The two projection identities for sigma and semilinearity of structural cohomology
pullback imply linearity over the functions on T. For a morphism T' to T, the canonical
base-change maps commute with sigma by the two pullback projection identities.
Functoriality of module cohomology and naturality of the structural-unit normalization
therefore identify the two restriction composites. The normalized tensor adjunction is
the adjunction selected by its uniquely specified section unit, so its composition
isomorphism is tensorSectionsComp. Thus the given section restriction equation is
exactly the etale tensor restriction equation after transport. No affine cover is
chosen, and identity, empty and zero cases are included. -/
theorem exists_unitAffineComparisonTransport {X S : Scheme.{u}} (f : X ⟶ S)
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
    ∃ c : ∀ (V : S.Etale) [IsAffine V.left],
      (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
        (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V) ≃+
          Γ((tensorPullback V.hom).obj E, ⊤),
      (∀ (V : S.Etale) [IsAffine V.left] (a : Γ(V.left, ⊤))
        (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
          (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)),
        c V ((pullback.fst V.hom f).appTop a • x) = a • c V x) ∧
      (∀ (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left] (h : V' ⟶ V)
        (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
          (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)),
        c V' (affineRealizationRestriction f (SheafOfModules.unit X.ringCatSheaf) 1 h x) =
          etaleTensorSectionsRestriction E h (c V x)) := by
  exact ⟨unitAffineComparisonFamily f E e e_natural,
    ⟨unitAffineComparisonFamily_scalar f E e e_natural,
      unitAffineComparison_canonical_naturality f E e e_natural⟩⟩

end
end AlgebraicGeometry.Scheme.Modules
