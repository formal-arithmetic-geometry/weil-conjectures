/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor

/-! Transport of the algebraic representative through a coefficient equivalence.

Source: Stacks Project, sites-cohomology.tex, Tags 0D6D and 093J.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Coefficient equivalence transport identifies the algebraic scalar-extension model.

STATEMENT-DISPUTED: the statement has no K-flat (or equivalent) hypothesis on P.
For a non-flat ring map q and a non-K-flat complex P, ordinary scalar extension
of P need not represent the derived scalar extension represented by L(Q(P));
for example q : ℤ →+* ℤ/2 and P := (ℤ/2)[0] produce a nonzero Tor term in the
left-derived extension that is absent from the ordinary tensor complex.

The restriction functor along the inverse of the ring equivalence is an exact
 equivalence and hence transports the chosen derived representative. Derived
 transitivity identifies the two scalar changes with the composite map. Constant
 realization preserves this transport termwise, including the universe lift.

Source: Stacks Project, sites-cohomology.tex, Tags 0D6D and 093J.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison-transport). -/
private theorem finiteModel_constantComplex_mapIso
    (X : Scheme.{t}) {D : Type t} [CommRing D]
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    {A B : CochainComplex (ModuleCat.{t} D) ℤ}
    (e : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj B) :
    Nonempty
      ((@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D A) ≅
        (@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D B)) := by
  have hconstant : (koszulConstantFunctor X D).Additive ∧
      PreservesFiniteLimits (koszulConstantFunctor X D) ∧
      PreservesFiniteColimits (koszulConstantFunctor X D) := by
    dsimp [koszulConstantFunctor]
    exact commutativeSiteConstantModuleFunctor_exact (ProEt.topology X) (ULift.{t + 1} D)
  have := hconstant.1
  have := hconstant.2.1
  have := hconstant.2.2
  have : (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D)).isEquivalence_functor
  have : PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom) :=
    Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  let F := ModuleCat.uliftFunctor.{t + 1, t} D ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom ⋙
    koszulConstantFunctor X D
  exact ⟨(F.mapDerivedCategoryFactors.app A).symm ≪≫
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app B⟩

theorem finiteModel_derivedRepresentative_transport
    (X : Scheme.{t}) {B C D : Type t} [CommRing B] [CommRing C] [CommRing D]
    (q : B →+* C) (ρ : C ≃+* D)
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (L : DerivedCategory (ModuleCat.{t} B) ⥤ DerivedCategory (ModuleCat.{t} C))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars q)
        (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    let K := ((ModuleCat.restrictScalars.{t} ρ.symm.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj (DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P)))
    Nonempty
      ((@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D
            (((ModuleCat.extendScalars (ρ.toRingHom.comp q)).mapHomologicalComplex
              (.up ℤ)).obj P)) ≅
        (@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D K)) := by
  sorry

end AlgebraicGeometry.Scheme
