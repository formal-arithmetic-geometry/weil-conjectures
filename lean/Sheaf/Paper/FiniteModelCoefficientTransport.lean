/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData

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

The restriction functor along the inverse of the ring equivalence is an exact
 equivalence and hence transports the chosen derived representative. Derived
 transitivity identifies the two scalar changes with the composite map. Constant
 realization preserves this transport termwise, including the universe lift.

Source: Stacks Project, sites-cohomology.tex, Tags 0D6D and 093J.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison-transport). -/
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
