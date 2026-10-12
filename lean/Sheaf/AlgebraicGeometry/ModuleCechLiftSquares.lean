/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCechComparison

/-! # Commuting squares for a lift between module injective resolutions

Source: Stacks Project, Cohomology of Sheaves, Tag 01EQ, functoriality of alpha and beta.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Applying the Cech functor and totalization to a lift of a module morphism gives
commuting squares with both comparison augmentations.
Source: Stacks Project, Cohomology of Sheaves, Tag 01EQ, proof and final functoriality
assertion (blueprint: lem-sc-module-cech-lift-squares).

Proof: In total degree n, alpha lands in the (n,0) summand. The total map on this
summand is the Cech map of the nth component of the lift. Restriction of a global
section commutes with that component by naturality of a presheaf module morphism.
The scalar restriction at the whole space is the identity, and its identification
commutes with module maps. This proves the alpha square componentwise. Beta lands
in the (0,n) summand. The total map on this summand is the degree-n Cech map of the
zeroth component of the lift. Functoriality of the Cech functor and the equation
relating that component to the two augmentations prove the beta square. Neither
argument needs a covering hypothesis, including for the empty indexing family.
-/
theorem moduleCechLiftSquares {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (φ : F ⟶ G) (I : InjectiveResolution F)
    (J : InjectiveResolution G) (ψ : I.cocomplex ⟶ J.cocomplex)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = φ ≫ J.ι.f 0) :
    let T := HomologicalComplex₂.total.map
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
          CategoryTheory.cechComplexFunctor U).mapHomologicalComplex
            (ComplexShape.up ℕ) |>.map ψ) (ComplexShape.up ℕ)
    moduleCechAlpha U I ≫ T =
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map ψ ≫ moduleCechAlpha U J ∧
    moduleCechBeta U I ≫ T =
      (CategoryTheory.cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          φ.val) ≫ moduleCechBeta U J := by
  sorry

end AlgebraicGeometry.Scheme.Modules
