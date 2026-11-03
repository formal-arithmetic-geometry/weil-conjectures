/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerLocalizationSpliceDefs
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.Basic

/-! # Root-normalized finite Kummer classes

Source: the finite étale-origin transport in step 4 of
`literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
cor-pur-affine-space-zero-section-purity.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The ordinary finite Kummer extension and the characteristic-exponent derived
Kummer class agree under any scalar comparison normalized on the roots.

Source: step 4 of cor-pur-affine-space-zero-section-purity, finite étale-origin
transport, and the prescribed root power comparison in def-pur-frame-class.
(blueprint: lem-pur-finite-kummer-unit-normalization).

Proof: apply the scalar-unit cohomology bijection to the two degree-one arrows.
The scalar-unit comparison sends the coefficient generator to 1. Naturality of
scalar extension sends the ordinary root map followed by e to its adjunction
unit, by he. Write N = char(A) d. The morphism of Kummer sequences with root map
zeta -> zeta^d, middle map multiplication by d and right map identity identifies
the two connecting classes. The canonical Tate comparison is defined using
exactly this power map, so the normalized cohomology classes agree. The
module/abelian cohomology bijection gives equality of the derived arrows.
This includes N = char(A), the empty scheme and the trivial unit. -/
theorem finiteKummerUnit_normalization
    (A : Type (u + 1)) [CommRing A] [NeZero (ringChar A)]
    (X : Scheme.{u}) [HasInvertibleExponent A X]
    (N : ℕ) (hA : (N : A) = 0) (hX : IsUnit (N : Γ(X, ⊤)))
    (e : Scheme.finiteEtaleTateLine X N A hA ≅
      (extendScalars A X).obj (X.rootsOfUnitySheaf N))
    (he : ordinaryFiniteRootMap A N hA X ≫
      (moduleAbelianForget A X).map e.hom =
        (extendScalarsAdjunction A X).unit.app (X.rootsOfUnitySheaf N))
    (s : Γ(X, ⊤)ˣ) :
    let v := tateTwistObjectIsoSingleFunctor A X 1 ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (e ≪≫ extendScalarsRootsOfUnityIsoTateTwistSheaf A N hA hX).symm
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom ≫
      kummerClassOf X A s ≫ v.hom⟦(1 : ℤ)⟧' =
        (finiteKummerUnitClass A N hA X hX s).hom := by sorry

end AlgebraicGeometry.Etale
