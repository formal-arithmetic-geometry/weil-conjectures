/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! # Localization of the affine sheaf-Hom evaluation counit

Source: Stacks Project, duality.tex, Tags 0BV0 and 0AX3.
-/

@[expose] public section

universe u wY wA

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry

/-- Evaluation compatibility on complex representatives for an already supplied derived
sheaf-Hom adjunction. This does not construct the adjunction or the unit-Hom isomorphism.

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0 and 0AX3.
(blueprint: lem-sc-affine-derived-hom-localized-evaluation).

Proof:
1. Replace the complex K by a K-injective resolution I. The right-derived universal
   property identifies R(Q K) with Q_A(H(I)); exact scalar restriction identifies its
   image under L with Q(H(I) restricted to O_Y).
2. Apply iH termwise. The underlying module of the algebra unit is f_* O_X, with the
   identification equal to the identity on sections. The derivedInternalHom localization
   comparison now identifies the resulting object with RHom(f_* O_X, Q K).
3. The equality h_eval says on every open that the underived counit evaluates at one.
   Under iH it is precomposition by O_Y -> f_* O_X followed by evaluation at one.
   This equality holds degreewise and therefore as a chain map. The equality h_counit
   identifies its image under Q with the derived counit; evaluate on I and cancel the
   invertible resolution comparisons.
4. With the canonical unit-Hom identification this gives the asserted equality.
   For the given iota, compose the comparison in step 2 with RHom(f_* O_X, alpha),
   where alpha is iota.inv followed by canonical_iota.hom. Naturality gives
   RHom(O_Y, alpha) followed by iota = iota followed by alpha, so the extra
   factor canonical_iota.inv followed by iota followed by alpha cancels to the
   identity. Thus the result is independent of the chosen unit-Hom isomorphism. -/
theorem affine_derivedHom_localized_evaluation
    {Y X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
      [H.Additive]
      (iH : H ⋙ SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor Y.sheaf).obj
          (op ((SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
              (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))
      (adj₀ : SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ⊣ H)
    (h_eval : ∀ (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (U : Y.Opens)
          (φ : (H.obj F).val.obj (op U)),
        ((adj₀.counit.app F).val.app (op U)).hom φ =
          ((((iH.hom.app F).val.app (op U)).hom φ).app (op (Over.mk (𝟙 U)))).hom
            (1 : (moduleRings (directImageAlgebraSpace f)).obj.obj (op U)))
    (R : schemeDerivedCategory Y ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
        (β : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (L : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))) ⥤
          schemeDerivedCategory Y)
        (t : DerivedCategory.Q ⋙ L ≅
          (SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
              (.up ℤ) ⋙ DerivedCategory.Q)
        (adj : L ⊣ R)
    (hR : R.IsRightDerivedFunctor β (HomologicalComplex.quasiIso _ (.up ℤ)))
    (h_counit : ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
          L.map (β.app K) ≫ adj.counit.app (DerivedCategory.Q.obj K) =
            t.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app K))
    (ι : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    ∃ d : L.obj (R.obj (DerivedCategory.Q.obj K)) ≅
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))),
            DerivedCategory.Q.obj K),
    d.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op,
          𝟙 (DerivedCategory.Q.obj K)) ≫
        ι.hom.app (DerivedCategory.Q.obj K) = adj.counit.app (DerivedCategory.Q.obj K) := by
  sorry

end AlgebraicGeometry
