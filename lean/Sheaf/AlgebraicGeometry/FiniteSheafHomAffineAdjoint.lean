/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # The affine derived sheaf-Hom adjunction

Source: Stacks Project, Duality for Schemes, Tags 0BV0, 0BUZ and 0AX3
(blueprint: lem-sc-finite-sheafhom-affine-adjoint).
-/

@[expose] public section

universe u w wA

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Restriction along `O_X → A = f_* O_Y` (the ring sheaf of the landed
`directImageAlgebraSpace f`) has right adjoint the derived sheaf-Hom out of `A`:
there are an underived right adjoint `H` of restriction, valued in `A`-modules, whose
underlying `O_X`-module functor is `homObj A (-)` and whose counit is evaluation at
`1 ∈ A`; a right derived functor `R : D(O_X) ⥤ D(A)` of `H` (with its comparison `β`);
the derived restriction `L` (with its comparison `t`); and an adjunction `L ⊣ R` whose
`O_X`-module right adjoint `R ⋙ L` is `RHom_{O_X}(A, -)` and whose counit is the
morphism induced by the underived evaluation counit (`Adjunction.derivedε_fac_app`).

Source: Stacks Project, Duality for Schemes, Tags 0BV0, 0BUZ and 0AX3
(blueprint: lem-sc-finite-sheafhom-affine-adjoint).

Proof:
1. Use the underived affine sheaf-Hom adjunction of lem-sc-finite-sheafhom-affine.
   Its underlying O_X-module is homObj(A,F), with A acting by precomposition with
   multiplication. The underived counit evaluates a local homomorphism at one.
2. Restriction of scalars is exact, hence its termwise functor descends through Q to an
   absolute left derived functor `L`. The right derived functor `R` of `H` is computed on
   K-injective resolutions; it is absolute, and `R ⋙ L` computes `RHom_{O_X}(A, -)`
   (def-pur-derived-internal-hom). Apply lem-sc-derived-adjunction-from-underived.
3. The counit clause of lem-sc-derived-adjunction-from-underived (Mathlib
   `Adjunction.derivedε_fac_app`) identifies the derived counit with the morphism induced
   by the underived counit, i.e. by evaluation at one. -/
theorem exists_affine_derivedSheafHom_adjunction
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :
    ∃ (H : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
      (_ : H.Additive)
      (iH : H ⋙ SheafOfModules.restrictScalars
          (R := moduleRings X.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor X.sheaf).obj
          (op ((SheafOfModules.restrictScalars
            (R := moduleRings X.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
              (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))
      (adj₀ : SheafOfModules.restrictScalars
          (R := moduleRings X.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ⊣ H),
      (∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (U : X.Opens)
          (φ : (H.obj F).val.obj (op U)),
        ((adj₀.counit.app F).val.app (op U)).hom φ =
          ((((iH.hom.app F).val.app (op U)).hom φ).app (op (Over.mk (𝟙 U)))).hom
            (1 : (moduleRings (directImageAlgebraSpace f)).obj.obj (op U))) ∧
      ∃ (R : schemeDerivedCategory X ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
        (β : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (L : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))) ⥤
          schemeDerivedCategory X)
        (t : DerivedCategory.Q ⋙ L ≅
          (SheafOfModules.restrictScalars
            (R := moduleRings X.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
              (.up ℤ) ⋙ DerivedCategory.Q)
        (adj : L ⊣ R),
        R.IsRightDerivedFunctor β (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
        (R ⋙ L).IsRightDerivedFunctor (Functor.whiskerRight β L ≫ (Functor.associator _ _ _).hom)
          (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
        Nonempty (R ⋙ L ≅ (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)).obj
            (op ((DerivedCategory.singleFunctor _ 0).obj
              ((SheafOfModules.restrictScalars
                (R := moduleRings X.toRingedSpace)
                (R' := moduleRings (directImageAlgebraSpace f))
                ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
                  (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))) ∧
        ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
          L.map (β.app K) ≫ adj.counit.app (DerivedCategory.Q.obj K) =
            t.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app K) := by
  sorry

end AlgebraicGeometry
