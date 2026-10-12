/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint
import Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule

/-! # AffineDerivedHomEvaluationCounit

Source: Stacks Project, Duality for Schemes, Section 48.11.
-/

@[expose] public section

universe u wY wA

open CategoryTheory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The affine algebra-valued derived Hom adjunction, with its evaluation counit.
This lemma involves neither a quasi-coherent right adjoint of pushforward nor its
comparison with scalar restriction.

Source: Stacks Project, Tags 0BUZ, 0BV0 and 0AX3
(blueprint: lem-sc-affine-derived-hom-evaluation-counit).

Proof:
1. Take the underived sheaf-Hom adjunction and its derived adjunction from
   `exists_affine_derivedSheafHom_adjunction`. Scalar restriction is exact, so its
   derived functor L is canonically isomorphic to the chosen rightDerivedFunctor.
   Transport the adjunction across that isomorphism, obtaining H and adjH.
2. Compute on a K-injective resolution I of K. After forgetting the algebra action,
   H(K) is Hom(A,I); identify A with the module f_* O_X by the identity on sections.
   The localization comparison for derivedInternalHom gives the displayed d.
3. Hom(O_Y,I) is canonically I, by evaluation at one in every degree. Descend this
   natural chain isomorphism and the resolution quasi-isomorphism to obtain iota.
4. Precomposition by O_Y -> A followed by that evaluation sends a local map to its
   value at one. The derived counit formula of the affine adjunction is the same
   chain map. Localization and its natural comparison therefore give the equality.
The argument works for all derived objects, including zero and arbitrary shifts. -/
theorem exists_affine_derivedHom_evaluation_counit {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :
    ∃ (H : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
      (adjH : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H),
    ∃ ι : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
    ∀ K : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
    ∃ d : (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor.obj
          (H.obj K) ≅
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))),
            K),
    d.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op, 𝟙 K) ≫
        ι.hom.app K = adjH.counit.app K := by
  sorry

end AlgebraicGeometry
