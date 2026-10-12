/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Sheaf.RingTheory.KoszulRegularSequenceDualComplex
import Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit
import Sheaf.AlgebraicGeometry.AffineModuleCorrespondence
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.Paper.DerivedInternalHomRestrictOpen

/-! # Cohomology of the algebra-valued Koszul dual

Source: Stacks Project, Tags 0BQZ, 0AX3 and 0AVW.
-/

@[expose] public section

universe u wY wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The intrinsic Koszul Ext identifications glue as direct-image-algebra module maps.
This computes cohomology only; it does not identify the derived objects or split
extensions between different cohomological degrees.

Source: Stacks Project, Tag 0BQZ, proof of Lemma 48.15.5; Tag 0AX3 and Tag 0AVW
(blueprint: lem-sc-koszul-regular-immersion-algebra-dual-homology).

Proof:
1. Use `exists_affine_derivedHom_evaluation_counit` for the closed immersion, which
   is affine. Uniqueness of right adjoints transports its cohomology calculation
   to H. Restriction of derived internal Hom to opens gives the local calculation.
   Its algebra action on Hom(i_* OZ,J), for a K-injective resolution J of
   OY, is precomposition by multiplication on i_* OZ.
2. Near a point of Z use a finite free Koszul resolution of the quotient A/I.
   Koszul-regularity makes its augmentation a quasi-isomorphism; bounded finite
   free Hom computes derived sheaf Hom. The dual Koszul cohomology theorem kills
   all degrees except the length n and identifies degree n with the determinant
   of the dual conormal, as an A/I-module. Its intrinsic Ext comparison identifies
   precomposition by multiplication with the ordinary A/I scalar action.
3. The conormal of this quotient is I/I², and the regular generators form a basis
   there. After passing to a stalk on Z its finrank is n. Thus hr gives r(z)=n.
   Restrict to the clopen rank-n locus. Affine module correspondence identifies
   the determinant module with the exterior sheaf of the dual of the recorded
   tensor pullback of the ideal sheaf.
4. The intrinsic Ext comparison is independent of regular generators and commutes
   with localization, by the change-of-generators and localization statements of
   the dual-Koszul theorem. Hence the algebra-linear cohomology identifications
   agree on chart intersections and glue. On the rank-n locus only degree n
   survives, so the result in degree k is precisely the direct image of the
   locallyRankedExteriorTerm in degree k. Negative degrees are zero.
5. Off the closed image of Z the algebra sheaf is zero, and so are all its modules.
   This proves the comparison on all of Y. If Z is empty both sides are zero;
   if the length is zero the calculation is Hom(A,A)=A in degree zero.
No lifting of a cohomology map to a derived morphism is asserted here. -/
theorem koszulRegularImmersion_algebraDual_homology {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    (H : schemeDerivedCategory Y ⥤ DerivedCategory (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i))))
    (adjH : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace i))
      ⟨Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj
        (H.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅
      (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
        (Scheme.Modules.locallyRankedExteriorTerm
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r n)) := by sorry

end AlgebraicGeometry
