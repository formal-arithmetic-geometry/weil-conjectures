/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

import WeilConjectures.AlgebraicGeometry.QlbarDirectImageComparison

/-! # Derived image comparison for finite-field extension to the algebraic closure -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual scalar inclusion from E into the finite-subextension-valued algebraic
closure commutes with compact and ordinary native derived images of a sheaf.
No dimension or cohomological bound is assumed or concluded.

Source: current blueprint, sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
Qbar paragraph of the Complement; sk-thm-sfb-qlbar-two-colimit and sk-prop-scalar-six.
(blueprint: lem-sf-finite-point-qbar-scalar-images).

Proof in words. The algebraic-closure coefficient sheaf is the filtered colimit of the
finite coefficient extensions containing E. Finite composita make this subsystem cofinal.
Each finite extension is a finite free E module; choosing a basis identifies its scalar
functor with a finite direct sum. Thus scalar extension to the algebraic closure is exact,
and finite scalar extension commutes with ordinary derived image. For the filtered colimit,
use qcqs bounded-below direct-image continuity: N[0] has lower bound zero, shared by every
finite scalar extension, so the natural mate is invertible. This is the canonical
isIso_derivedPushHom_padicAlgCl_of_boundedBelow comparison. For compact support use the
fixed factorization Rg_* j_!. Exact extension by zero commutes with scalar extension by
the unit-normalized open-immersion mate, and j_!N[0] still has lower bound zero. Apply the
same bounded-below comparison to the proper map g and compose the two comparisons.
Finally apply both image functors to the single-complex map induced by the
given isomorphism m. This proves both displayed isomorphisms in the derived category.
The empty scheme and zero module use the same constructions, with no rank assumption. -/
theorem finite_point_qbar_scalar_images
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (N : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X.left))
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X.left))
    (m : (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X.left ℓ E)).obj N ≅ M) :
    let T := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl (Spec (.of D.k)) ℓ E)
    Nonempty (T.leftDerivedFunctor.obj
      ((rightDerivedLowerShriekOfCompactification
        (Profinite.continuousMapRingObj.{u} E) c).obj
        ((DerivedCategory.singleFunctor _ 0).obj N)) ≅
      (rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj.{u} ℓ) c).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
    Nonempty (T.leftDerivedFunctor.obj
      ((lowerStar (Profinite.continuousMapRingObj.{u} E) X.hom).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N)) ≅
      (lowerStar (Profinite.padicAlgClRingObj.{u} ℓ) X.hom).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  let K := (DerivedCategory.singleFunctor _ 0).obj N
  let J := openImmersionLowerShriek (Profinite.continuousMapRingObj.{u} E) c.i
  let KJ := J.mapDerivedCategory.obj K
  let C : DerivedCategory.Plus _ := ⟨K, ⟨0, inferInstance⟩⟩
  let CJ : DerivedCategory.Plus _ :=
    ⟨KJ, ⟨0, J.isGE_mapDerivedCategory_obj K 0⟩⟩
  let a := Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E
  let TX := Mod.extendScalars (coefficientMap a X.left)
  have : IsIso ((derivedPushHom a X.hom).app K) :=
    isIso_derivedPushHom_padicAlgCl_of_boundedBelow ℓ E X.hom C
  have : IsIso ((derivedPushHom a c.g).app KJ) :=
    isIso_derivedPushHom_padicAlgCl_of_boundedBelow ℓ E c.g CJ
  let eK : TX.leftDerivedFunctor.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj M :=
    (TX.singleFunctorCompLeftDerivedFunctorIso.app N) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso m
  let ec := asIso ((derivedPushHom a c.g).app KJ) ≪≫
    (lowerStar (Profinite.padicAlgClRingObj ℓ) c.g).rightDerivedFunctor.mapIso
      ((derivedOpenImmersionShriekIso a c.i).app K) ≪≫
    (rightDerivedLowerShriekOfCompactification
      (Profinite.padicAlgClRingObj ℓ) c).mapIso eK
  let eo := asIso ((derivedPushHom a X.hom).app K) ≪≫
    (lowerStar (Profinite.padicAlgClRingObj ℓ) X.hom).rightDerivedFunctor.mapIso eK
  exact ⟨⟨ec⟩, ⟨eo⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
