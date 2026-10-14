/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition
import Sheaf.AlgebraicGeometry.TensorPullbackCompositionAssociativity

/-! # Single-module coefficients in an open square

Source: Stacks Project, Tags 06YJ, 0D5S and 01JR.
(blueprint: lem-pc-single-open-tensor-coefficient-coherence).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Normalized single-module coefficient comparisons commute with an open square.
This is an equality of coefficient maps, before any direct image or base-change mate.
Source: Stacks Project, Tags 06YJ and 0D5S; coefficient calculation in
lem-pc-standard-single-open-relative-arrow.
(blueprint: lem-pc-single-open-tensor-coefficient-coherence).

Proof: Postcompose the desired equality with the invertible single comparison
for r. Substitute the normalization equation for beta on the right. Naturality
moves its tensor-composition factors through the comparison for e'. Apply the
single-map composition identity to (k,i) and (r,q) on the left and to (k,e)
and (e',t) on the right. Substitute the normalization equation for alpha.
The tensor-composition associativity identity for (k,e,z), together with
hi and ht, identifies the coefficient factors on the two sides; the path
(e',t,z) is the same triple composite by ht, and hsq identifies it with (r,q).
Equality induction on hi, ht and hsq identifies the transports. Reassociate,
cancel the derived composition isomorphisms, and cancel the final comparison
for r. No single comparison for q or t is inverted. This is valid for zero
modules, empty schemes, and identity morphisms. The statement does not require
open immersions: the invertibility needed for cancellation is explicit. -/
theorem single_open_tensor_coefficient_coherence
    {W Z X' P J J' : Scheme.{u}}
    (z : Z ⟶ W) (q : X' ⟶ W) (t : P ⟶ Z)
    (i : J ⟶ W) (r : J' ⟶ X') (k : J' ⟶ J)
    (e : J ≅ Z) (e' : J' ≅ P)
    (hi : e.hom ≫ z = i) (ht : k ≫ e.hom = e'.hom ≫ t)
    (hsq : k ≫ i = r ≫ q) (N : W.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings W.toRingedSpace)) 0).obj N
    let M := Scheme.Modules.tensorPullbackObj z N
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M
    let E' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj t M)
    let K' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj q N)
    let phi0 := (relativeMVComp k i).hom.app K ≫
      eqToHom (congrArg (fun a ↦ (derivedPullback a).obj K) hsq) ≫
      (relativeMVComp r q).inv.app K ≫
      (derivedPullback r).map (Scheme.picardTermwiseSingleMap q N)
    let aN := (Scheme.Modules.tensorPullbackCompositionIso e.hom z i hi).symm.app N
    let heq : (e'.hom ≫ t) ≫ z = r ≫ q := by
      rw [← ht, Category.assoc, hi, hsq]
    let bN := (Scheme.Modules.tensorPullbackCompositionIso
        e'.hom t (e'.hom ≫ t) rfl).symm.app M ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso
        (e'.hom ≫ t) z (r ≫ q) heq).symm.app N ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso r q (r ≫ q) rfl).app N
    IsIso (Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N)) →
    ∀ (alpha : (derivedPullback e.hom).obj E ⟶ (derivedPullback i).obj K)
      (beta : (derivedPullback e'.hom).obj E' ⟶ (derivedPullback r).obj K'),
      alpha ≫ Scheme.picardTermwiseSingleMap i N =
        Scheme.picardTermwiseSingleMap e.hom M ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings J.toRingedSpace)) 0).map aN.hom →
      beta ≫ Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N) =
        Scheme.picardTermwiseSingleMap e'.hom (Scheme.Modules.tensorPullbackObj t M) ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings J'.toRingedSpace)) 0).map bN.hom →
      (derivedPullback k).map alpha ≫ phi0 =
        (relativeMVComp k e.hom).hom.app E ≫
        eqToHom (congrArg (fun a ↦ (derivedPullback a).obj E) ht) ≫
        (relativeMVComp e'.hom t).inv.app E ≫
        (derivedPullback e'.hom).map (Scheme.picardTermwiseSingleMap t M) ≫
        beta := by sorry

end AlgebraicGeometry
