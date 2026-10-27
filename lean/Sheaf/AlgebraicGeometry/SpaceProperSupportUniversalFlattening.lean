/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable

/-! # Universal flattening of a module with proper support

Source: Stacks Project, spaces-flat.tex, Tags 0CVI, 0CX1, 0CX2(1), 0CWX and the
schemehood paragraph of 0CXB; spaces-morphisms.tex, Tag 03XX
(blueprint: lem-sfb-space-proper-support-universal-flattening).

The ambient base is the universe-polymorphic spectrum of the integers. Test objects
retain their actual scheme maps to Spec R. The pulled module and its structural map
use the existing sheaf fibre product and tensor pullback of the proper Quot interface.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finitely presented quasi-coherent module with proper support has a universal
flattening represented by a scheme monomorphism of finite presentation. The final
biconditional includes uniqueness of each factorization. No Noetherian condition on
R and no flatness of X over R is assumed.
Source: Stacks Project, Tags 0CVI, 0CX1, 0CX2(1), 0CWX, 0CXB and 03XX
(blueprint: lem-sfb-space-proper-support-universal-flattening).

Proof:
1. Finite presentation of f implies finite type and quasi-separatedness, and finite
   presentation of F implies finite type. Apply
   lem-sfb-space-proper-support-universal-purity to the closed proper carrier in hsupp.
   This proves universal relative purity, with no flatness or Noetherian assumption.
2. Apply lem-sfb-space-pure-dimension-flatness-representability with n = 0. It gives
   an algebraic space E and a finite-presentation monomorphism E to Spec R, whose
   scheme-test image is the dimension-filtered flatness condition P_0.
3. Transcendence degree is nonnegative: its defining supremum includes the empty
   independent set. Thus P_0 asks for flatness at every point of every etale chart,
   exactly the displayed chartwise IsFlatOver condition for the same tensor pullback.
4. The morphism E to Spec R is locally of finite type. Apply
   lem-sfb-space-lft-monomorphism-separated-lqf to obtain local quasi-finiteness and
   the closed-immersion diagonal. Then
   lem-a1-separated-locally-qf-space-representable supplies a representing scheme T
   over Spec R and a compatible Yoneda isomorphism.
5. Transport finite presentation and the scheme-test representing bijection through
   this isomorphism. Charts and their maps to Spec R are identical under transport,
   so quasi-compactness, quasi-separatedness and local finite presentation persist.
   Yoneda identifies the representing map with h. Its injectivity gives the stated
   monomorphism and uniqueness; its image gives the flatness biconditional. -/
theorem exists_universalFlattening_of_properSupport
    (R : CommRingCat.{u})
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec R))))
    (hsep : MapIsSeparated f) (hfp : ProperQuotFinitePresentation f)
    (F : X.QCoh) (hF : F.obj.IsFinitePresentation)
    (hsupp : ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      MapIsProper (i ≫ f) ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ F.obj)) :
    ∃ (T : Scheme.{u}) (h : T ⟶ Spec R),
      LocallyOfFinitePresentation h ∧ QuasiCompact h ∧ QuasiSeparated h ∧
      (∀ B : Scheme.{u}, Function.Injective (fun g : B ⟶ T ↦ g ≫ h)) ∧
      ∀ B : ProperQuotTest (schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec R)))),
        (∃! g : B.left.left ⟶ T, g ≫ h = (yoneda.preimage B.hom).left) ↔
          ∀ U : (properQuotFibre f B).EtaleSite,
            ((schemeRestriction (properQuotFibre f B) U).obj
              ((moduleTensorPullback (properQuotFst f B)).obj F.obj)).IsFlatOver
              (yoneda.preimage (U.obj.hom ≫ (properQuotSnd f B).hom.hom)).left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
