/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.SixFunctors.CondensedDualizingIdentification
public import WeilConjectures.SixFunctors.ModCondensedCachedInstances

/-! # Composition of the condensed Verdier coefficient comparison

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/
thm-coef-rational-verdier.proof.md, paragraphs 1 and 3.
(blueprint: lem-coef-rational-verdier-composition-equation).

The helpers specialize the prescribed exceptional adjoint to the coefficient unit
for an arbitrary finite-CD base field. The existing nativeDualizingObject and
nativeDualizingComparison have a finite-field datum as parameter and therefore do
not cover this base-field generality. The coefficient unit and point instances are reused.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)] (hcd : BaseFieldFiniteCD ell k)

/-- The specified dualizing object Ra^! Lambda for the structure morphism over k.
This uses the existing constructible exceptional functor and the existing regular
coefficient unit, without choosing a new adjunction or a dualizing presentation.
Source: thm-coef-rational-verdier.proof.md, paragraphs 1 and 3; det-def-sf-operations
(blueprint: lem-coef-rational-verdier-composition-equation). -/
def condensedCompositionOmega (Λ : ScalarSixRing.{u})
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    ConstantModelConstructibleFiniteTor Λ.X X.left :=
  (ctfExceptionalInverseImage Λ.X ell k hcd
    (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of k)))) hΛ).obj
      (nativeDualizingUnit Λ (Spec (.of k)))

/-- The canonical exceptional coefficient comparison at the coefficient unit,
followed by exceptional inverse image of the monoidal coefficient-unit identification.
Source: thm-coef-rational-verdier.proof.md, paragraphs 1 and 3, scalar-six comparisons
(blueprint: lem-coef-rational-verdier-composition-equation). -/
def condensedCompositionOmegaComparison {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (scalarExceptionalChange ell k a ha X).obj
        (condensedCompositionOmega ell k hcd Λ (listedCoefficientCtf ell a ha).1 X) ⟶
      condensedCompositionOmega ell k hcd Λ' (listedCoefficientCtf ell a ha).2.1 X :=
  (scalarSixCtfExceptionalComparison ell k hcd a ha
      (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of k))))).app
        (nativeDualizingUnit Λ (Spec (.of k))) ≫
    (ctfExceptionalInverseImage Λ'.X ell k hcd
      (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (Spec (.of k))))
      (listedCoefficientCtf ell a ha).2.1).map
        (ObjectProperty.isoMk _
          (Functor.Monoidal.εIso (scalarSixChange a (Spec (.of k)))).symm).hom

/-- The displayed b: the evaluation-transpose internal-Hom comparison followed
by internal Hom of the canonical exceptional coefficient comparison in its second slot.
It is defined on the ordinary uncompleted derived categories.
Source: thm-coef-rational-verdier.proof.md, paragraphs 1 and 3
(blueprint: lem-coef-rational-verdier-composition-equation). -/
def condensedCompositionVerdierComparison {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)) :
    (scalarSixChange a X.left).obj
        ((ihom K).obj
          (condensedCompositionOmega ell k hcd Λ (listedCoefficientCtf ell a ha).1 X).obj) ⟶
      (ihom ((scalarSixChange a X.left).obj K)).obj
        (condensedCompositionOmega ell k hcd Λ' (listedCoefficientCtf ell a ha).2.1 X).obj :=
  scalarSixHomComparison a X.left K
      (condensedCompositionOmega ell k hcd Λ (listedCoefficientCtf ell a ha).1 X).obj ≫
    (ihom ((scalarSixChange a X.left).obj K)).map
      (condensedCompositionOmegaComparison ell k hcd a ha X).hom

/-- The associator equation for the specified condensed Verdier coefficient arrows.
The last factor is contravariant internal Hom of the forward scalar associator.
Listed maps include identities, finite field extensions and nonflat finite reductions;
K lies in the finite-Tor constructible subcategory for all coefficients.
Source: thm-coef-rational-verdier.proof.md, paragraph 3 and paragraph 1
(blueprint: lem-coef-rational-verdier-composition-equation).

Proof:
1. Exceptional coefficient composition and monoidal unit compatibility give
u_j composed with T_j(u_i) equal to u_ji composed with alpha_omega. These are
comparisons for the prescribed constructible exceptional adjoints, at the unit.
2. Coefficient composition for the evaluation-transpose internal-Hom arrows gives
H(1,alpha_M) v_j T_j(v_i) = H(alpha_K,1) v_ji alpha_H(K,M), with both sides
landing in H(T_j T_i K,T_ji M). Specialize M to omega_0.
3. Naturality of v_j in its second argument moves T_j(H(1,u_i)) past v_j.
The two b arrows then expand to H(1,u_j T_j(u_i)) v_j T_j(v_i).
Substitute step 1 and then step 2. Bifunctoriality gives exactly the displayed
contravariant alpha_K factor. All tensors stay derived, so no flatness is used.
-/
theorem condensedVerdier_composition_equation {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}}
    (i : Λ₀ ⟶ Λ₁) (j : Λ₁ ⟶ Λ₂)
    (hi : ListedCoefficientMap ell i) (hj : ListedCoefficientMap ell j)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ₀.X X.left) :
    (scalarSixChange j X.left).map
        (condensedCompositionVerdierComparison ell k hcd i hi X K.obj) ≫
        condensedCompositionVerdierComparison ell k hcd j hj X
          ((scalarSixChange i X.left).obj K.obj) =
      (scalarSixTower i j X.left).hom.app
          ((ihom K.obj).obj
            (condensedCompositionOmega ell k hcd Λ₀ (listedCoefficientCtf ell i hi).1 X).obj) ≫
        condensedCompositionVerdierComparison ell k hcd (i ≫ j) (.comp i j hi hj) X K.obj ≫
        (MonoidalClosed.pre ((scalarSixTower i j X.left).hom.app K.obj)).app
          (condensedCompositionOmega ell k hcd Λ₂ (listedCoefficientCtf ell j hj).2.1 X).obj := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
