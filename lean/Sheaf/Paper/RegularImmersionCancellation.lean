/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.PurityConventions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.Paper.PurityFrameClass
import Sheaf.Paper.PurityFrameIndependence
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

public import Sheaf.Paper.RegularImmersionClassData
public import Sheaf.Paper.RegularImmersionSignedEvaluation
/-!
# Counit-normalized cancellation of opposite Tate lines

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular,
def-pur-regular-immersion-cancellation (blueprint: def-pur-regular-immersion-cancellation).

All coefficients are the actual finite quotient of the fixed purity setting. Supported
classes use the published Hom model, and their restriction uses the section-normalized
closed coefficient exchange. The frame product is the existing ordered Kummer-boundary fold.

## Main declarations

* `regularCancellation`.
* `regularNegativeUnit`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u u'

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The native signed pullback has the required cancellation carrier.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-cancellation).
Proof: unfold the native shifted pullback carrier and regularTate. Both sides are
inverse image of the same shifted signed Tate sheaf and its corresponding target. -/
theorem regularCancellationPullbackType_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (type_of% (P.regularSignedPullback i aX (-(c : ℤ)))) =
      regularCancellationPullbackType (ModuleCat.{u + 1} P.Coefficient) i
        (P.regularTate X (-(c : ℤ))) (P.regularTate Z (-(c : ℤ))) := by
  sorry

/-- The actual signed pullback in the shared cancellation carrier.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-cancellation). -/
def regularCancellationPullback (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) :
    regularCancellationPullbackType (ModuleCat.{u + 1} P.Coefficient) i
      (P.regularTate X (-(c : ℤ))) (P.regularTate Z (-(c : ℤ))) :=
  cast (P.regularCancellationPullbackType_eq i aX c)
    (P.regularSignedPullback i aX (-(c : ℤ)))

/-- The displayed evaluation has the shared cancellation carrier.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-cancellation).
Proof: expand the two named carriers. Both are the same Hom from the tensor of the
oppositely shifted Tate lines to the degree-zero constant coefficient. -/
theorem regularCancellationEvaluationType_eq (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (c : ℕ) :
    P.regularEvaluationTarget X c =
      regularCancellationEvaluationType (ModuleCat.{u + 1} P.Coefficient) X
        (P.regularTate X c) (P.regularTate X (-(c : ℤ)))
        ((P.regularSingle X).obj (P.constant X)) := by
  sorry

/-- The actual dual evaluation in the shared cancellation carrier.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-cancellation). -/
def regularCancellationEvaluation (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (c : ℕ) :
    regularCancellationEvaluationType (ModuleCat.{u + 1} P.Coefficient) X
      (P.regularTate X c) (P.regularTate X (-(c : ℤ)))
      ((P.regularSingle X).obj (P.constant X)) :=
  cast (P.regularCancellationEvaluationType_eq X c) (P.regularEvaluation X c)

/-- The unique counit-normalized cancellation comparison. Its equation is the
co-projection mate: projection formula, coefficient pullback, this comparison, and
the exceptional counit equal the tensor of the original counit followed by dual
Tate evaluation. The equation uniquely determines the comparison, so no arbitrary
isomorphism is selected.
Source: the inverse twist in clause (c) of sk-thm-regular
(blueprint: def-pur-regular-immersion-cancellation).
Proof: the finite Tate line is invertible, so its projection formula is an isomorphism.
Apply the exceptional Hom equivalence to its inverse followed by the tensor of the
counit and the dual evaluation. The source is bounded below of etale origin, since
both the exceptional image and the finite Tate line are. This determines one map.
Repeat with the opposite Tate shift; the evaluation identities and the adjunction
triangles identify the composites with identities. Hence the map is an isomorphism.
The same Hom bijection and the invertible projection map prove uniqueness. -/
theorem regularCancellation_existsUnique (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX] (c : ℕ) :
    ∃! e : regularCancellationIso (ModuleCat.{u + 1} P.Coefficient) Z
        ((P.regularExceptional i aX).obj (P.regularTate X c))
        (P.regularTate Z (-(c : ℤ)))
        ((P.regularExceptional i aX).obj ((P.regularSingle X).obj (P.constant X))),
      RegularCancellationEquation (ModuleCat.{u + 1} P.Coefficient) i
        ((P.regularExceptional i aX).obj (P.regularTate X c))
        (P.regularTate Z (-(c : ℤ)))
        ((P.regularExceptional i aX).obj ((P.regularSingle X).obj (P.constant X)))
        (P.regularTate X c) (P.regularTate X (-(c : ℤ)))
        ((P.regularSingle X).obj (P.constant X)) (P.regularCancellationPullback i aX c) e
        (P.regularCounit i aX (P.regularTate X c) (P.regularTatePlus X c))
        (P.regularCounit i aX ((P.regularSingle X).obj (P.constant X))
          (P.regularConstantOrigin X).plus) (P.regularCancellationEvaluation X c) := by
  sorry

/-- The uniquely counit-normalized co-projection followed by evaluation.
Source: sk-thm-regular(c) (blueprint: def-pur-regular-immersion-cancellation). -/
def regularCancellation (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX] (c : ℕ) :=
  (P.regularCancellation_existsUnique i aX c).exists.choose

/-- The specified shifted coefficient action in its native generic carrier.
Source: inverse twisting of cl_i (blueprint: def-pur-regular-immersion-cancellation). -/
def regularNativeNegativeUnit (P : PurityFiniteSetting.{u}) (Z : Scheme.{u}) (c : ℕ) :=
  regularActionCanonical
    (P.constant Z) (P.regularSignedSheaf Z (-(c : ℤ))) (2 * (-(c : ℤ)))
    ((tensorIso (cupConstantIso P Z) (Iso.refl (P.regularSignedSheaf Z (-(c : ℤ))))).hom ≫
      (λ_ (P.regularSignedSheaf Z (-(c : ℤ)))).hom)

/-- The displayed negative-Tate unit-action Hom with its canonical tensor.
Source: inverse twisting of cl_i (blueprint: def-pur-regular-immersion-cancellation). -/
def regularNegativeUnitTarget (P : PurityFiniteSetting.{u}) (Z : Scheme.{u}) (c : ℕ) : Type _ :=
  (P.regularSingle Z).obj (P.constant Z) ⊗ P.regularTate Z (-(c : ℤ)) ⟶
    P.regularTate Z (-(c : ℤ))

/-- The native shifted-action carrier is the displayed negative-Tate unit Hom.
Source: inverse twisting of cl_i (blueprint: def-pur-regular-immersion-cancellation).
Proof: rewrite the shared tensor structure by regularTensorMonoidal_eq, then unfold
the common single-functor and signed-Tate references. Both carriers are the same Hom
in the same derived category with the same tensor and shift. -/
theorem regularNegativeUnitHom_eq (P : PurityFiniteSetting.{u}) (Z : Scheme.{u}) (c : ℕ) :
    (type_of% (P.regularNativeNegativeUnit Z c)) =
      P.regularNegativeUnitTarget Z c := by
  sorry

/-- The ordinary coefficient unit acting on the negative shifted line, localized
and shifted with the published exact comparisons.
Source: inverse twisting of cl_i (blueprint: def-pur-regular-immersion-cancellation). -/
def regularNegativeUnit (P : PurityFiniteSetting.{u}) (Z : Scheme.{u}) (c : ℕ) :
    P.regularNegativeUnitTarget Z c :=
  cast (P.regularNegativeUnitHom_eq Z c) (P.regularNativeNegativeUnit Z c)

/-- The coefficient-unit action is invertible.
Source: the inverse twist normalization (blueprint: def-pur-regular-immersion-cancellation).
Proof: the coefficient unit is flat; hence its single-complex tensor comparison is
an isomorphism. The remaining factors are the shift comparison, the constant-unit
identification and the ordinary left unitor, all isomorphisms. -/
theorem regularNegativeUnit_isIso (P : PurityFiniteSetting.{u}) (Z : Scheme.{u}) (c : ℕ) :
    IsIso (P.regularNegativeUnit Z c) := by
  sorry


/-- The class-isomorphism carrier with the native derived-category instance.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-cancellation). -/
def regularCancellationClassType (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (Z : Scheme.{u})
    (U M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) : Type _ :=
  U ≅ M

/-- The coefficient-unit isomorphism carrier with the native derived tensor.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-cancellation). -/
def regularCancellationUnitType (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Z : Scheme.{u})
    (U N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) : Type _ :=
  U ⊗ N ≅ N

/-- Invert the specified class, tensor its negative line and apply the coefficient unit.
Source: sk-thm-regular(c), equivalent displayed purity isomorphism
(blueprint: def-pur-regular-immersion-cancellation). -/
@[no_expose]
def regularCancelledIsoGeneral (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Z : Scheme.{u})
    (M N V U : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (e : regularCancellationIso A Z M N V) (f : regularCancellationClassType A Z U M)
    (a : regularCancellationUnitType A Z U N) :=
  e.symm ≪≫ tensorIso f.symm (Iso.refl N) ≪≫ a

/-- The coefficient action isomorphism has the same native tensor carrier.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-cancellation).
Proof: unfold both carriers. The single object, negative signed Tate line and
published derived tensor are identical; only the names of their instances differ. -/
theorem regularNegativeUnitIsoType_eq (P : PurityFiniteSetting.{u})
    (Z : Scheme.{u}) (c : ℕ) :
    (type_of% (@asIso _ _ _ _ (P.regularNegativeUnit Z c)
      (P.regularNegativeUnit_isIso Z c))) =
      regularCancellationUnitType (ModuleCat.{u + 1} P.Coefficient) Z
        ((P.regularSingle Z).obj (P.constant Z)) (P.regularTate Z (-(c : ℤ))) := by
  sorry

/-- The same coefficient unit isomorphism in the shared native carrier.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-cancellation). -/
def regularCancellationUnitIso (P : PurityFiniteSetting.{u}) (Z : Scheme.{u}) (c : ℕ) :
    regularCancellationUnitType (ModuleCat.{u + 1} P.Coefficient) Z
      ((P.regularSingle Z).obj (P.constant Z)) (P.regularTate Z (-(c : ℤ))) :=
  cast (P.regularNegativeUnitIsoType_eq Z c)
    (@asIso _ _ _ _ (P.regularNegativeUnit Z c) (P.regularNegativeUnit_isIso Z c))

end WeilConjectures.PurityFiniteSetting
