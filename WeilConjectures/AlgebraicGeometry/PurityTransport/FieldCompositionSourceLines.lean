/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceGeometricData
import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceLineProduct
import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceLinePullback

/-! # Scalar compatibility of normalized Tate multiplication and pullback

Source: smooth composition's coefficient passage, root and power calculation.
(blueprint: lem-pur-field-composition-source-lines). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Scheme
open CategoryTheory.Functor.OplaxMonoidal
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
attribute [local irreducible] DerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

/-- The two Tate-line identities needed by the source-word calculation.
They concern only shifted lines, with no arbitrary coefficient complex and no
trace or smooth adjunction. Source: smooth composition, scalar passage Step 2.
(blueprint: lem-pur-field-composition-source-lines).

Proof in words. Apply fieldCompositionSourceLineProduct to Px,d,e and apply
fieldCompositionSourceLinePullback to p,p',Px,Py,e. The global exactness
hypothesis supplies exact scalar extension on X for the first application.
Pair the two equations. Their separate proofs record the ordinary-power,
derived-single and shift-normalization calculations. -/
theorem fieldCompositionSourceLines
    (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (hunit : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom T))]
    {X Y : Scheme.{u}} [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)]
    (f : X ⟶ Y) (p : LinePullCoordinates ell c f)
    (p' : LinePullCoordinates ell c' f)
    (Px : ScalarLineCoordinates ell a hunit X)
    (Py : ScalarLineCoordinates ell a hunit Y) (d e : ℕ) :
    letI := fieldCompScalarMonoidal ell a X
    letI := _root_.DerivedCategory.braidedCategory'
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X))
    letI := _root_.DerivedCategory.braidedCategory'
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c'.obj ell) X))
    ((scalarSixChange a X).map
        (((derivedProduct ell c X d e).symm ≪≫ β_ _ _).hom) ≫
      δ (scalarSixChange a X) (c.derivedLine ell X e) (c.derivedLine ell X d) ≫
        (scalarLineMap ell a X e (Px.power e) ⊗ₘ
          scalarLineMap ell a X d (Px.power d)) =
      scalarLineMap ell a X (d + e) (Px.power (d + e)) ≫
        (((derivedProduct ell c' X d e).symm ≪≫ β_ _ _).hom)) ∧
    ((scalarSixChange a X).map (p.derived ell e).inv ≫
        (fieldCompScalarPull ell a f).hom.app (c.derivedLine ell Y e) ≫
        (actualPull (c'.obj ell) f).map (scalarLineMap ell a Y e (Py.power e)) ≫
        (p'.derived ell e).hom = scalarLineMap ell a X e (Px.power e)) := by
  exact ⟨fieldCompositionSourceLineProduct ell a hunit X Px d e,
    fieldCompositionSourceLinePullback ell a hunit f p p' Px Py e⟩

end AlgebraicGeometry.ProEtale.PurityTransport
