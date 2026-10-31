/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenScalarTensorData
public import WeilConjectures.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import WeilConjectures.AlgebraicGeometry.CompactSupportIntrinsicTensorComparison

/-! # Compact-support coefficient maps in normalized scalar coordinates

Source: Stacks Tags 07A6 and 0GL6; current blueprint main-20261015,
sk-prop-sf-pf-reduction, coefficient comparison
(blueprint: def-sf-compact-support-scalar-coordinates).

These are the universal-arrow maps of def-coef-compact-support-tensor-comparison
in the normalized scalarPair and openExtension presentations. The recorded intrinsic
comparison instead uses pbcDerivedExtend and sfIntrinsicCompactSupport. Those chosen
functors are not definitionally these presentations. We therefore evaluate the same
universal-arrow formula with the actual scalarPair units and Hom bijections, conjugating
only the open restriction comparison by reductionOpenModel. No coefficient map or
factorization identity is supplied as an extra parameter.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.OpenScalarTensor
namespace AlgebraicGeometry.ProEtale.PfReductionFactors

/-- The canonical restriction comparison in the normalized open-adjunction coordinates.
Only the published constant-section coordinate changes surround the intrinsic comparison.
Source: Stacks 0GL6 (blueprint: def-sf-compact-support-scalar-coordinates). -/
def compactRestriction {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (r : Z ⟶ Y) (N : proEtaleDerivedCategory X B) :
    (directImageConstantPush.{u} A r).obj
        ((openExtension.{u} (A := A) j).obj ((scalarRestriction.{u} φ X).obj N)) ⟶
      (scalarRestriction.{u} φ Y).obj
        ((directImageConstantPush.{u} B r).obj ((openExtension.{u} (A := B) j).obj N)) :=
  (directImageConstantPush.{u} A r).map
      ((reductionOpenModel.{u} A j).inv.app ((scalarRestriction.{u} φ X).obj N)) ≫
    (intrinsicCompactSupportRestriction.{u} φ j r).hom.app N ≫
    (scalarRestriction.{u} φ Y).map
      ((directImageConstantPush.{u} B r).map ((reductionOpenModel.{u} B j).hom.app N))

attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify in
/-- The actual compact-support coefficient arrow, defined by the scalar.{u} Hom bijection.
Its adjunct is compact support of the scalar unit followed by canonical restriction.
Source: Stacks 0GL6 and def-coef-compact-support-tensor-comparison
(blueprint: def-sf-compact-support-scalar-coordinates). -/
def compactScalar (m : Models.{u}) {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y)
    (K : proEtaleDerivedCategory X A) :
    (scalar.{u} m φ Y).obj
        ((directImageConstantPush.{u} A r).obj ((openExtension.{u} (A := A) j).obj K)) ⟶
      (directImageConstantPush.{u} B r).obj
        ((openExtension.{u} (A := B) j).obj ((scalar.{u} m φ X).obj K)) :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  letI : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let adjY : scalar.{u} m φ Y ⊣ scalarRestriction.{u} φ Y :=
    (scalarPair.{u} m φ Y).adjunction
  let adjX : scalar.{u} m φ X ⊣ scalarRestriction.{u} φ X :=
    (scalarPair.{u} m φ X).adjunction
  (adjY.homEquiv _ _).symm
    ((directImageConstantPush.{u} A r).map
        ((openExtension.{u} (A := A) j).map (adjX.unit.app K)) ≫
      compactRestriction.{u} φ j r ((scalar.{u} m φ X).obj K))

end AlgebraicGeometry.ProEtale.PfReductionFactors
