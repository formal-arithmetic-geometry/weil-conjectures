/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparisonData
/-! # The specified inverse-encoding projection square

Source: the finite native tensor comparison argument.
(blueprint: lem-pur-finite-native-encoding-projection-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.FiniteNativeTensor
open FiniteDiscreteOrdinary
-- Discard the imported instance with a free coefficient universe.
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [local instance 20000] sheafBraidedCategory sheafSymmetricCategory
  sheafMonoidalCategory sheafMonoidalClosed
  preservesColimitsOfSize_tensorLeft_sheaf preservesColimitsOfSize_tensorRight_sheaf
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- The inverse section-action encoding preserves the actual compactification projection,
with the fixed pure-tensor structure and the specified adjunction comparison.
Source: sk-prop-sp-composition, finite coefficient tensor-map comparison, Steps 1, 4
and 5; the normalized coefficient-heart comparison and its derived operation mates.
(blueprint: lem-pur-finite-native-encoding-projection-square).

Proof: on the hearts the chosen tensorator sends every local pure tensor to the
internal pure pairing. The direct-image comparison is identity on the same additive
sections, so its tensor equation follows from that pure-pairing formula and the
balanced tensor universal property. Uniqueness of the adjunction mate gives the
specified monoidal pullback comparison. Derive this exact monoidal square using
K-flat tensor comparisons; transport along the exact/left-derived identifications.
The right-derived direct-image comparison is the derived counit mate, by the
right-derived transformation uniqueness and factorization equations. Thus the
categorical projection-mate square applies to the proper factor. The open encoding
comparison is the stated left-adjoint-uniqueness comparison; its unit equation
identifies the inverse open projection as the same adjunct of the unit tensored
with identity. Invert that open equation, and paste it with the proper equation
and the pullback compositor. Finally invert the two monoidal encoding equivalences;
the triangle identities turn the resulting compact-support comparison into q below
and the pullback comparison into inverseEncodingPull. This gives the equation for
all unbounded ordinary inputs, without a constructibility, smoothness or field
hypothesis. All constructions use universal properties, so the zero ring and empty
scheme require no exception.
-/
theorem finiteNativeEncodingProjectionSquare (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
  letI := encodingMonoidal A X (E X)
  letI := encodingMonoidal A Y (E Y)
  letI := (E X).fixedDerived.inverseMonoidal
  letI := (E Y).fixedDerived.inverseMonoidal
  let q : nativeCompact A true c ⋙ (E Y).fixedDerived.inverse ≅
      (E X).fixedDerived.inverse ⋙ nativeCompact A false c :=
    Iso.isoInverseComp (G := (E X).fixedDerived) ((Functor.associator _ _ _).symm ≪≫
      Iso.compInverseIso (H := (E Y).fixedDerived) (compactEncoding A E c).symm)
  ∀ (M : Native A true X) (K : Native A true Y),
    (E Y).fixedDerived.inverse.map (nativeP A true c M K) ≫
        q.hom.app (M ⊗ (nativeUpper A true f).obj K) ≫
        (nativeCompact A false c).map
          ((Functor.Monoidal.μIso (E X).fixedDerived.inverse M
            ((nativeUpper A true f).obj K)).inv ≫
            (𝟙 ((E X).fixedDerived.inverse.obj M) ⊗ₘ
              (inverseEncodingPull A E f).inv.app K)) =
      (Functor.Monoidal.μIso (E Y).fixedDerived.inverse
        ((nativeCompact A true c).obj M) K).inv ≫
        (q.hom.app M ⊗ₘ
          𝟙 ((E Y).fixedDerived.inverse.obj K)) ≫
        nativeP A false c ((E X).fixedDerived.inverse.obj M)
          ((E Y).fixedDerived.inverse.obj K) := by sorry

end AlgebraicGeometry.ProEtale.FiniteNativeTensor
