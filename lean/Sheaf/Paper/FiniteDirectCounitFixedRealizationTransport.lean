/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.FiniteProjectionFixedCoordinates

/-! # Transport for the direct counit in fixed coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Transport of the fixed-coordinate counit to the intrinsic coefficient adjunction.
This is the coefficient-realization calculation used in the direct counit identity.
(blueprint: lem-sf-finite-direct-counit-fixed-realization-transport).

The proof expands the two prescribed coordinate comparisons, the K-flat comparison,
and the conjugated intrinsic adjunction.  Naturality of the equivalence units and
counits and the triangle identities cancel the intermediate comparison maps. -/
theorem directCounit_coordinate_transport (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    (fixedPullRealization S f ((S.finite.direct f).obj K)).hom ≫
      (fixedDerivedPull (C := C) (E := E) (n := n) f).map
        (directCoordinates S f K).hom ≫
      (fixedAdjunction (C := C) (E := E) (n := n) f).counit.app
        ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K) =
    (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.map
      ((S.finitePullback f).hom.app ((S.finite.direct f).obj K) ≫
        (sfIntrinsicPullback (Padic.coefficientExtensionRing C.l E n)
          f.hom.left).mapDerivedCategory.map
          ((S.finiteDirectImage f).hom.app K) ≫
        ((sfIntrinsicConstantModuleAdjunction f.hom.left
          (Padic.coefficientExtensionRing C.l E n)).mapDerivedCategoryRightDerivedAdjunction
          ).counit.app
          ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.obj K)) := by
  sorry


end WeilConjectures.CompactSupportFiniteProjection
