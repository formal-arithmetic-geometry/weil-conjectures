/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates

/-! # Pullback of the finite partial tensor

Source: the proper-factor calculation of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

end WeilConjectures.CompactSupportFiniteProjection

namespace WeilConjectures.CompactSupportFiniteProjection

/-- Pullback of the partial tensor, using the published fixed-scalar tensor comparison
and the specified pullback realizations. Both coefficient-equivalence units are
cancelled explicitly. No projection map or identity comparison is used to define it.
Source: def-exchange-projection, tensor comparison; prop-sf-pf-coherence, proper factor
(blueprint: def-sf-finite-partial-pullback-tensor). -/
def pullbackTensorComparison (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M : sixFunctorFiniteCategory D C E n hn Y)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (S.finite.pull f).obj (((partialTensor S Y).obj M).obj L) ≅
      ((partialTensor S X).obj ((S.finite.pull f).obj M)).obj ((torPull S f).obj L) := by
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let TY := fixedTensor (C := C) (E := E) (n := n) Y
  let P := fixedDerivedPull (C := C) (E := E) (n := n) f
  let LB : sixFunctorFiniteCategory D C E n hn Y := ⟨L.obj, L.property.1⟩
  exact ObjectProperty.isoMk _
    (pullRealization S f (((partialTensor S Y).obj M).obj L) ≪≫
      RX.functor.mapIso
        ((fixedPullComparison (C := C) (E := E) (n := n) f).symm.app
          (RY.inverse.obj (((partialTensor S Y).obj M).obj L).obj) ≪≫
        P.mapIso ((RY.unitIso.app ((TY.obj (RY.inverse.obj M.obj)).obj
          (RY.inverse.obj L.obj))).symm) ≪≫
        AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left (RY.inverse.obj M.obj) (RY.inverse.obj L.obj) ≪≫
        (TX.mapIso (fixedPullRealization S f M).symm).app (P.obj (RY.inverse.obj L.obj)) ≪≫
        (TX.obj (RX.inverse.obj ((S.finite.pull f).obj M).obj)).mapIso
          (fixedPullRealization S f LB).symm))

end WeilConjectures.CompactSupportFiniteProjection
