/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation

/-! # The tensor formula for arbitrary finite coefficients

Source: general-ring smooth purity, proof (3).

Source: general-ring smooth purity, proof (1)-(3).
(blueprint: lem-pur-finite-general-ring-tensor-formula).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

/-- The specified tensor/counit purity map is invertible and natural on intrinsic
constructible finite-Tor objects, for any finite coefficient ring with invertible exponent.
Source: general-ring smooth purity, proof (3); smooth tensor duality and its ordinary
etale/pro-etale origin transport
(blueprint: lem-pur-finite-general-ring-tensor-formula).

Proof: smooth tensor duality makes the ordinary tensor mate invertible. Tensoring
with the inverse of alpha preserves invertibility. Intrinsic finite-Tor constructible
objects have ordinary origins and invertible comparison counits; hence the actual
source-to-origin map is invertible and transports gamma to proGamma. Ordinary
exceptional preservation and comparison give the constructible finite-Tor target.
Naturality follows from that of the tensor mate and inverse comparison counit. -/
theorem finiteGeneralRingTensorFormula
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (L : Etale.DerivedCategoryModule A X)
    (alpha : Etale.dualizingComplex A f ≅ L) :
    FiniteGeneralRingTensorFormula A f L alpha := by
  constructor
  · intro K hK
    exact ⟨(Etale.FiniteSmoothPurity.proObjectsCtf A N hN hA f d hY L alpha K hK).2,
      Etale.FiniteSmoothPurity.proGammaIso A N hN hA f d hY L alpha K hK⟩
  · intro K K' hK hK' a
    exact Etale.FiniteSmoothPurity.proNaturality A f L alpha hK hK' a

end AlgebraicGeometry.ProEtale
