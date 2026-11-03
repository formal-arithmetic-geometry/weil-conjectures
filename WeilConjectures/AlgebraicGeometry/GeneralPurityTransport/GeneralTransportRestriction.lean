/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransportData
public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ExplicitSmoothAdjunctionData

/-! # Restricting the explicit normalized smooth adjunction family

Source: latest blueprint, sec-smooth-purity/sk-thm-purity-transport,
proof Step 3 and the coefficient and affine normalization paragraphs.
(blueprint: lem-pur-general-transport-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityTransport

/-- Forget only the extra separated-over-the-field indices. The map, dimension and
compactification stay the supplied ones.
Source: proof Step 3 (blueprint: lem-pur-general-transport-restriction). -/
def SmoothDatum.explicit {k : Type u} [Field k] (s : SmoothDatum k) :
    ExplicitSmoothComparison.Datum k :=
  { X := s.X.left
    Y := s.Y.left
    base := s.Y.hom
    map := s.map
    dim := s.dim
    compactification := s.compactification }

/-- The family restriction reuses the literal adjunction, including its counit.
Source: proof Step 3 (blueprint: lem-pur-general-transport-restriction). -/
def restrictExplicitFamily (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    (b : ExplicitSmoothComparison.Family ell k) : AdjunctionFamily ell k := fun c s ↦
  { support_closed := (b c s.explicit).support_closed
    source_closed := (b c s.explicit).source_closed
    adjunction := (b c s.explicit).adjunction }

/-- Restriction retains the same scalar counit equation, with every normalized
comparison unchanged. Source: proof Step 4
(blueprint: lem-pur-general-transport-restriction). -/
theorem restrictExplicitFamily_scalar (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] (b : ExplicitSmoothComparison.Family ell k)
    (hb : ExplicitSmoothComparison.ScalarCompatible ell k b) :
    ScalarCompatible ell k (restrictExplicitFamily ell b) := by
  intro c c' a ha
  obtain ⟨h, H⟩ := hb c c' a ha
  exact ⟨h, fun s ↦ H s.explicit⟩

end AlgebraicGeometry.ProEtale.GeneralPurityTransport
