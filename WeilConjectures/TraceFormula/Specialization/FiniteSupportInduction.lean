/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.FiniteSupportDiagonal
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import WeilConjectures.Mathlib.Topology.Sober
public import WeilConjectures.TraceFormula.OpenClosedTriangle
public import WeilConjectures.TraceFormula.OpenCover
public import WeilConjectures.TraceFormula.ConstructibleGeneration

/-!

# Finite direct image is conservative

Let `f : Z ⟶ B` be a finite morphism of separated `k`-schemes of finite type. If a bounded
constructible `ℚ̄_ℓ`-complex `F` on `Z` satisfies `Rf_* F = 0`, then `F = 0`
(`ProEtale.CondensedRing.isZero_of_isZero_lowerStar_of_isFinite`).

The proof is a noetherian induction on the open `O ⊆ B` over which `F` is known to vanish. If
`F|_{f⁻¹ O} = 0` and `S = B ∖ O` is non-empty, give `S` its reduced structure; then `F` is the
pushforward of its restriction `G` to `f⁻¹ S`, and `Rf_{S*} G = 0` since the pushforward along the
closed immersion `S ⟶ B` is fully faithful. Above a generic point `ξ` of `S` the fibre of
`f⁻¹ S ×_S f⁻¹ S` is finite and discrete, so the diagonal has open image above an open
neighbourhood `V` of `ξ` in `S` (`AlgebraicGeometry.exists_isOpen_range_diagonal_inter_preimage`),
and `G` vanishes above `V` (`isZero_upperStar_opensOverι_of_isOpen_range_diagonal`). Hence `F`
vanishes over a strictly larger open `O ∪ V'`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated TopologicalSpace

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

namespace ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

/-! ### Closed subschemes and their preimages -/

section Closed

variable {B : Over (Spec (.of k))} (S : Closeds B.left)

/-- The closed subset `S` of `B` with its reduced structure, as a scheme over `s`. -/
noncomputable abbrev closedOver : Over (Spec (.of k)) :=
  Over.mk ((IdealSheafData.vanishingIdeal S).subschemeι ≫ B.hom)

instance [LocallyOfFiniteType B.hom] : LocallyOfFiniteType (closedOver S).hom :=
  inferInstanceAs (LocallyOfFiniteType ((IdealSheafData.vanishingIdeal S).subschemeι ≫ B.hom))

instance [QuasiCompact B.hom] : QuasiCompact (closedOver S).hom :=
  inferInstanceAs (QuasiCompact ((IdealSheafData.vanishingIdeal S).subschemeι ≫ B.hom))

instance [IsSeparated B.hom] : IsSeparated (closedOver S).hom :=
  inferInstanceAs (IsSeparated ((IdealSheafData.vanishingIdeal S).subschemeι ≫ B.hom))

variable {Z : Over (Spec (.of k))} (f : Z ⟶ B)

end Closed

/-! ### Detection and the induction -/

section Induction

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {Z B : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  (f : Z ⟶ B) [IsFinite f.left]

end Induction

end ProEtale.CondensedRing

end AlgebraicGeometry
