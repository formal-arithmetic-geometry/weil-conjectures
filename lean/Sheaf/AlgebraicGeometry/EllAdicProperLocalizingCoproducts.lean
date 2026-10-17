/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure
public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Proper adic direct image preserves coproducts on the constructible localizing hull

Source: blueprint `sk-thm-existence` (2), with the identity compactification of a proper map.
(blueprint: lem-sfb-adic-proper-localizing-coproducts)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k hΛ

/-- Proper derived pushforward, restricted to the source localizing hull, preserves
small coproducts. The target here is still the full ambient derived category.

Source: blueprint `sk-thm-existence` (2), `det-proper-image-localizing-proper`,
`sk-lem-proper-unbounded-window-ii`, and `det-prop-int-compactness-direct-sums` (3).
(blueprint: lem-sfb-adic-proper-localizing-coproducts)

Proof: distinguish the three constructors of the coefficient certificate. The schemes
and their locally closed strata are Noetherian. For E and Qlbar, identify the library's
local finite presentations with lisse local models using
`exists_finiteFree_cover_of_condensedField_lfp` and `condensedQbar_lfp_locally_free`.
For OE, use `integral_lfp_local_torsion_charts` and
`integral_lfp_locallyFree_resolution` for the integral constructible comparison and
finite Tor amplitude. These comparisons concern ordinary module sheaves; they do not
replace their ambient coproducts by completed coproducts.
In the E and Qlbar cases, bounded constructibility equals constructibility with finite Tor
amplitude. The subcategory of complexes with ind-constructible cohomology contains
bounded constructible complexes and is replete, triangulated and closed under ambient
sums (`det-ambient-ind-derived-sums` (3)). It therefore contains the source hull.
The proper unbounded-window theorem gives preservation of sums on this larger
subcategory: a uniform geometric fibre-dimension bound reduces each target cohomology
degree to a fixed finite truncation window, where proper direct-image continuity
commutes with sums. For Qlbar use the finite-subextension coefficient convention.
In the OE case, choose a uniform bound d on geometric fibre dimensions. Integral
proper finiteness gives the bound [0, 2d+1] on ind-constructible sheaves; the associated
truncation window gives preservation of sums on ind-constructible complexes and hence
on the hull (`det-prop-int-compactness-direct-sums` (1)-(3)). In each case the comparison
comes from the coprojections. Its cohomology maps are the continuity comparisons just
proved, so it is an isomorphism and the image cocone is a coproduct cocone. This also
handles the empty family, for which exact pushforward sends zero to zero.
-/
theorem ellAdic_localizingLowerStar_preservesCoproducts (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      ((boundedConstructibleLocalizingClosure Λ Z.left).ι ⋙ R((g.left)_*⟦Λ⟧)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
