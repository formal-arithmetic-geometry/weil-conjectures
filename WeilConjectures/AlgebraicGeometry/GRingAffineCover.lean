/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.RingTheory.GRing
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.RingTheory.RegularRingEquiv

/-!
# G-rings on affine opens of a scheme

Source: Stacks Project, Properties of Schemes, Tag 0HA5, equivalence (3) and (2)
(blueprint: lem-trf-g-ring-affine-cover).
-/

@[expose] public section

universe u v

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

/-- The G-ring property passes from an affine open cover to every affine open.

Source: Stacks Project, Properties of Schemes, Tag 0HA5, equivalence (3) and (2)
(blueprint: lem-trf-g-ring-affine-cover).

Proof: (1) The G-ring hypothesis says each affine chart ring is Noetherian, so the
cover gives local Noetherianity. (2) The affine-open local-Noetherianity theorem makes
the section ring of the arbitrary affine open Noetherian. (3) For each prime of that
ring, identify its localization with the corresponding localization of a covering
chart through their common stalk, using the affine-open point and stalk-localization
statements. (4) Transport the adic completion map across the resulting ring
isomorphism using the compatible-completion equivalence. (5) Transport regularity of
the chart completion map through this commuting square using invariance of regular
ring maps under ring equivalences. (6) The Noetherianity and regularity conditions
are exactly the definition of a G-ring.
-/
theorem isGRing_of_affine_open_cover
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.affineOpens)
    (hU : ⨆ i, (U i : X.Opens) = ⊤)
    (h : ∀ i, IsGRing Γ(X, U i)) (V : X.affineOpens) :
    IsGRing Γ(X, V) := by
  have : IsLocallyNoetherian X :=
    isLocallyNoetherian_of_affine_cover hU (fun i ↦ (h i).1)
  refine ⟨IsLocallyNoetherian.component_noetherian V, ?_⟩
  intro q hq
  let y : PrimeSpectrum Γ(X, V) := ⟨q, hq⟩
  let x : X := V.2.fromSpec y
  have hx : x ∈ (V : X.Opens) := (V.2.isoSpec.inv y).2
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (U i : X.Opens) := by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [hU]
    trivial
  let p := ((U i).2.primeIdealOf ⟨x, hi⟩).asIdeal
  let : Algebra Γ(X, U i) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hi⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
    (U i).2.isLocalization_stalk ⟨x, hi⟩
  let a : Localization.AtPrime p ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv p.primeCompl _ _).toRingEquiv
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    V.2.isLocalization_stalk' y hx
  let b : X.presheaf.stalk x ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv q.primeCompl _ _).toRingEquiv
  let e := a.trans b
  obtain ⟨E, hE⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)) e
    (IsLocalRing.map_ringEquiv_maximalIdeal e).symm
  exact RingHom.IsRegular.of_ringEquiv _ _ e E hE ((h i).2 p)

end AlgebraicGeometry
