/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Limit
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import all WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.OpensCone

/-!
# Absolute Noetherian approximation

Every quasi-compact quasi-separated scheme admits a Noetherian approximation
(`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, Stacks Project Tag 01ZA), by
induction over a finite affine cover.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.NoetherianApproximation in
/-- (Implementation) **Absolute Noetherian approximation** for a finite union of affine
opens of a quasi-separated scheme, by induction on the number of members of the union
(Stacks Project Tag 07RN). -/
private lemma nonempty_noetherianApproximation_finsetSup {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (s : Finset X.Opens) (hs : ∀ V ∈ s, IsAffineOpen V) :
    Nonempty ((s.sup id : X.Opens).toScheme.NoetherianApproximation) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      have h : IsAffine ((⊥ : X.Opens).toScheme) := isAffineOpen_bot X
      exact ⟨Scheme.NoetherianApproximation.ofIsAffine _⟩
  | insert a s ha ih =>
      obtain ⟨N₀⟩ := ih fun V hV ↦ hs V (Finset.mem_insert_of_mem hV)
      have haff : IsAffineOpen a := hs a (Finset.mem_insert_self a s)
      have hsaff : ∀ V ∈ s, IsAffineOpen V := fun V hV ↦ hs V (Finset.mem_insert_of_mem hV)
      rw [Finset.sup_insert, id]
      set Y : X.Opens := a ⊔ s.sup id with hYdef
      have : QuasiSeparatedSpace Y.toScheme :=
        (isQuasiSeparated_iff_quasiSeparatedSpace _ Y.2).mp (.of_quasiSeparatedSpace _)
      set U : Y.toScheme.Opens := Y.ι ⁻¹ᵁ (s.sup id) with hUdef
      set V : Y.toScheme.Opens := Y.ι ⁻¹ᵁ a with hVdef
      have hUV : U ⊔ V = ⊤ := by
        rw [hUdef, hVdef, ← Scheme.Hom.preimage_sup, sup_comm, ← hYdef,
          Scheme.Opens.ι_preimage_self]
      have hVaff : IsAffineOpen V := by
        refine haff.preimage_of_isOpenImmersion Y.ι ?_
        rw [Scheme.Opens.opensRange_ι]
        exact le_sup_left
      -- the approximation of `U`, transported from the induction hypothesis
      have hrange : Set.range (X.homOfLE (le_sup_right : s.sup id ≤ Y)) =
          Set.range (Scheme.Opens.ι U) := by
        rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
          Scheme.opensRange_homOfLE, Scheme.Opens.opensRange_ι]
      have N : U.toScheme.NoetherianApproximation :=
        N₀.ofIso (IsOpenImmersion.isoOfRangeEq _ _ hrange)
      -- the intersection `U ⊓ V` is quasi-compact
      have hsc : IsCompact ((s.sup id : X.Opens) : Set X) :=
        isCompact_finset_sup s fun V hV ↦ (hsaff V hV).isCompact
      have hinfc : IsCompact (((s.sup id ⊓ a : X.Opens)) : Set X) := by
        rw [TopologicalSpace.Opens.coe_inf]
        exact QuasiSeparatedSpace.inter_isCompact _ _ (s.sup id).2 hsc a.2 haff.isCompact
      have hUVc : IsCompact ((U ⊓ V : Y.toScheme.Opens) : Set Y.toScheme) := by
        have he : (U ⊓ V : Y.toScheme.Opens) = Y.ι ⁻¹ᵁ (s.sup id ⊓ a) := by
          rw [hUdef, hVdef, Scheme.Hom.preimage_inf]
        rw [he]
        refine Y.ι.isOpenEmbedding.isInducing.isCompact_preimage' hinfc ?_
        rw [Scheme.Opens.range_ι]
        exact le_trans inf_le_left le_sup_right
      have hUVc' : IsCompact ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) := by
        have he : (U.ι ⁻¹ᵁ V : U.toScheme.Opens) = U.ι ⁻¹ᵁ (U ⊓ V) := by
          rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
        rw [he]
        refine U.ι.isOpenEmbedding.isInducing.isCompact_preimage' hUVc ?_
        rw [Scheme.Opens.range_ι]
        exact inf_le_left
      obtain ⟨i₀, W₀, hW₀c, hW₀⟩ :=
        exists_preimage_eq N.D (Cone.mk _ N.π) N.isLimit _ hUVc'
      -- the generators of the intersection
      obtain ⟨t, ht⟩ := hVaff.exists_finset_basicOpen_eq hUVc inf_le_right
      obtain ⟨m, eq⟩ : ∃ m, Nonempty ({x // x ∈ t} ≃ Fin m) := ⟨t.card, ⟨t.equivFin⟩⟩
      obtain ⟨eq⟩ := eq
      have hcov : (U ⊓ V : Y.toScheme.Opens) =
          ⨆ l : Fin m, Y.toScheme.basicOpen ((eq.symm l : {x // x ∈ t}) :
            Γ(Y.toScheme, V)) := by
        have h1 : (⨆ f ∈ t, Y.toScheme.basicOpen f) =
            ⨆ x : {x // x ∈ t}, Y.toScheme.basicOpen (x : Γ(Y.toScheme, V)) :=
          iSup_subtype' (p := fun x : Γ(Y.toScheme, V) ↦ x ∈ t)
            (f := fun x _ ↦ Y.toScheme.basicOpen x)
        rw [ht, h1, ← Equiv.iSup_comp (g := fun x : {x // x ∈ t} ↦
          Y.toScheme.basicOpen (x : Γ(Y.toScheme, V))) eq.symm]
      exact ⟨Scheme.NoetherianApproximation.ExtensionData.approximation
        { X := Y.toScheme, U := U, V := V, hUV := hUV, hV := hVaff, N := N, i₀ := i₀,
          W₀ := W₀, hW₀c := hW₀c, hW₀ := hW₀, n := m,
          b := fun l ↦ ((eq.symm l : {x // x ∈ t}) : Γ(Y.toScheme, V)),
          hb := fun l ↦ hcov ▸ le_iSup (fun l : Fin m ↦ Y.toScheme.basicOpen
            ((eq.symm l : {x // x ∈ t}) : Γ(Y.toScheme, V))) l,
          hb' := hcov }⟩

/-- **Absolute Noetherian approximation** (Stacks Project Tag 01ZA): every quasi-compact
quasi-separated scheme is the limit of a cofiltered system of schemes of finite type over
`ℤ` with affine transition morphisms.

The affine case is `AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`. The
general case follows by induction over a finite affine cover: each step extends an
approximation of a quasi-compact open across one more affine open, see
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData.approximation`.
(Blueprint: `prop:nagata-noetherian-inverse-system`.) -/
@[stacks 01ZA]
theorem Scheme.nonempty_noetherianApproximation (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    Nonempty S.NoetherianApproximation := by
  classical
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    S.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) (by simpa using isCompact_univ)
  obtain ⟨N⟩ := nonempty_noetherianApproximation_finsetSup hUsfin.toFinset
    (fun V hV ↦ hUsB (hUsfin.mem_toFinset.mp hV))
  rw [Finset.sup_id_eq_sSup, hUsfin.coe_toFinset, ← hUs] at N
  exact ⟨N.ofIso S.topIso⟩

end AlgebraicGeometry
