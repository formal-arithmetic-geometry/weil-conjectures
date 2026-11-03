/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedAdjunctionCoordinates

/-! # Detecting completeness using the actual adjunction unit

Source: sk-lem-sp-tower-equivalence.proof.md, Unit paragraph.
(blueprint: lem-sp-normalized-completion-detection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Identification with the specified Roos augmentation detects precisely derived
completeness, with no geometric assumption on T.

Source: sk-lem-sp-tower-equivalence.proof.md, Unit paragraph
(blueprint: lem-sp-normalized-completion-detection).
Proof: choose a native K-flat representative of K and use representative independence
of derived completeness. The completion comparison identifies the augmentation with
the unit followed by an isomorphism. Cancel that isomorphism in both directions. -/
theorem normalized_unit_iff (D : Model l E T) (adj : D.red ⊣ D.rlim)
    (h : CompletionUnitNormalized l E T D adj) (K : Integral l E T) :
    IsIso (adj.unit.app K) ↔ IsDerivedComplete l E T K := by
  obtain ⟨P, hP, ⟨e⟩⟩ :=
    CondensedRing.exists_kFlat_iso_Qh_obj (DerivedNakayama.integerRing l E) K
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have hflat := (HomotopyCategory.kFlat_quotient_obj_iff _).mp hP
  let e' : DerivedCategory.Q.obj P ≅ K :=
    (DerivedCategory.quotientCompQhIso _).symm.app P ≪≫ e
  obtain ⟨c, hc⟩ := h K P e' hflat
  rw [AdicCompletion.isDerivedComplete_iff l E T K P hflat e', ← hc]
  constructor
  · intro hi
    infer_instance
  · intro hi
    exact IsIso.of_isIso_comp_right (adj.unit.app K) c.hom

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
