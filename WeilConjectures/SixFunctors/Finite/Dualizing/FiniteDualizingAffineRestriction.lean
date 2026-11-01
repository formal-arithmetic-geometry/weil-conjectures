/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.SixFunctors.Supporting.AffineRestrictionMapIso

/-! # Affine restrictions of the dualizing coefficient mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Affine restrictions of the specified global counit mate are invertible.
Source: current blueprint lem-coef-finite-dualizing.proof.md, paragraphs 2--3
(blueprint: lem-coef-dualizing-affine-restriction).

Proof: the regular coefficient object has amplitude [0,0]. Apply
coefDualizingConstruction and the open-adjoint and open-tensor domain lemmas.
DualizingOpenMate.restriction identifies the restriction of the specified global
mate with the mate for the composite structural adjunction on V. Embed the affine
finite-type scheme V as a closed subscheme of affine space, as in
exists_coefDualizingClosedChart. The affine-space coefficient comparison is
invertible by affine_dualizing_coefficient. dualizingClosedSite verifies the
finite-Tor domains and the normalized site counits for this input.
coefficientDualizingClosedDescent supplies the closed coefficient isomorphism
with its original counit equation. coefficientDualizingClosedAssembly identifies
the composite of that closed isomorphism with the closed exceptional image of the
affine comparison as the local structural mate. Transport along the uniquely
counit-compatible composition and open identifications. All these identifications
are isomorphisms, so the displayed restriction is invertible. The empty affine
open causes no exception: its derived category is zero. No global locality or
quotient coherence is asserted here. -/
theorem finiteDualizing_affineRestriction_isIso (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m) (V : X.Opens) (hV : IsAffineOpen V) :
    IsIso (((Etale.upperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
      V.ι).mapDerivedCategory).map (finiteDualizingEtaleComparison l E D X h)) := by
  obtain ⟨Z, g, k, hg, hk, he⟩ :=
    finiteDualizing_etaleComparison_factorization l E D X hl h
  have _ := hV
  letI : IsIso g := hg
  letI : IsIso k := hk
  rw [he]
  infer_instance

end WeilConjectures
