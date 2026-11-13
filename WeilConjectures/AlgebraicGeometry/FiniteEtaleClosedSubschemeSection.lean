/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.FiniteClopenOpenCoverSection
import WeilConjectures.AlgebraicGeometry.FiniteEtaleClosedSubschemeSectionOpens

/-!
# Étale covers of closed subschemes of an affine normal scheme

## References

* Stacks Project, Tag 09ZA
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine étale scheme over a closed subscheme of an affine integral normal scheme with
separably closed function field is a finite disjoint union of opens of the closed subscheme.
If the étale morphism is also finite and surjective, it admits a section
(Stacks, Tag 09ZA). -/
theorem Etale.exists_finite_clopen_opens_and_section_of_closedImmersion
    {X Z V : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
    (p : V ⟶ Z) [Etale p] [IsAffine V] :
    (∃ (n : ℕ) (W : Fin n → V.Opens),
      (∀ j, IsClosed (W j : Set V)) ∧
      (∀ j k, j ≠ k → Disjoint (W j) (W k)) ∧
      (⨆ j, W j) = ⊤ ∧
      ∀ j, IsOpenImmersion ((W j).ι ≫ p)) ∧
    (Surjective p → IsFinite p → ∃ s : Z ⟶ V, s ≫ p = 𝟙 Z) := by
  obtain ⟨n, W, hclosed, hdisj, hcov, hopen⟩ :=
    Etale.exists_finite_clopen_opens_of_closedImmersion hX i p
  refine ⟨⟨n, W, hclosed, hdisj, hcov, hopen⟩, ?_⟩
  intro hs hf
  let : Surjective p := hs
  let : IsFinite p := hf
  let (j : Fin n) : IsOpenImmersion ((W j).ι ≫ p) := hopen j
  obtain ⟨hcop⟩ := nonempty_isColimit_cofanMk_of (fun j ↦ (W j).ι)
    (by simpa using hcov) (by intro j k hjk; simpa using hdisj j k hjk)
  apply exists_section_of_finite_clopen_open_cover Z V p (fun j ↦ (W j).toScheme)
    (fun j ↦ (W j).ι) _ hcop (fun j ↦ (W j).ι ≫ p) (fun _ ↦ rfl)
  intro j
  refine ⟨inferInstance, IsClosedImmersion.of_isPreimmersion _ ?_⟩
  simpa using hclosed j

end AlgebraicGeometry
