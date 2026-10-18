/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.EllAdicClosedSupportRepresentable
import Sheaf.AlgebraicGeometry.EllAdicAffineProjectionClosedSupportDuality
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-! # Bounded constructible representatives for compact support on an affine source -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] in
private theorem affine_closed_factorization
    {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [IsAffine U.left]
    (f : U ⟶ Y) :
    ∃ (n : Type u) (_ : Finite n) (i : U.left ⟶ 𝔸(n; Y.left)),
      IsClosedImmersion i ∧ i ≫ (𝔸(n; Y.left) ↘ Y.left) = f.left := by
  have hft : U.hom.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let := U.hom.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  let v : s → Γ(U.left, ⊤) := Subtype.val
  let i := AffineSpace.homOfVector f.left v
  refine ⟨s, inferInstance, i, ?_, AffineSpace.homOfVector_over _ _⟩
  have hgen : Subring.closure (Set.range U.hom.appTop ∪ Set.range v) = ⊤ := by
    have h := congrArg Subalgebra.toSubring hs
    rw [Algebra.adjoin_eq_ring_closure, Algebra.top_toSubring] at h
    change Subring.closure (Set.range U.hom.appTop ∪ (s : Set _)) = ⊤ at h
    rw [eq_top_iff, ← h]
    apply Subring.closure_mono
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  have hclosed := AffineSpace.isClosedImmersion_homOfVector U.hom v hgen
  have : IsClosedImmersion (i ≫ AffineSpace.map s Y.hom) := by
    dsimp only [i]
    rw [AffineSpace.homOfVector_map, Over.w f]
    exact hclosed
  have : IsSeparated (AffineSpace.map s Y.hom) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (AffineSpace.isPullback_map Y.hom).flip inferInstance
  exact IsClosedImmersion.of_comp i (AffineSpace.map s Y.hom)

include ℓ hΛ in
/-- Compact support from an affine source has a bounded constructible representative
when tested against bounded constructible complexes.

Source: blueprint `sk-thm-restriction/sk-thm-restriction-local.proof.md`, existence of
charts and constructibility paragraphs, and the integral counterpart
`sk-thm-int-restriction/sk-thm-int-restriction-glue.proof.md` (2).
Proof: choose finitely many generators of the global algebra of the affine source over
`k`. They give a closed embedding into affine space over `k`. The same coordinates over
`Y` give a morphism to relative affine space; its composite with the separated change of
base is that closed embedding, so it is also closed. Thus `f = i ≫ p`, with `i` closed
and `p` an affine-space projection. Affine projection duality with closed supports supplies
a bounded constructible object `P` on the affine space and natural bijections
`Hom(Rf! M, K) ≃ Hom(i_* M, P)`. The closed-support calculation supplies `L` and a counit
`i_* L → P`. Transport this counit back to `Rf! L → K`. Naturality identifies each
postcomposition map with the composite of the two Hom bijections. This proves the claimed
bijections without constructing a right adjoint or a localizing functor as new data.
(blueprint: lem-sfb-adic-affine-compact-support-representable) -/
theorem affine_compactSupport_representable
    {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [IsAffine U.left] (f : U ⟶ Y) (c : Compactification f.left)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ L : (boundedConstructible (condensedRingObj Λ U.left)).FullSubcategory,
      ∃ ε : (rightDerivedLowerShriekOfCompactification Λ c).obj L.obj ⟶ K.obj,
        ∀ M : (boundedConstructible (condensedRingObj Λ U.left)).FullSubcategory,
          Function.Bijective (fun a : M.obj ⟶ L.obj ↦
            (rightDerivedLowerShriekOfCompactification Λ c).map a ≫ ε) := by
  classical
  obtain ⟨n, hn, i₀, hi, hip⟩ := affine_closed_factorization f
  let _ := hn
  let A : Over (Spec (.of k)) := Over.mk ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom)
  let p : A ⟶ Y := Over.homMk (𝔸(n; Y.left) ↘ Y.left) rfl
  let i : U ⟶ A := Over.homMk i₀ (by
    dsimp only [A, Over.mk_hom]
    rw [← Category.assoc, hip, Over.w f])
  have : IsClosedImmersion i.left := hi
  have : LocallyOfFiniteType A.hom := by
    change LocallyOfFiniteType ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom)
    infer_instance
  have : QuasiCompact A.hom := by
    change QuasiCompact ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom)
    infer_instance
  have : IsSeparated A.hom := by
    change IsSeparated ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom)
    infer_instance
  have hf : i ≫ p = f := by
    ext
    exact hip
  let c' := c.copy (congrArg Over.Hom.left hf)
  obtain ⟨P, hP⟩ := affine_projection_closedSupport_duality Λ ℓ hΛ n K
  obtain ⟨hclosed, L, η, hη⟩ := closed_support_representable Λ ℓ hΛ i P
  let _ := hclosed
  obtain ⟨e, he⟩ := hP i c'
  let ε := (e L).symm η
  refine ⟨L, ε, fun M ↦ ?_⟩
  change Function.Bijective (fun a : M.obj ⟶ L.obj ↦
    (rightDerivedLowerShriekOfCompactification Λ c').map a ≫ ε)
  have heq : (fun a : M.obj ⟶ L.obj ↦
      (e M) ((rightDerivedLowerShriekOfCompactification Λ c').map a ≫ ε)) =
      (fun a : M.obj ⟶ L.obj ↦ D((i.left)_*⟦Λ⟧).map a ≫ η) := by
    funext a
    rw [he, Equiv.apply_symm_apply]
  apply ((e M).bijective.of_comp_iff' _).mp
  simpa only [Function.comp_def, heq] using hη M

end AlgebraicGeometry.ProEtale.CondensedRing
