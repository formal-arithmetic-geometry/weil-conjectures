/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Sheaf.RingTheory.LocalCompleteIntersectionFieldChange

/-!
# Complete-intersection residue charts after extending the residue field

Source: Stacks Project, Tags 01JR, 01I4 and 00SJ
(blueprint: lem-trf-lci-residue-chart-cover-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Residue-fibre charts cover after any field extension, with their canonical tensor
identifications. Source: Stacks Project, Tags 01JR, 01I4, 00SJ and 01T1
(blueprint: lem-trf-lci-residue-chart-cover-extension).

The algebra structures introduced by `letI` are the right-factor structures, so the
field acts by `u ↦ 1 ⊗ u`. The residue fibre uses Mathlib's
`p.Fiber (B b) = κ(p) ⊗[A] B b`; the canonical tensor symmetry identifies it
with the source's `B b ⊗[A] κ(p)`. The scalar-tower hypothesis specifies the composite
`A → κ(p) → K`; the chart equations specify the given morphism on every affine chart.

Proof:
1. The pullback equation puts the first projection inside `f ⁻¹ᵁ V`, since the second
   map factors through `V`. Pulling back the assumed union gives the asserted cover.
2. Apply lem-weil-pbc-open-fibre-product (Stacks 01JR) with opens `V`, `U b`, and
   all of `Spec K`. Then lem-weil-pbc-fibre-product-affine-spectra (Stacks 01I4)
   identifies each inverse-image open with `Spec (B b ⊗[A] K)`, with both projections.
3. The displayed formula for `E` respects the inner `A`-balancing and outer
   `κ(p)`-balancing. Its displayed inverse respects `A`-balancing because
   `(1 ⊗ rc) ⊗ u = (r̄ ⊗ c) ⊗ u = (1 ⊗ c) ⊗ r̄u`.
   The maps preserve addition, multiplication, units and `K`-scalars. Their composites
   fix pure tensors, hence are inverse. Taking spectra gives the second chart.
4. Apply lem-weil-pbc-lci-field-change (Stacks 00SJ) to the finite type residue
   algebra. Transport finite generation and the defining principal-open complete
   intersection presentations along `E`. The spectrum homeomorphism preserves dimension.
5. The resulting cover by finite type affine `K`-schemes proves local finite type
   (def-weil-finite-type-morphism, Stacks 01T1). The affine opens of `Spec K` are
   itself and the empty open. Zero rings give empty charts and are complete
   intersections by the convention in def-weil-pbc-complete-intersection-over-field.
   An empty covering family forces the pullback empty. -/
theorem lci_residue_chart_cover_extension
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    (A : Type u) [CommRing A] (V : Y.Opens) (eV : V.toScheme ≅ Spec (.of A))
    (J : Type w) (B : J → Type u) [∀ b, CommRing (B b)] [∀ b, Algebra A (B b)]
    (U : J → X.Opens) (eU : ∀ b, (U b).toScheme ≅ Spec (.of (B b)))
    (hchart : ∀ b, (U b).ι ≫ f =
      (eU b).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (B b))) ≫ eV.inv ≫ V.ι)
    (hcover : f ⁻¹ᵁ V = ⨆ b, U b)
    (p : Ideal A) [p.IsPrime] (K : Type u) [Field K]
    [Algebra p.ResidueField K] [Algebra A K] [IsScalarTower A p.ResidueField K]
    (t : Spec (.of K) ⟶ Y)
    (ht : t = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ eV.inv ≫ V.ι) :
    letI : ∀ b, Algebra K (B b ⊗[A] K) :=
      fun b ↦ Algebra.TensorProduct.rightAlgebra (R := A) (A := B b) (B := K)
    letI : ∀ b, Algebra K (p.Fiber (B b) ⊗[p.ResidueField] K) :=
      fun b ↦ Algebra.TensorProduct.rightAlgebra
        (R := p.ResidueField) (A := p.Fiber (B b)) (B := K)
    ∀ (hfin : ∀ b, Algebra.FiniteType p.ResidueField (p.Fiber (B b))),
      (∀ b, @Algebra.IsLocalCompleteIntersection p.ResidueField
        (p.Fiber (B b)) _ _ _ (hfin b)) →
      (⨆ b, (pullback.fst f t) ⁻¹ᵁ U b) = ⊤ ∧
      LocallyOfFiniteType (pullback.snd f t) ∧
      ∀ b, ∃ hfinK : Algebra.FiniteType K (B b ⊗[A] K),
        @Algebra.IsLocalCompleteIntersection K (B b ⊗[A] K) _ _ _ hfinK ∧
        ∃ E : (p.Fiber (B b) ⊗[p.ResidueField] K) ≃ₐ[K] (B b ⊗[A] K),
          (∀ (c : B b) (a : p.ResidueField) (z : K),
            E ((a ⊗ₜ[A] c) ⊗ₜ[p.ResidueField] z) =
              c ⊗ₜ[A] ((algebraMap p.ResidueField K a) * z)) ∧
          (∀ (c : B b) (z : K),
            E.symm (c ⊗ₜ[A] z) = ((1 : p.ResidueField) ⊗ₜ[A] c) ⊗ₜ[p.ResidueField] z) ∧
          ∃ (e₁ : ((pullback.fst f t) ⁻¹ᵁ U b).toScheme ≅ Spec (.of (B b ⊗[A] K)))
            (e₂ : ((pullback.fst f t) ⁻¹ᵁ U b).toScheme ≅
              Spec (.of (p.Fiber (B b) ⊗[p.ResidueField] K))),
            e₁.hom ≫ Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : B b →+* B b ⊗[A] K)) ≫
                (eU b).inv ≫ (U b).ι =
              ((pullback.fst f t) ⁻¹ᵁ U b).ι ≫ pullback.fst f t ∧
            e₁.hom ≫ Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight.toRingHom : K →+* B b ⊗[A] K)) =
              ((pullback.fst f t) ⁻¹ᵁ U b).ι ≫ pullback.snd f t ∧
            e₂.hom = e₁.hom ≫ Spec.map (CommRingCat.ofHom E.toRingHom) ∧
            e₂.hom ≫ Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight.toRingHom :
                K →+* p.Fiber (B b) ⊗[p.ResidueField] K)) =
              ((pullback.fst f t) ⁻¹ᵁ U b).ι ≫ pullback.snd f t := by
  sorry

end AlgebraicGeometry
