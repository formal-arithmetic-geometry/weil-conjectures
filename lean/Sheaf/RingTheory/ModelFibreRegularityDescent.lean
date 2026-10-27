/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.FibreLocalRingNaturalIso

/-!
# Faithfully flat comparison of model fibre local rings

Source: Stacks Project, Tag 056Y, proof of `lemma-slice-given-element`, second paragraph
(blueprint: lem-trf-model-fibre-regularity-descent).

Mathlib orders the factors of a fibre as `κ(p) ⊗ B`. Consequently the base-changed model
fibre is written `κ(p) ⊗[κ(p₀)] (κ(p₀) ⊗[A₀] B₀)`. The scalar structure on `κ(p)` is
specified by equality with `Ideal.ResidueField.map`; it is the canonical residue-field
extension, with no condition on the original base change. The equations on pure tensors
and on elements before localization characterize all the comparison maps uniquely.
-/

@[expose] public section

universe u₀ u v₀ v

set_option autoImplicit false

open scoped TensorProduct

namespace Algebra

/-- The canonical comparison of model fibres induces a faithfully flat local map of
fibre stalks, the natural quotient identifications, and descent of a regular singleton.

Source: Stacks Project, Tag 056Y, proof of `lemma-slice-given-element`, second paragraph
(blueprint: lem-trf-model-fibre-regularity-descent).

Proof:
1. The contraction equation `hp₀` gives the canonical embedding of residue fields:
   `a/s` maps to `f(a)/f(s)`; denominators remain outside the contracted prime.
2. Tensor balancing gives the displayed comparison `Φ`, with the stated pure-tensor
   formula. Its inverse uses `e.symm`, sending `(t ⊗ b₀) ⊗ λ` to
   `(λ * t̄) ⊗ (1 ⊗ b₀)`. Both composites fix pure tensors.
3. By lem-weil-pbc-fibre-ring-localization-quotient, the fibre prime over `q` is the
   kernel of the map to `κ(q)`. In the fraction description membership is equivalent
   to the numerator belonging to `q`. Its contraction to the model fibre lies over `q₀`.
4. Apply lem-weil-pbc-field-extension-base-change-faithfully-flat to the model fibre
   and the residue-field extension. Transport through `Φ`, then apply
   lem-weil-pbc-flat-local-ring-maps at the chosen fibre prime. The induced localization
   map is flat and local; lem-weil-pbc-flat-local-hom-faithfully-flat makes it faithfully
   flat. Its defining equation before localization is the displayed equation for `ψ`.
5. Apply lem-weil-pbc-fibre-ring-local-ring-natural-iso to both fibres. The resulting
   quotient identifications send the class of `b/s` to `(1 ⊗ b)/(1 ⊗ s)`.
   Their equations on `b₀` and `b` identify the maps from the original algebras.
6. By lem-weil-pbc-faithfully-flat-universally-injective with the module equal to the
   source ring, `ψ` is injective. If `α₀ x = 0`, its image is `α ψ(x) = 0`.
   Regularity upstairs gives `ψ(x) = 0`, hence `x = 0`.
7. Membership of `e(1 ⊗ a₀)` in `q` puts `a₀` in `q₀` and its fibre-local image in
   the maximal ideal. Its principal ideal is therefore proper, so its quotient is
   nonzero. This and step 6 give def-weil-pbc-regular-sequence for the singleton.

The equations `hp`, `hq₀`, and `hp₀` name contractions. The additional scalar structure
on the residue fields is fixed uniquely by `hk`, rather than an additional hypothesis
on the rings. No flatness, finiteness, or Noetherian assumption is required. -/
theorem model_fibre_regularity_descent
    {A₀ : Type u₀} {A : Type u} {B₀ : Type v₀} {B : Type v}
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing B]
    [Algebra A₀ A] [Algebra A₀ B₀] [Algebra A B]
    (e : A ⊗[A₀] B₀ ≃ₐ[A] B)
    (q : Ideal B) [q.IsPrime]
    (p : Ideal A) [p.IsPrime] (hp : p = q.comap (algebraMap A B))
    (q₀ : Ideal B₀) [q₀.IsPrime]
    (hq₀ : q₀ = q.comap (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))
    (p₀ : Ideal A₀) [p₀.IsPrime] (hp₀ : p₀ = p.comap (algebraMap A₀ A))
    [Algebra p₀.ResidueField p.ResidueField]
    (hk : algebraMap p₀.ResidueField p.ResidueField =
      Ideal.ResidueField.map p₀ p (algebraMap A₀ A) hp₀) :
    p₀ = q₀.comap (algebraMap A₀ B₀) ∧
    ∃ Φ : p.ResidueField ⊗[p₀.ResidueField] (p₀.Fiber B₀) ≃ₐ[p.ResidueField] p.Fiber B,
      (∀ (c : p.ResidueField) (c₀ : p₀.ResidueField) (b₀ : B₀),
        Φ (c ⊗ₜ[p₀.ResidueField] (c₀ ⊗ₜ[A₀] b₀)) =
          (c * algebraMap p₀.ResidueField p.ResidueField c₀) ⊗ₜ[A] e (1 ⊗ₜ[A₀] b₀)) ∧
      ∃ (r : Ideal (p.Fiber B)) (_ : r.IsPrime),
        r.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧
        ∃ (r₀ : Ideal (p₀.Fiber B₀)) (_ : r₀.IsPrime),
          r₀ = r.comap (Φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ∧
          r₀.comap Algebra.TensorProduct.includeRight.toRingHom = q₀ ∧
          ∃ ψ : Algebra (Localization.AtPrime r₀) (Localization.AtPrime r),
            IsLocalHom ψ.algebraMap ∧
            Module.FaithfullyFlat (Localization.AtPrime r₀) (Localization.AtPrime r) ∧
            (∀ z : p₀.Fiber B₀,
              ψ.algebraMap (algebraMap (p₀.Fiber B₀) (Localization.AtPrime r₀) z) =
                algebraMap (p.Fiber B) (Localization.AtPrime r)
                  (Φ (1 ⊗ₜ[p₀.ResidueField] z))) ∧
            ∃ (ε₀ : (Localization.AtPrime q₀ ⧸
                  (p₀.map (algebraMap A₀ B₀)).map
                    (algebraMap B₀ (Localization.AtPrime q₀))) ≃+* Localization.AtPrime r₀)
              (ε : (Localization.AtPrime q ⧸
                  (p.map (algebraMap A B)).map
                    (algebraMap B (Localization.AtPrime q))) ≃+* Localization.AtPrime r),
              (∀ b₀ : B₀,
                ε₀ (Ideal.Quotient.mk _ (algebraMap B₀ (Localization.AtPrime q₀) b₀)) =
                  algebraMap (p₀.Fiber B₀) (Localization.AtPrime r₀) (1 ⊗ₜ[A₀] b₀)) ∧
              (∀ b : B,
                ε (Ideal.Quotient.mk _ (algebraMap B (Localization.AtPrime q) b)) =
                  algebraMap (p.Fiber B) (Localization.AtPrime r) (1 ⊗ₜ[A] b)) ∧
              (∀ b₀ : B₀,
                ψ.algebraMap
                  (ε₀ (Ideal.Quotient.mk _ (algebraMap B₀ (Localization.AtPrime q₀) b₀))) =
                  ε (Ideal.Quotient.mk _
                    (algebraMap B (Localization.AtPrime q) (e (1 ⊗ₜ[A₀] b₀))))) ∧
              ∀ a₀ : B₀, e (1 ⊗ₜ[A₀] a₀) ∈ q →
                Function.Injective (fun x : Localization.AtPrime r ↦
                  algebraMap (p.Fiber B) (Localization.AtPrime r)
                    (1 ⊗ₜ[A] e (1 ⊗ₜ[A₀] a₀)) * x) →
                RingTheory.Sequence.IsRegular (Localization.AtPrime r₀)
                  ([algebraMap (p₀.Fiber B₀) (Localization.AtPrime r₀) (1 ⊗ₜ[A₀] a₀)]) ∧
                algebraMap (p₀.Fiber B₀) (Localization.AtPrime r₀) (1 ⊗ₜ[A₀] a₀) ∈
                  IsLocalRing.maximalIdeal (Localization.AtPrime r₀) ∧
                Function.Injective (fun x : Localization.AtPrime r₀ ↦
                  algebraMap (p₀.Fiber B₀) (Localization.AtPrime r₀) (1 ⊗ₜ[A₀] a₀) * x) ∧
                Nontrivial (Localization.AtPrime r₀ ⧸ Ideal.span
                  {algebraMap (p₀.Fiber B₀) (Localization.AtPrime r₀) (1 ⊗ₜ[A₀] a₀)}) := by
  sorry

end Algebra
