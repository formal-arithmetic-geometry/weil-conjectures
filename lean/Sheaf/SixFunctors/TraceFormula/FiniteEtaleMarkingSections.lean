/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import WeilConjectures.FieldTheory.GenericSeparableAlgebraSplitting
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.NagataDomainN2
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Splitting a finite étale marking into disjoint sections after alteration

Source: literature/stacks-project/pione.tex, Tag 0BQL, and
Illusie–Laszlo–Orgogozo, Exposé IX, §1.4, p. 133
(blueprint: lem-trf-finite-etale-marking-sections).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Splitting a finite étale marking into disjoint sections after alteration.

Source: literature/stacks-project/pione.tex, Tag 0BQL, and
Illusie–Laszlo–Orgogozo, Exposé IX, §1.4, p. 133
(blueprint: lem-trf-finite-etale-marking-sections).

The geometric fibres are compared as schemes over the algebraically closed field `Ω`: the
isomorphism commutes with the two projections to `Spec Ω`.

Proof.
1. The fibres of `D → B` are discrete unions of spectra of finite separable field
   extensions; they are proper over a field, hence quasi-compact, hence finite.  As `B` is
   locally Noetherian and `D → B` is proper with finite fibres, `D → B` is finite, so
   `D_η = Spec C` with `C` a finite `K`-algebra, `K = κ(η)`.
2. Choose a finite separable `L / K` such that `(C ⊗_K L)_red` is a product of purely
   inseparable extensions of `L`.  Since `C ⊗_K L` is étale over `L`, it is reduced and each
   factor is separable and purely inseparable, hence equal to `L`:
   `D_η ×_K L ≅ ∐_{i < n} Spec L`.  If `D` is empty take `L = K` and `n = 0`.
3. Let `b : B₁ → B` be the normalization of `B` in `L`; `B₁` is normal and integral with
   function field `L`.  Affine opens of `B` have excellent, hence Nagata and N-2, rings, so
   the integral closure is finite: `b` is finite, hence proper and closed, and it is
   surjective since its image contains the generic point.
4. `a : X₁ = X ×_B B₁ → X` is finite and surjective by base change.  The affine opens of
   `B₁` and `X₁` lying over affine opens of `B` and `X` have finite, hence finite type,
   algebras over excellent rings, so `B₁` and `X₁` are excellent and Noetherian.
5. `g₁` is proper, flat and of finite presentation by base change; the base change of the
   smooth `g|_V` is `g₁|_{a⁻¹(V)}`, so `g₁` is smooth at every point of `a⁻¹(V)`.
6. The generic fibre of `g₁` is `X_η ×_K L`: geometrically integral, proper (so separated
   and of finite type) over `L`, and of dimension one, hence a geometrically integral curve.
   For `t̄ : Spec Ω → B₁`, associativity of fibre products gives
   `X₁ ×_{B₁} Spec Ω ≅ X ×_B Spec Ω` over `Spec Ω`, the right side along `b ∘ t̄`.
7. `X₁` is integral: on a nonempty affine `Spec A ⊆ X₁` over `Spec R ⊆ B₁`, flatness makes
   `A → A ⊗_R L` injective, and `A ⊗_R L` is a nonempty affine open of the integral generic
   fibre, so `A` is a domain; two nonempty opens meet because their generic parts do.
8. `D₁ = D ×_X X₁ ≅ D ×_B B₁` is a finite étale closed subscheme of `X₁`.  Put
   `T = ∐_{i < n} B₁`, finite étale over `B₁`, with generic fibre that of `D₁` by Step 2.
9. Over the normal integral base `B₁`, restriction of finite étale covers to the generic
   point is fully faithful, so the generic isomorphism and its inverse extend uniquely to
   mutually inverse `B₁`-morphisms `h : T ≅ D₁`.
10. `s_i = h ∘ ι_i` followed by `D₁ → X₁` is a section of `g₁`; the summands are disjoint,
   open and closed, so `D₁` is the disjoint union of the closed subschemes `s_i(B₁)`, which
   lie in `a⁻¹(V)` since `D ⊆ V`.  For `D` empty, `n = 0`.
-/
theorem exists_finite_etale_marking_sections
    {X B : Scheme.{u}} (g : X ⟶ B)
    [IsIntegral X] [IsIntegral B]
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian B] [CompactSpace B]
    (hX : ∀ U : X.Opens, IsAffineOpen U → IsExcellent Γ(X, U))
    (hB : ∀ U : B.Opens, IsAffineOpen U → IsExcellent Γ(B, U))
    [IsProper g] [Flat g] [LocallyOfFinitePresentation g]
    (η : B) (hη : IsGenericPoint η Set.univ)
    [GeometricallyIntegral (g.fiberToSpecResidueField η)]
    [IsIntegralCurve (g.fiberToSpecResidueField η)]
    (D : Scheme.{u}) (i : D ⟶ X) (hi : IsEffectiveCartierCenter i)
    (hDV : ∀ d : D, i d ∈ g.smoothLocus)
    [IsProper (i ≫ g)] [Etale (i ≫ g)] :
    ∃ (B₁ : Scheme.{u}) (b : B₁ ⟶ B),
      IsIntegral B₁ ∧
        (∀ U : B₁.Opens, IsAffineOpen U → IsExcellent Γ(B₁, U)) ∧
        IsLocallyNoetherian B₁ ∧
      CompactSpace B₁ ∧ IsFinite b ∧ IsIntegralHom b ∧ Surjective b ∧
      IsIntegral (pullback g b : Scheme.{u}) ∧
        (∀ U : (pullback g b : Scheme.{u}).Opens,
          IsAffineOpen U → IsExcellent Γ(pullback g b, U)) ∧
      IsLocallyNoetherian (pullback g b : Scheme.{u}) ∧ CompactSpace (pullback g b : Scheme.{u}) ∧
      IsFinite (pullback.fst g b) ∧ Surjective (pullback.fst g b) ∧
      IsProper (pullback.snd g b) ∧ Flat (pullback.snd g b) ∧
      LocallyOfFinitePresentation (pullback.snd g b) ∧
      (∃ η₁ : B₁, IsGenericPoint η₁ Set.univ ∧
        GeometricallyIntegral ((pullback.snd g b).fiberToSpecResidueField η₁) ∧
        IsIntegralCurve ((pullback.snd g b).fiberToSpecResidueField η₁)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (tbar : Spec (.of Ω) ⟶ B₁),
        ∃ e : pullback (pullback.snd g b) tbar ≅ pullback g (tbar ≫ b),
          e.hom ≫ pullback.snd g (tbar ≫ b) = pullback.snd (pullback.snd g b) tbar) ∧
      (∀ x : (pullback g b : Scheme.{u}),
        (pullback.fst g b) x ∈ g.smoothLocus →
          x ∈ (pullback.snd g b).smoothLocus) ∧
      (∃ (n : ℕ) (s : ∀ j : Fin n, B₁ ⟶ pullback g b)
        (e : (∐ fun _ : Fin n ↦ B₁) ≅ pullback i (pullback.fst g b)),
        (∀ j : Fin n, s j = Sigma.ι (fun _ : Fin n ↦ B₁) j ≫ e.hom ≫
          pullback.snd i (pullback.fst g b)) ∧
        (∀ j : Fin n, s j ≫ pullback.snd g b = 𝟙 B₁) ∧
        (∀ ⦃j k⦄, j ≠ k →
          Disjoint (Set.range (s j)) (Set.range (s k))) ∧
        (∀ j : Fin n, IsClosedImmersion (Sigma.ι (fun _ : Fin n ↦ B₁) j ≫ e.hom)) ∧
        (∀ j : Fin n, ∀ x : B₁, (pullback.fst g b) (s j x) ∈ g.smoothLocus) ∧
        (IsEmpty D → n = 0)) := by
  sorry

end AlgebraicGeometry
