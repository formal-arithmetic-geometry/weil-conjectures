/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.SetTheory.Cardinal.ENat
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.TraceFormula.SmoothComponentPureTranscendental
import Sheaf.TraceFormula.GeometricFibreComponentCountBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-!
# The diagonal component of a smooth self-product

Source: Ning Guo, Divisors on coherent schemes and homogeneous spaces, Lemma 4.3(i)-(ii),
printed page 10, March 31, 2026 version; specialize both factors to `Y` and the graph to
its diagonal (blueprint: lem-sfb-smooth-self-product-component-rank).

The component count is defined directly using the canonical geometric point. At the
residue field of a generic point this is the geometric generic component count `ρ`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The number of geometric irreducible components of the fibre of `f` at `t`, with value
`∞` for an infinite component set. For a generic point of a nonempty integral target,
this is the count `ρ_f` used in Guo, Lemma 4.3, printed page 10 (March 31, 2026).
The fibre is the actual pullback along the canonical algebraic-closure geometric point.
(blueprint: lem-sfb-smooth-self-product-component-rank). -/
noncomputable def Scheme.Hom.geometricIrreducibleComponentCount
    {Z T : Scheme.{u}} (f : Z ⟶ T) (t : T) : ℕ∞ :=
  ENat.card (irreducibleComponents
    ↥(pullback f (T.fromSpecAlgebraicClosureResidueField t)))

/-- A smooth separated finite type integral family over a normal affine Noetherian
integral base has a finite clopen integral decomposition of its self-product. The
component containing the diagonal has geometrically integral generic fibre and count
one; the other component counts are positive and strictly smaller than the original
count. The sum is the original count, and all assertions restrict to nonempty affine
opens of the first factor.

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Lemma 4.3(i)-(ii),
printed page 10 (March 31, 2026), with `X = Y` and `g = id`.
(blueprint: lem-sfb-smooth-self-product-component-rank).

Proof:
1. Base change preserves smoothness, separatedness and finite type
   (`lem-pc-proper-base-change`, `lem-pod-separated-finite-type-base-change`). Finite type
   over a Noetherian scheme gives Noetherianity of `Y` and then `W`
   (`lem-weil-pbc-finite-type-over-noetherian`). Smooth ascent gives normality
   (`lem-sfb-smooth-normal-ascent`). Noetherian opens have finitely many components
   (`lem-weil-pbc-noetherian-open-subscheme-noetherian`,
   `lem-weil-pbc-noetherian-finite-components`), so normality gives disjoint clopen
   integral components (`lem-sfb-normal-locally-finite-components`).
2. Their inclusions are open and closed immersions. Open restriction preserves
   smoothness (`lem-weil-pbc-smooth-restrict-open-subschemes`); closed immersions are
   finite type (`lem-weil-pbc-closed-immersion-proper`), and composition preserves it
   (`lem-sfb-finite-type-composition-base-change`). Their diagonals are base changes
   of the separated projection's diagonal (`lem-weil-pbc-closed-immersion-base-change`).
3. Smooth maps are flat and locally finitely presented (`lem-pc-smooth-flat`), hence
   open (`lem-weil-pbc-flat-lfp-open`). Nonempty open images in integral targets are
   dense and contain the generic point. Thus `f` and every component projection are
   dominant, their generic fibres are nonempty, and `f ξ = η`.
4. The generic fibre of each component is irreducible: two nonempty fibre opens lift
   to nonempty opens of the integral component. Their intersection is nonempty and
   has open image containing the target generic point, so it meets the generic fibre.
5. The irreducible diagonal image lies in exactly one clopen component. Factor it
   through this open (`lem-weil-pbc-morphism-factors-through-open-subscheme`); the
   pullback identities make the factor a section. At `ξ` it gives a rational point
   of the connected component that is the generic fibre of this distinguished piece.
6. Apply `lem-trf-smooth-component-pure-transcendental` to this rational point, whose
   residue extension is purely transcendental in zero variables. The distinguished
   generic fibre is geometrically integral, so its geometric component count is one.
7. All geometric generic fibres are nonempty by
   `lem-sfb-field-extension-irreducible-components` and
   `lem-sc-irreducible-components-cover`, and finite type over fields, hence Noetherian.
   Their irreducible component counts are positive finite integers.
8. `lem-trf-geometric-fibre-component-count-base-change` identifies the self-product's
   geometric generic count with that of `f`. The finite clopen partition pulls back
   (`lem-weil-pbc-open-fibre-product`); each irreducible component lies in exactly one
   piece. Thus the counts sum to `N`; the distinguished summand is one, yielding the
   strict upper bound for every other positive summand.
9. For a nonempty affine open `B`, base change is the open preimage in each component
   (`lem-weil-pbc-open-fibre-product`). Dominance makes it nonempty; a nonempty open
   of an integral normal scheme is integral and normal. Base change preserves its
   morphism properties. The generic point lies in `B` with unchanged residue field,
   so the geometric generic fibres and counts agree. Base change restricts the section.
-/
theorem exists_smooth_selfProduct_component_rank
    {S Y : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S] [IsIntegral S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : Y ⟶ S) [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsIntegral Y] (η : S) (ξ : Y)
    (hη : IsGenericPoint η Set.univ) (hξ : IsGenericPoint ξ Set.univ) :
    ∃ N : ℕ, 0 < N ∧ f.geometricIrreducibleComponentCount η = (N : ℕ∞) ∧
      IsNoetherian (pullback f f) ∧
      (∀ w : ↥(pullback f f), IsDomain ((pullback f f).presheaf.stalk w) ∧
        IsIntegrallyClosed ((pullback f f).presheaf.stalk w)) ∧
      ∃ (m : ℕ) (C : Fin (m + 1) → (pullback f f).Opens) (r : Fin (m + 1) → ℕ),
        Function.Injective C ∧
        Set.range (fun i ↦ (C i : Set ↥(pullback f f))) =
          irreducibleComponents ↥(pullback f f) ∧
        (∀ i, IsClosed (C i : Set ↥(pullback f f)) ∧ IsIntegral (C i).toScheme ∧
          (∀ c : (C i).toScheme, IsDomain ((C i).toScheme.presheaf.stalk c) ∧
            IsIntegrallyClosed ((C i).toScheme.presheaf.stalk c)) ∧
          Smooth ((C i).ι ≫ pullback.fst f f) ∧
          IsSeparated ((C i).ι ≫ pullback.fst f f) ∧
          LocallyOfFiniteType ((C i).ι ≫ pullback.fst f f) ∧
          QuasiCompact ((C i).ι ≫ pullback.fst f f) ∧
          DenseRange ((C i).ι ≫ pullback.fst f f) ∧
          ((C i).ι ≫ pullback.fst f f).geometricIrreducibleComponentCount ξ = (r i : ℕ∞)) ∧
        (∀ i, Set.range (pullback.diagonal f) ⊆ (C i : Set ↥(pullback f f)) ↔ i = 0) ∧
        r 0 = 1 ∧ (∑ i, r i) = N ∧ (∀ i, i ≠ 0 → 1 ≤ r i ∧ r i < N) ∧
        GeometricallyIntegral (((C 0).ι ≫ pullback.fst f f).fiberToSpecResidueField ξ) ∧
        ∃ δ : Y ⟶ (C 0).toScheme,
          δ ≫ (C 0).ι = pullback.diagonal f ∧
          δ ≫ ((C 0).ι ≫ pullback.fst f f) = 𝟙 Y ∧
          ∀ (B : Y.Opens), IsAffineOpen B → (B : Set Y).Nonempty →
            ∃ b : B.toScheme, IsGenericPoint b Set.univ ∧
              (∀ i,
                IsOpenImmersion (pullback.fst ((C i).ι ≫ pullback.fst f f) B.ι) ∧
                IsIntegral (pullback ((C i).ι ≫ pullback.fst f f) B.ι) ∧
                (∀ c : ↥(pullback ((C i).ι ≫ pullback.fst f f) B.ι),
                  IsDomain ((pullback ((C i).ι ≫ pullback.fst f f) B.ι).presheaf.stalk c) ∧
                  IsIntegrallyClosed
                    ((pullback ((C i).ι ≫ pullback.fst f f) B.ι).presheaf.stalk c)) ∧
                Smooth (pullback.snd ((C i).ι ≫ pullback.fst f f) B.ι) ∧
                IsSeparated (pullback.snd ((C i).ι ≫ pullback.fst f f) B.ι) ∧
                LocallyOfFiniteType (pullback.snd ((C i).ι ≫ pullback.fst f f) B.ι) ∧
                QuasiCompact (pullback.snd ((C i).ι ≫ pullback.fst f f) B.ι) ∧
                Scheme.Hom.geometricIrreducibleComponentCount
                  (pullback.snd ((C i).ι ≫ pullback.fst f f) B.ι) b = (r i : ℕ∞)) ∧
              ∃ δB : B.toScheme ⟶ pullback ((C 0).ι ≫ pullback.fst f f) B.ι,
                δB ≫ pullback.fst ((C 0).ι ≫ pullback.fst f f) B.ι = B.ι ≫ δ ∧
                δB ≫ pullback.snd ((C 0).ι ≫ pullback.fst f f) B.ι = 𝟙 B.toScheme := by
  sorry

end AlgebraicGeometry
