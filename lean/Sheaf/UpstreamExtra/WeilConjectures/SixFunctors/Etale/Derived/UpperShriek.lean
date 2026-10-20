module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow

/-!
Declarations moved out of `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`
by the scheduled upstream sync on 2026-10-20.
-/

/-!

# Derived Upper Shriek

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *defined* here as a chosen right adjoint of the derived lower shriek `Rf_!` on the
unbounded derived categories of étale sheaves. It is defined whenever `Rf_!` is a left adjoint,
which is taken as an instance argument.

# Main Results

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : for torsion coefficients,
  `A = ModuleCat Λ` with `Λ` finite, `Rf_!` is a left adjoint on `D(X_ét)`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét) ⥤ D(X_ét)`, with scoped
  notation `R(f)^![A]`, for `Rf_!` a left adjoint.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

- `AlgebraicGeometry.Etale.HasBoundedBelowUpperShriek` : `Rf^!` exists and preserves bounded
  below objects, an instance for torsion coefficients over a quasi-compact base; and
  `AlgebraicGeometry.Etale.HasBoundedBelowUpperShrieks`, the same for every `f` with
  quasi-compact target.

## Implementation notes

* That `Rf_!` is a left adjoint is *not* true for an arbitrary coefficient category: it rests
  on `Rg_*` preserving coproducts for the proper part `g` of the compactification, which needs
  `Rg_*` to have finite cohomological dimension, i.e. torsion coefficients. For general `A` the
  existence of the right adjoint is therefore an instance argument
  `[(R(f)_![A]).IsLeftAdjoint]` of `rightDerivedUpperShriek`, and it is supplied as an instance
  only at the torsion coefficients `ModuleCat Λ`, `[Finite Λ]`
  (`isLeftAdjoint_rightDerivedLowerShriek`). That instance is the blueprint theorem
  `thm-amb-etale-exceptional-adjoint` of the smooth-purity chapter (Brown representability,
  Stacks `0F5Y`, applied to the coproduct-preserving `Rf_!`), proved in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.
* `Rf^!` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint extracted from
  the instance, not a construction. Only the adjunction `rightDerivedUpperShriekAdjunction`
  should be used about it; it has no definitional content.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.
* No bounded below variant of `Rf^!` is defined here. The ambient `Rf^!` preserves `D⁺` only
  through the finite cohomological amplitude of `Rf_!`, and the bounded below exceptional
  functor of the blueprint is the constructible one of `sk-prop-sf-existence` (c). That `Rf^!`
  preserves `D⁺` is recorded, together with the existence of `Rf^!`, by the hypothesis class
  `AlgebraicGeometry.Etale.HasBoundedBelowUpperShriek`, which the pro-étale adjunction for
  `Rf^!` assumes; it is an instance for torsion coefficients when `Y` is quasi-compact
  (`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`). Quasi-compactness is needed: for
  `Y = ⊔ₙ Spec k` and `X = ⊔ₙ ℙⁿ_k`, `f` proper, `Rf^! Λ` is `Λ(n)[2n]` on `ℙⁿ_k`, which is not
  bounded below.

## TODO

* The composition `R(f ≫ g)^! ≅ R(g)^! ⋙ R(f)^!`, from the corresponding compatibility
  of `Rf_!`.
* For `f` étale, `Rf^! = f^*`; for `f` proper, `Rf^!` is right adjoint to `Rf_*`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section TorsionCoefficients

variable (Λ : Type (u + 1)) [CommRing Λ]

end TorsionCoefficients

section Unbounded

variable [(R(f)_![A]).IsLeftAdjoint]

end Unbounded

section BoundedBelow

/-- For finite coefficients and a uniform global upper-amplitude bound `N` for `Rf_!`,
the exceptional inverse image preserves bounded below objects.

Source: SGA 4, Exp. XVIII, 3.1.7; the adjunction and t-structure orthogonality argument.
(blueprint: lem-etale-upper-shriek-bounded-below-from-amplitude)

Proof: if `K` is bounded below by `n` and `L` is bounded above by `n - N - 1`, the
amplitude hypothesis bounds `Rf_! L` above by `n - 1`. Every morphism from `Rf_! L`
to `K` is zero by t-structure orthogonality. The adjunction identifies these morphisms
with those from `L` to `Rf^! K`, so orthogonality bounds `Rf^! K` below by `n - N`.
The bound must be global: finite coefficients alone do not supply a uniform `N`
when the fibre dimensions of the compactification are unbounded. -/
theorem hasBoundedBelowUpperShriek_of_amplitude (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : ℤ)
    (hN : ∀ (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (n : ℤ), DerivedCategory.TStructure.t.IsLE L n →
        DerivedCategory.TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) (n + N)) :
    HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f := by
  refine { plus_rightDerivedUpperShriek_obj := ?_ }
  intro K hK
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - N, ?_⟩
  change DerivedCategory.TStructure.t.IsGE ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) (n - N)
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - N - 1) (n - N) (by omega)]
  intro L φ hL
  have := hn
  have : DerivedCategory.TStructure.t.IsLE
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) (n - 1) := by
    convert hN L (n - N - 1) hL using 1
    omega
  let adj := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f
  apply (adj.homEquiv L K).symm.injective
  rw [adj.homAddEquiv_symm_zero]
  exact DerivedCategory.TStructure.t.zero _ (n - 1) n (by omega)


private theorem exists_uniform_proper_dimension_bound
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] [CompactSpace T]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ d : ℕ, ∀ (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj G) := by
  exact exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite p

attribute [instance] HasBoundedBelowUpperShrieks.isLeftAdjoint
  HasBoundedBelowUpperShrieks.hasBoundedBelowUpperShriek

/-- If every compactifiable morphism has a uniform upper-amplitude bound for `Rf_!`,
finite coefficients have exceptional inverse images preserving bounded below objects.
The amplitude bound is an explicit hypothesis, rather than a consequence of finiteness.

Source: `hasBoundedBelowUpperShriek_of_amplitude` and `HasBoundedBelowUpperShrieks`.
(blueprint: lem-etale-upper-shrieks-bounded-below-from-amplitude)

Proof: for each compactifiable morphism f, take its amplitude bound N and apply
`hasBoundedBelowUpperShriek_of_amplitude f Λ N` to the given bound. Return the resulting
bound for all morphisms, including non-quasi-compact targets, and build the upstream global
class from it. Only proofs of propositions are constructed. -/
theorem hasBoundedBelowUpperShrieks_of_amplitude (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (h : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f],
      ∃ N : ℤ, ∀ (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (n : ℤ), DerivedCategory.TStructure.t.IsLE L n →
          DerivedCategory.TStructure.t.IsLE ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) (n + N)) :
    HasBoundedBelowUpperShrieks (ModuleCat.{u + 1} Λ) ∧
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f],
        HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f := by
  have hall : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f],
      HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f := by
    intro X Y f hf
    obtain ⟨N, hN⟩ := h f
    simpa only using hasBoundedBelowUpperShriek_of_amplitude f Λ N hN
  refine ⟨?_, hall⟩
  constructor
  · intro X Y f hf
    infer_instance
  · intro X Y f hf hcompact
    exact hall f

end BoundedBelow

end Etale

end AlgebraicGeometry
