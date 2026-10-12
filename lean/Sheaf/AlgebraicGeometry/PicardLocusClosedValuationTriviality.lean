module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ValuationClosedFibreSectionVanishing
import Sheaf.AlgebraicGeometry.ValuationProperCoherentSections
import Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar

@[expose] public section

open scoped AlgebraicGeometry

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

/-!
# Generic-fibre triviality over a valuation ring

Source: More on Morphisms, Lemma 0EX8 (blueprint: lem-sc-picard-locus-closed-valuation-triviality).
-/

/-- Let `A` be a valuation ring with fraction field `K`, and let `f : X ⟶ Spec A` be
proper, flat, and of finite presentation (properness supplies quasi-compactness and
quasi-separatedness, so `LocallyOfFinitePresentation f` is finite presentation here).
`hX₀` says that the closed fibre `X₀ = X ×_A Spec (A ⧸ 𝔪)` is integral. `hglobal` says
`H⁰(X_K, O_{X_K}) = K`: the canonical map `K = Γ(Spec K, ⊤) → Γ(X_K, ⊤)` induced by the
projection `X_K ⟶ Spec K` is an isomorphism. `htriv` says that the pullback of `L` along
`X_K ⟶ X` is trivial. Then `L` is trivial on `X`.

Proof (Stacks 0EX8): `H⁰(X, L)` is a finitely presented, torsion-free, hence finite free
`A`-module; flat base change gives `H⁰(X, L) ⊗_A K = H⁰(X_K, L_K) = K`, so it is free of
rank one with a generator `s`. If `A` is a field there is nothing more to prove. Otherwise
`s` restricted to the integral closed fibre is nonzero (else `s` would be divisible by a
nonzero `π ∈ 𝔪`), so the zero scheme `Z(s)` is a relative effective Cartier divisor, flat
over `A`. As `s` trivializes `L` on `X_K`, `Z(s)_K` is empty; generizations lift along the
flat `Z(s) → Spec A`, so `Z(s)` is empty and `s` trivializes `L`.

Source: More on Morphisms, Lemma 0EX8
(blueprint: lem-sc-picard-locus-closed-valuation-triviality). -/
theorem generic_fibre_triviality_over_valuation_ring
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (hX₀ : IsIntegral (pullback f (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))))
    (hglobal : IsIso (pullback.snd f (Spec.map
      (CommRingCat.ofHom (algebraMap A K)))).appTop)
    (htriv : Nonempty ((Scheme.Modules.tensorPullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj L ≅
      SheafOfModules.unit _)) :
    Nonempty (L ≅ SheafOfModules.unit _) := by
  sorry

