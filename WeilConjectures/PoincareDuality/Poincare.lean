/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.SmoothPurity.Defs

/-!

# Poincaré duality for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime, `k` a field of characteristic `≠ ℓ` and `p : X ⟶ S` a smooth morphism of
pure relative dimension `d` of separated `k`-schemes of finite type. Smooth purity
(`ProEtale.CondensedRing.smoothPurityIso`) provides the chosen isomorphism
`pur_p : Rp^! ℚ̄_ℓ,S ≅ ℚ̄_ℓ,X(d)[2d]`, and this file defines from it, through the abstract
constructions of `WeilConjectures.PoincareDuality.Abstract`:

* the **trace** `Tr_p : Rp_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S`, the composite of `Rp_!(pur_p⁻¹)` and the
  counit of `Rp_! ⊣ Rp^!`;
* the **Poincaré duality morphism** `PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)`, the
  composite of `Rp_*(pur_p⁻¹)`, the identification `Rp^! ℚ̄_ℓ,S ≅ RHom(ℚ̄_ℓ,X, Rp^! ℚ̄_ℓ,S)` and
  the Verdier exchange morphism `Φ_{p,ℚ̄_ℓ,X,ℚ̄_ℓ,S}`;
* the **compact-support cup product**
  `cup_c : Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ Rp_! ℚ̄_ℓ,X(d)[2d]`, from the derived exceptional
  projection morphism and the counit of `Lp^* ⊣ Rp_*`.

All three share the normalization of `pur_p`: the transpose of `PD_p` is exactly `Tr_p ∘ cup_c`
(`ProEtale.CondensedRing.uncurry_poincareMap`), and `PD_p` is an isomorphism by Verdier
duality (`ProEtale.CondensedRing.isIso_poincareMap`), which is **Poincaré duality** in the
form `𝔻_S(Rp_! ℚ̄_ℓ,X) ≅ Rp_* ℚ̄_ℓ,X(d)[2d]`.

All objects live in the bounded constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`, which are
assumed to be monoidal closed subcategories of the ambient derived categories (instance
arguments, see `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`).

## Not treated here

* The passage from the derived statement to the perfect pairing
  `H^i_c(X, ℚ̄_ℓ) × H^{2d-i}(X, ℚ̄_ℓ(d)) ⟶ ℚ̄_ℓ` on cohomology groups over `S = Spec k̄`, which
  requires the perfectness of `Rp_! ℚ̄_ℓ,X` and the comparison of `RΓ(S, RHom(-, ℚ̄_ℓ,S))` with the
  linear dual.
* The Frobenius equivariance, which belongs to the Weil sheaf formalism.
* The compatibility with the compactly supported base change isomorphism and with the
  compactification and composition comparisons, which are commutativity conditions on the maps
  defined here, to be stated once those comparisons are available.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
  [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
  (p : X ⟶ S) [p.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d p]
  [(boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).IsMonoidal]
  [(boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)).IsMonoidal]
  [(boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).IsMonoidalClosed]
  [(boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)).IsMonoidalClosed]

/-- The **trace** `Tr_p : Rp_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S` of a smooth morphism `p : X ⟶ S` of pure
relative dimension `d`: `Rp_!(pur_p⁻¹)` followed by the counit of `Rp_! ⊣ Rp^!`. -/
noncomputable def trace :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ k p).obj
      (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶ 𝟙_ _ :=
  Verdier.trace (boundedConstructibleUpperShriekAdjunction _ ℓ k p) (smoothPurityIso ℓ k p d)

/-- The **Poincaré duality morphism**
`PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)`: `Rp_*(pur_p⁻¹)`, the identification
`Rp^! ℚ̄_ℓ,S ≅ RHom(ℚ̄_ℓ,X, Rp^! ℚ̄_ℓ,S)`, and the Verdier exchange morphism. -/
noncomputable def poincareMap :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k p).obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶
      (ihom ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ k p).obj
        (𝟙_ _))).obj (𝟙_ _) :=
  Verdier.poincareMap (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ k p)
    (boundedConstructibleUpperShriekAdjunction _ ℓ k p)
    (boundedConstructibleExceptionalProjectionMorphism _ ℓ k p) (smoothPurityIso ℓ k p d)

/-- The **compact-support cup product**
`cup_c : Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ Rp_! ℚ̄_ℓ,X(d)[2d]`: the derived exceptional
projection morphism `PF^!`, the counit `Lp^* Rp_* ⟶ 𝟭` and the left unitor. -/
noncomputable def cupProduct :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ k p).obj (𝟙_ _) ⊗
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k p).obj
          (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ k p).obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) :=
  Verdier.cupProduct (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ k p)
    (boundedConstructibleExceptionalProjectionMorphism _ ℓ k p)

omit [SmoothOfRelativeDimension d p] in
/-- **Poincaré duality is the trace–cup pairing**: the transpose
`Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S` of the Poincaré duality morphism is the cup product
followed by the trace. -/
theorem uncurry_poincareMap :
    uncurry (poincareMap ℓ k p d) = cupProduct ℓ k p d ≫ trace ℓ k p d :=
  Verdier.uncurry_poincareMap _ _ _ _
    (boundedConstructibleExceptionalProjectionMorphism_natural_right _ ℓ k p)

omit [SmoothOfRelativeDimension d p] in
/-- **Poincaré duality**: the Poincaré duality morphism
`PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)` is an isomorphism, by Verdier duality. -/
theorem isIso_poincareMap : IsIso (poincareMap ℓ k p d) := by
  have := isIso_verdierExchange (Profinite.padicAlgClRingObj ℓ) ℓ k p (𝟙_ _) (𝟙_ _)
  unfold poincareMap Verdier.poincareMap
  exact inferInstanceAs (IsIso (_ ≫ verdierExchange _ ℓ k p (𝟙_ _) (𝟙_ _)))

end AlgebraicGeometry.ProEtale.CondensedRing
