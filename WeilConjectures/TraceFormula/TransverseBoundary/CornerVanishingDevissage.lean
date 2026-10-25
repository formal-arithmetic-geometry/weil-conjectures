/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ForgetCohomologyVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.StrictLocalizationVanishing
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Forget
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerConnected
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerVanishingConstant
public import WeilConjectures.TraceFormula.TransverseBoundary.MonodromyDevissage
public import WeilConjectures.TraceFormula.TransverseBoundary.MonodromyPullback

/-!
# Vanishing at the transverse corner, assuming the constant case

Let `S` be the strict localization of the surface of a transverse corner at a geometric point
`z̄` (with algebraically closed field), `i' : S - (X_S ∪ Y_S) ⟶ S - Y_S` and
`p' : S - (X_S ∪ Y_S) ⟶ Z - (X ∪ Y)`. Assuming that the restriction maps
`H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` are bijective (blueprint
`det-tf-transverse-corner-constant`), this file proves that `(Rj_* i_! E)_z̄ = 0` for every
bounded `E` with finite `ℓ`-group monodromy (blueprint `det-tf-transverse-corner-vanishing`):

* *constant coefficients*: `RΓ(S - Y_S, i'_! N) = 0` for a finite `Λ`-module `N` killed by `ℓ`,
  as an abelian sheaf a finite sum of copies of `ℤ/ℓ`;
* *dévissage* on the connected `S - (X_S ∪ Y_S)`
  (`AlgebraicGeometry.Etale.prop_singleFunctor_of_hasFiniteEllGroupMonodromy`) gives
  `RΓ(S - Y_S, i'_! p'^* H) = 0` for every sheaf `H` with finite `ℓ`-group monodromy;
* *stalk formula*: `(R^q j_* i_! H)_z̄ = H^q(S - Y_S, (i_! H)|) = H^q(S - Y_S, i'_! p'^* H)`
  (`AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_rightDerivedLowerStar_of_subsingleton_sheafH`
  and base change of the extension by zero);
* *dévissage* of the bounded complex `E` by truncation.

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.isZero_leftDerivedUpperStar_boundaryComplex_of_bijective`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] (C : TransverseCorner k) {ℓ : ℕ} [Fact ℓ.Prime]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (zbar : Spec (.of Ω) ⟶ C.Z)

/-- The property of `K ∈ D(S - (X_S ∪ Y_S), Λ)` that `RΓ(S - Y_S, i'_! K) = 0`, to which the
dévissage is applied (blueprint `det-tf-transverse-corner-vanishing`). -/
def IsAcyclicExtension :
    ObjectProperty (DerivedCategory
      (Sheaf (C.strictLocalizationComplement zbar).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ IsZero ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
    (pullback C.j (strictLocalizationToBase zbar))).obj
      ((D((C.strictLocalizationComplementι zbar)_!open[ModuleCat.{u + 1} Λ])).obj K))

instance : (C.IsAcyclicExtension Λ zbar).IsClosedUnderIsomorphisms := by
  sorry

/-- `IsAcyclicExtension` is stable under shifts. -/
lemma isAcyclicExtension_shift
    (K : DerivedCategory
      (Sheaf (C.strictLocalizationComplement zbar).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (hK : C.IsAcyclicExtension Λ zbar K) : C.IsAcyclicExtension Λ zbar (K⟦n⟧) := by
  sorry

/-- `IsAcyclicExtension` is stable under extensions. -/
lemma isAcyclicExtension_ext (T : Pretriangulated.Triangle (DerivedCategory
      (Sheaf (C.strictLocalizationComplement zbar).smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _) (h₁ : C.IsAcyclicExtension Λ zbar T.obj₁)
    (h₃ : C.IsAcyclicExtension Λ zbar T.obj₃) : C.IsAcyclicExtension Λ zbar T.obj₂ := by
  sorry

/-- Constant coefficients (blueprint `det-tf-transverse-corner-vanishing`): if the restriction
maps `H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` are bijective, then `RΓ(S - Y_S, i'_! N) = 0` for
every finite `Λ`-module `N` killed by `ℓ`. -/
lemma isAcyclicExtension_constantSheaf
    (hbij : ∀ q : ℕ, Function.Bijective (Etale.cohomologyMap
      (pullback.snd (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase zbar)))
      ((pullback C.j (strictLocalizationToBase zbar)).constantZMod ℓ) q))
    (N : ModuleCat.{u + 1} Λ) (hN : Finite N) (hℓN : ∀ n : N, (ℓ : Λ) • n = 0) :
    C.IsAcyclicExtension Λ zbar ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (C.strictLocalizationComplement zbar).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj N)) := by
  sorry

/-- Sheaves (blueprint `det-tf-transverse-corner-vanishing`): for a sheaf `H` on `Z - (X ∪ Y)`
with finite `ℓ`-group monodromy, the stalk at `z̄` of `Rj_* i_! H` vanishes. -/
lemma isZero_leftDerivedUpperStar_rightDerivedLowerStar_singleFunctor
    (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    (hbij : ∀ q : ℕ, Function.Bijective (Etale.cohomologyMap
      (pullback.snd (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase zbar)))
      ((pullback C.j (strictLocalizationToBase zbar)).constantZMod ℓ) q))
    (H : Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : Etale.HasFiniteEllGroupMonodromy ℓ H) :
    IsZero ((L((zbar)^*[ModuleCat.{u + 1} Λ])).obj ((R((C.j)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((C.i)_!open[ModuleCat.{u + 1} Λ].obj H)))) := by
  sorry

/-- Blueprint `det-tf-transverse-corner-vanishing`, assuming `det-tf-transverse-corner-constant`
in the form of the bijectivity of the restriction maps
`H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)`: for a geometric point `z̄` with algebraically closed
field, the stalk at `z̄` of `M = Rj_* i_! E` vanishes for every bounded `E` with finite `ℓ`-group
monodromy. -/
theorem isZero_leftDerivedUpperStar_boundaryComplex_of_bijective
    (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    (hbij : ∀ q : ℕ, Function.Bijective (Etale.cohomologyMap
      (pullback.snd (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase zbar)))
      ((pullback C.j (strictLocalizationToBase zbar)).constantZMod ℓ) q))
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : Etale.IsBoundedFiniteEllGroupMonodromy ℓ E) :
    IsZero ((L((zbar)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E)) := by
  sorry

end AlgebraicGeometry.Scheme.TransverseCorner
