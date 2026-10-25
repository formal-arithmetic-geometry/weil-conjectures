/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitSmoothSurface
public import WeilConjectures.AlgebraicGeometry.RegularDivisor
public import WeilConjectures.ConstructibleSheaf.EllMonodromy
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!
# Restriction to a transverse punctured curve

Let `Z` be a smooth surface over an algebraically closed field `k` (or an étale limit of such),
`X, Y ⊆ Z` regular divisors meeting transversely at exactly one point `z`, `j : Z - Y ⟶ Z` and
`i : Z - (X ∪ Y) ⟶ Z - Y` the open immersions, and `E` a bounded complex of `Λ`-modules on
`Z - (X ∪ Y)` with finite `ℓ`-group monodromy, `Λ` a finite `ℓ`-primary ring. Put
`M = Rj_* i_! E`. The transverse boundary calculation (blueprint
`sk-lem-tf-transverse-boundary`, stated here as
`AlgebraicGeometry.Etale.transverseBoundary`) gives `M_z = 0` and, for `Y` connected, that the
restriction `RΓ(Y, M|_Y) ⟶ M_s` is zero at every closed point `s ≠ z` of `Y`.

From this we deduce (blueprint `sk-lem-tf-punctured-restriction`) that for a closed curve
`C ⊆ Z` with `C ∩ Y = {s}` the restriction map
```
RΓ(Z - Y, i_! E) ⟶ RΓ(C_(s) - s, (i_! E)|_{C_(s) - s})
```
to the punctured strict localization of `C` at `s` is zero. Following the blueprint
(`det-tf-punctured-restriction-factorization`), the restriction factors through the restriction
`RΓ(Y, M|_Y) ⟶ M_s` to the stalk at `s`; here the stalk `M_s` is computed on the strictly local
scheme `C_(s)` itself rather than on the strict localization of `Z`. In fact only this is used of
`C_(s) - s`: it maps to `Z - Y` through a strictly local scheme `S` over `Z` whose closed point
maps to `s` (`AlgebraicGeometry.Etale.globalSectionsRestriction_eq_zero_of_strictlyLocal`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime]
  {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
  {Z : Over (Spec (.of k))} {X Y : Scheme.{u}} {iX : X ⟶ Z.left} {iY : Y ⟶ Z.left}
  {UY UXY : Z.left.Opens}

/-- The complex `M = Rj_* i_! E` on `Z` of the transverse boundary calculation (blueprint
`sk-lem-tf-transverse-boundary`), for `j : Z - Y ⟶ Z` and `i : Z - (X ∪ Y) ⟶ Z - Y`. -/
noncomputable abbrev transverseBoundaryComplex (hXY : UXY ≤ UY)
    (E : DerivedCategory (Sheaf UXY.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory (Sheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ((UY.ι)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.obj
    (((Z.left.homOfLE hXY)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E)

/-- **Transverse boundary calculation** (blueprint `sk-lem-tf-transverse-boundary`).
Compatibility required from the subsection `sk-lem-tf-transverse-boundary` (to be proved there).

Let `Z` be a smooth surface over the algebraically closed field `k` of characteristic `≠ ℓ`, or
an étale limit with affine transition maps of such surfaces, and `X, Y` regular divisors meeting
transversely at exactly one point `z`, with open complements `Z - Y` (`UY`) and
`Z - (X ∪ Y)` (`UXY`), `j : Z - Y ⟶ Z` and `i : Z - (X ∪ Y) ⟶ Z - Y`. Let `Λ` be a finite
`ℓ`-primary ring and `E` a bounded complex of `Λ`-modules on `Z - (X ∪ Y)` with finite locally
constant cohomology whose monodromy factors through a finite `ℓ`-group. Put `M = Rj_* i_! E`.
Then
1. `M_z = 0`: the pullback of `M` to every geometric point over `z` vanishes;
2. `M|_{Y - z}` has finite locally constant cohomology;
3. if `Y` is connected, then for every closed point `s ≠ z` of `Y` and every geometric point
   `s̄` over `s`, the restriction map `RΓ(Y, M|_Y) ⟶ M_s = RΓ(s̄, s̄^* M|_Y)` is zero. -/
theorem transverseBoundary (hℓ : (ℓ : k) ≠ 0) (hΛ : IsNilpotent (ℓ : Λ))
    (hZ : IsEtaleLimitOfSmoothSurfaces Z) (hX : IsRegularDivisor iX) (hY : IsRegularDivisor iY)
    (z : Z.left) (hz : MeetTransverselyAt iX iY z)
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ)
    (hUXY : (UXY : Set Z.left) = (Set.range iX ∪ Set.range iY)ᶜ) (hle : UXY ≤ UY)
    (E : DerivedCategory (Sheaf UXY.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) :
    (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (z' : Spec (.of Ω) ⟶ Z.left),
      Set.range z' = {z} →
        IsZero (((z')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
          (transverseBoundaryComplex hle E))) ∧
    (∀ V : Y.Opens, (V : Set Y) = (iY ⁻¹' {z})ᶜ → ∀ n : ℤ,
      Scheme.IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj
        (((V.ι ≫ iY)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
          (transverseBoundaryComplex hle E)))) ∧
    (ConnectedSpace Y → ∀ (s : Y), IsClosed ({s} : Set Y) → iY s ≠ z →
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s' : Spec (.of Ω) ⟶ Y), Set.range s' = {s} →
        globalSectionsRestriction s' (((iY)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
          (transverseBoundaryComplex hle E)) = 0) :=
  sorry

end AlgebraicGeometry.Etale
