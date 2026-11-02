/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.AffineSpace

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

/-!
# Relative affine-line low-degree calculation

Source: Stacks Project, Etale Cohomology, Tags 0EYU, 03Q9 and 03PL; the
"Reduction to a geometric fibre" and "Degrees 0 and 1" paragraphs of the blueprint
proof `sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/det-prop-a1-kummer`
(blueprint: lem-pur-relative-line-low-degree-general).
-/


namespace AlgebraicGeometry.Etale

/-- Relative affine-line and punctured-line low-degree calculation.

Source: Stacks Project, Etale Cohomology, Tags 0EYU, 03Q9 and 03PL; the
"Reduction to a geometric fibre" and "Degrees 0 and 1" paragraphs of the blueprint
proof `det-prop-a1-kummer` (blueprint: lem-pur-relative-line-low-degree-general).

The coefficient sheaf is the finite Tate line `μ_(ℓ^N) ⊗ Λ`, represented by
`finiteEtaleTateSheaf` in degree one.  The open immersion `j` is required to
have the complement of the zero section as its range, so it is the relative
multiplicative group.  The two displayed isomorphisms are the actual
adjunction units; the last equality says that restriction is the identity
when those units are used to identify both direct images with the base sheaf.

Proof plan (the node's proof):
1. Pass to underlying abelian sheaves (forgetful comparisons). `p` and `π` are affine,
   hence qcqs; by the strict-local stalk formula (Tag 03Q9) at `S = Spec O^sh_{Y,ȳ}`
   the claims reduce to `H⁰(𝔸¹_S, L) = L_ȳ`, `H¹(𝔸¹_S, L) = 0`, `H⁰(𝔾_{m,S}, L) = L_ȳ`
   via the unit maps; geometric stalks detect isomorphisms.
2. `O^sh` is strictly henselian; factor `k → F → O^sh` with `F` separably closed.
   `L_S` is pulled back from `Spec F`, hence constant `B`, a finite `ℓ`-group.
3. Over an algebraic closure `Ω` of `F`, `𝔸¹_Ω` and `𝔾_{m,Ω}` are connected, so
   `H⁰(C, B) = B` by constant sections, compatibly with restriction.
4. Using a primitive `ℓ`-th root of unity, `Z/ℓ ≅ μ_ℓ`, and the Kummer root-line
   computation gives `H¹(𝔸¹_Ω, Z/ℓ) = 0`.
5. Finite-torsion extension induction (exact constant sheaves, enough injectives,
   long exact sequence) gives `H¹(𝔸¹_Ω, B) = 0`.
6. `Ω/F` is purely inseparable, so `C_Ω → C_F` is a universal homeomorphism;
   topological invariance transfers steps 3-5 to `F`.
7. Rotated smooth base change (Tag 0EYU) for `C_F → Spec F` smooth and `S → Spec F`
   affine, with strictly henselian constant cohomology of `S`, gives
   `B_{C_F}[0] ≅ Rh_* B_{C_S}` via the unit.
8. Derived global sections and the Leray identification (Tags 01EZ, 01F9) give
   `H⁰(C_S, B) = B` for both curves and `H¹(𝔸¹_S, B) = 0`, by constant sections.
9. Conservativity of geometric stalks gives the three sheaf assertions; since
   `j ≫ p = π`, pullback of sections along `X_V → V` followed by restriction to `U_V`
   is the `π`-unit, so the restriction is the identity under the units.
-/
theorem relativeLineLowDegreeGeneral
    (k : Type u) [Field k] (ell : ℕ) (hell : ell.Prime)
    (hellk : IsUnit (ell : k)) (N : ℕ) (hN : 1 ≤ N)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ((ell ^ N : ℕ) : Λ) = 0)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (G : Scheme.{u})
    (j : G ⟶ AffineSpace (ULift.{u} (Fin 1)) Y)
    [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ) :
    let m : ℕ := ell ^ N
    let p : AffineSpace (ULift.{u} (Fin 1)) Y ⟶ Y :=
      (AffineSpace.over (ULift.{u} (Fin 1)) Y).hom
    let π : G ⟶ Y := j ≫ p
    let LY : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      Scheme.finiteEtaleTateSheaf Λ m Y hΛ 1
    let LX : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
        (ModuleCat.{u + 1} Λ) :=
      (Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj LY
    let LU : Sheaf G.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      (Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj LX
    let restriction :
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).obj LX ⟶
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) π).obj LU :=
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).map
          ((Etale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) j).unit.app LX) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) j p π
          (by rfl)).hom.app LU
    let H1p :=
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (1 : ℤ)).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj LX))
    ∃ e₀ : LY ≅ (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).obj LX,
      ∃ eπ : LY ≅ (Etale.lowerStar (ModuleCat.{u + 1} Λ) π).obj LU,
        e₀.hom = (Etale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) p).unit.app LY ∧
        eπ.hom = (Etale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) p).unit.app LY ≫ restriction ∧
        IsZero H1p ∧
        e₀.hom ≫ restriction ≫ eπ.inv = 𝟙 LY := by
  sorry

end AlgebraicGeometry.Etale
