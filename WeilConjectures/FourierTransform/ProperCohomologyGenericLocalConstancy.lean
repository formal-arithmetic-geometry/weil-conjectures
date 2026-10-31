/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Proper

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-!
# Generic local constancy of proper étale cohomology

Source: Stacks Project, `more-etale.tex`, Tag 0GL0 (theorem-constructible-shriek),
generic-stratum consequence for a proper morphism over an integral affine Noetherian base,
with Tags 0GKY and 0GKZ for its proof, and `etale-cohomology.tex`, Tag 03RW, for finite
locally constant constructible sheaves
(blueprint: lem-fd-proper-cohomology-generic-local-constancy).

For a proper morphism `f : X ⟶ S` to an integral affine Noetherian scheme, a constructible
sheaf `F` of modules over a finite field `A` of characteristic `ℓ` and `q ≥ 0`, some nonempty
open of `S` carries `R^q f_* F` as a finite locally constant sheaf. No invertibility of `ℓ`
is assumed.
-/

/-- **Generic local constancy of one proper higher direct image.** Source: Stacks Project,
`more-etale.tex`, Tag 0GL0 (identity open compactification), with `etale-cohomology.tex`,
Tag 03RW (blueprint: lem-fd-proper-cohomology-generic-local-constancy).

Let `A` be a finite field of characteristic the prime `ℓ`, `S` an integral affine Noetherian
scheme, `f : X ⟶ S` proper, `F` a constructible sheaf of `A`-modules on `X_ét` and `q ≥ 0`.
Then there is a nonempty open immersion `j : U ⟶ S` such that `j^{-1} R^q f_* F`, with
`R^q f_* F = H^q(Rf_*(F[0]))`, is finite locally constant. No invertibility of `ℓ` is assumed.

Proof (blueprint steps):
1. For a compactification `(j, p)`, exact extension by zero and the right derived direct image
   make `Rp_* j_!` additive and triangulated; it preserves lower cohomological bounds, and
   complexes with constructible cohomology form a triangulated subcategory (Serre class).
2. Over an affine base `Y` of finite type over `ℤ` and an affine open `W` of `𝔸¹_Y` with a
   finite locally constant `L`, the finite-étale filtration theorem gives a finite étale
   `g : T → W` of degree prime to `ℓ`; the trace identity makes `L` a retract of `g_* g^* L`,
   and finite direct image is exact.
3. The pieces `T_a → Y` are smooth affine curves; the constant smooth-affine-curve result
   (Tag 0GKX, no invertibility), finite-filtration dévissage, disjoint-open extension and
   compact-support composition give constructibility over `W`.
4. An arbitrary open of `𝔸¹_Y` is handled by a finite affine cover, relative Mayer–Vietoris
   and Serre closure, inducting on the cover size.
5. For constructible `F` on `𝔸¹_Y`, a dense lisse open with finite closed complement, the
   open–closed triangle and quasi-finite shriek constructibility give the result.
6. Noetherian induction on closed subsets of `Y` (reduced induced structures, exact inverse
   image, compact-support base change) gives constructibility over all of `Y`.
7. An arbitrary affine `Y = Spec R` is the limit over finitely generated `ℤ`-subalgebras;
   constructible-module limit descent gives the same conclusion.
8. Truncation and bounded dévissage upgrade the result to bounded-below complexes with
   constructible cohomology, and induction on dimension gives it for affine space.
9. An affine open `W ⊆ X` is a finite-presentation closed subscheme of `𝔸ⁿ_S`; closed
   immersion, quasi-finite shriek and composition give constructibility on `W`.
10. A finite affine cover of the quasi-compact `X`, with affine intersections, Mayer–Vietoris
    and induction on the cover size, give constructibility of `R^q f_* F`.
11. The identity compactification identifies `Rf_!` with `Rf_*`; generic constancy of the
    constructible `R^q f_* F` gives a dense open on which it is finite locally constant, and
    a dense open of the integral (hence nonempty, irreducible) `S` is nonempty. -/
theorem proper_cohomology_generic_local_constancy
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type (u + 1)) [Field A] [Finite A] [CharP A ℓ]
    (S : Scheme.{u}) [IsAffine S] [IsIntegral S] [IsLocallyNoetherian S]
    (X : Scheme.{u}) (f : X ⟶ S) [IsProper f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (q : ℤ) (hq : 0 ≤ q) :
    ∃ (U : Scheme.{u}) (j : U ⟶ S),
      Nonempty U ∧ IsOpenImmersion j ∧
        Scheme.IsFiniteLocallyConstantSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} A) j).obj
            ((DerivedCategory.Plus.homologyFunctor
                (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
              ((Etale.rightDerivedLowerStarPlus
                  (ModuleCat.{u + 1} A) f).obj
                ((DerivedCategory.Plus.singleFunctor
                    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F)))) := by
  sorry

end AlgebraicGeometry
