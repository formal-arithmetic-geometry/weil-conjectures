/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.TraceFormula.CurveLocal.BlowupRestriction
public import WeilConjectures.TraceFormula.CurveLocal.Model

/-!

# Prime-to-`ℓ` covers separating the graph and the diagonal

This file states the covering step of the proof of blueprint `sk-lem-tf-curve-restriction-zero`
(`det-tf-restriction-zero-covers`, together with the identification of
`det-tf-restriction-zero-localization` (i) pulled back to the cover).

In the strictly local model `T` of a `CurveLocalModel` (with the graph `G`, the diagonal `B`, the
vertical axis `V` and the horizontal axis `H = X × {y}`), let `L, K ∈ D^b_{ctf}(X, Λ)` with
`K_ȳ = 0` and `P = (L ⊠ K)|_T`. There are finite covers `X' ⟶ X`, `Y' ⟶ Y` of the two strictly
local traits by strictly local regular traits, of the same degree `d` prime to `ℓ` and generically
étale, such that, with `T'` the localization of `X' × Y'` at its closed point and `G', V', H', B'`
the reduced inverse images:

1. **(i)** the pullbacks `N', Q'` of `N = L|_{X ∖ y}` and `Q = K|_{Y ∖ y}` admit bounded finite
   projective lisse models whose termwise monodromy factors through finite `ℓ`-groups;
2. **(ii)** `T'` is a strictly local smooth surface, finite flat of rank `d²` over `T` and étale
   away from `H ∪ V`; in particular `B' ∖ y' ⟶ B ∖ y` is finite étale of degree `d²`;
3. **(iii)** the support of the tangent cone of `G' ∪ V'` meets neither that of `B'` nor that of
   `H'` outside the origin.

Since `K_ȳ = 0`, `K = j_{Y!} Q`, and `P` restricted to `T ∖ (G ∪ V)` is the extension by zero of
`(N ⊠ Q)|_{T ∖ (G ∪ V ∪ H)}` (`det-tf-restriction-zero-localization` (i)); its pullback to
`T' ∖ (G' ∪ V')` is the extension by zero of `E' = (N' ⊠ Q')|_{T' ∖ (G' ∪ V' ∪ H')}`, whose
cohomology sheaves have finite `ℓ`-group monodromy by (i). The statement
`AlgebraicGeometry.Etale.CurveLocalModel.exists_restrictionZeroCover` records exactly the data
used in the proof of `sk-lem-tf-curve-restriction-zero`: the strictly local smooth surface `T'`
with the curves `D' = G' ∪ V'`, `H'`, `B'` satisfying the hypotheses of
`sk-lem-tf-blowup-restriction`, the finite étale map `B' ∖ y' ⟶ B ∖ y` of degree prime to `ℓ`
compatible with the punctured diagonals, and the identification of the pullback of `P` to
`T' ∖ D'` with `i'_! E'`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

/-- **Prime-to-`ℓ` covers separating the graph and the diagonal** (blueprint
`det-tf-restriction-zero-covers`, with the identification of
`det-tf-restriction-zero-localization` (i) pulled back to the cover). Let `ℓ` be a prime
invertible in `k`, `Λ` a finite commutative `ℓ`-primary ring, `L, K ∈ D^b_{ctf}(X, Λ)` with
`K_ȳ = 0`, `P = (L ⊠ K)|_T` on the strictly local model `T`, and `ψ : B ∖ Y ⟶ T ∖ (G ∪ V)` the
inclusion of the punctured diagonal. Then there are: the strict localization `T'` of a smooth
surface `S'` at a `k`-point, a morphism `π : T' ⟶ T`, closed curves `D' = G' ∪ V'`, `H'`, `B'` of
`T'` satisfying the hypotheses of `sk-lem-tf-blowup-restriction` (`H'` regular, `D'`, `B'`
reduced curves, `C_t D' ∩ C_t B' = {0}`, `C_t D' ∩ T_t H' = {0}`), with
`T' ∖ D' ⊆ π⁻¹(T ∖ (G ∪ V))`, a finite étale map `B' ∖ y' ⟶ B ∖ Y` all of whose geometric
fibres have `d` points (`d` prime to `ℓ`) compatible with `ψ`, and a bounded complex `E'` on
`T' ∖ (D' ∪ H')` with finite locally constant cohomology and finite `ℓ`-group monodromy whose
extension by zero to `T' ∖ D'` is the pullback of `P`. -/
theorem exists_restrictionZeroCover (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.boundedConstructibleFiniteTor Λ M.X L)
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ M.X K)
    (hKy : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (P : DerivedCategory (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K))
    (ψ : M.yB.openComplement.toScheme ⟶ M.O.toScheme)
    (hψ : ψ ≫ M.O.ι = M.yB.openComplement.ι ≫ M.b) :
    ∃ (S' : Scheme.{u}) (aS' : S' ⟶ Spec (.of k)) (_ : SmoothOfRelativeDimension 2 aS')
      (s' : Spec (.of k) ⟶ S') (_ : s' ≫ aS' = 𝟙 _) (π : strictLocalization s' ⟶ M.T)
      (D' H' B' : Scheme.{u}) (dD' : D' ⟶ strictLocalization s')
      (dH' : H' ⟶ strictLocalization s') (dB' : B' ⟶ strictLocalization s')
      (_ : IsClosedImmersion dD') (_ : IsClosedImmersion dH') (_ : IsClosedImmersion dB')
      (_ : Nonempty D') (_ : Nonempty H') (_ : Nonempty B')
      (_ : ∃ _ : IsDomain Γ(H', ⊤), IsDiscreteValuationRing Γ(H', ⊤))
      (_ : IsReduced D' ∧ ringKrullDim Γ(D', ⊤) = 1)
      (_ : IsReduced B' ∧ ringKrullDim Γ(B', ⊤) = 1)
      (_ : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s') (specIdeal dD')
        (specIdeal dB'))
      (_ : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s') (specIdeal dD')
        (specIdeal dH'))
      (_ : dD'.openComplement ≤ π ⁻¹ᵁ M.O)
      (πU : (dB' ⁻¹ᵁ dD'.openComplement).toScheme ⟶ M.yB.openComplement.toScheme)
      (_ : IsFinite πU) (_ : Etale πU) (d : ℕ)
      (_ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ M.yB.openComplement.toScheme),
        Nat.card (πU.GeometricFiber s) = d)
      (_ : IsUnit (d : Λ))
      (_ : πU ≫ ψ ≫ M.O.ι =
        dB'.resLE dD'.openComplement (dB' ⁻¹ᵁ dD'.openComplement) le_rfl ≫
          dD'.openComplement.ι ≫ π)
      (E' : DerivedCategory (Sheaf (dD'.openComplement ⊓ dH'.openComplement).toScheme.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)))
      (_ : (∃ a b : ℤ, E'.IsGE a ∧ E'.IsLE b) ∧ ∀ n : ℤ,
        ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G)
          (c : Scheme.GaloisCover G (dD'.openComplement ⊓ dH'.openComplement).toScheme)
          (N : ModuleCat.{u + 1} Λ) (_ : Finite N),
          Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj
              ((DerivedCategory.homologyFunctor _ n).obj E') ≅
            (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)),
      Nonempty ((dD'.openComplement.ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj
          ((π)^*[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj P) ≅
        ((strictLocalization s').homOfLE (inf_le_left :
          dD'.openComplement ⊓ dH'.openComplement ≤ dD'.openComplement))_!open[ModuleCat.{u + 1} Λ]
          |>.mapDerivedCategory.obj E') :=
  sorry

end AlgebraicGeometry.Etale.CurveLocalModel
