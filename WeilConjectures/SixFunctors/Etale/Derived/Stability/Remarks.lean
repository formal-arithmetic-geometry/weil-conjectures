/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.CtfStability

/-!
# Remarks on the preservation theorem

This file collects complements to the preservation theorem for constructible complexes of finite
Tor amplitude (`AlgebraicGeometry.Etale.constructibleFiniteTor_stability`). Each is a theorem
bundling the statements it points to:

- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_leftDerivedUpperStar_of_derivedComplete`:
  the integral form of the pullback clause;
- `AlgebraicGeometry.Etale.reductionModIdeal_constantComplex_and_exists_normalizedTower`: the
  constant coefficient tower;
- `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar_proofStatus`: the
  direct-image clause on the two sites;
- `AlgebraicGeometry.Etale.coefficientTransport_status`: the proved coefficient transport and its
  domains;
- `AlgebraicGeometry.Etale.NormalizedTower.reconstruction_and_integral_comparisons`: the
  normalized DVR reconstruction and the integral comparisons;
- `AlgebraicGeometry.Etale.exceptionalInverseImage_coefficientStages`,
  `AlgebraicGeometry.Etale.exceptionalAdjoint_admissibility_constructible`,
  `AlgebraicGeometry.Etale.exceptionalAdjoint_traceAdmissibility_coefficients`: the exceptional
  inverse image at the finite and integral stages;
- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.ctfDescent`: the verified domains entering
  the six-functor datum;
- `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_scope`: the sharp internal-Hom bound holds
  for a site-perfect first variable and fails in general.

The tower shapes that occur are described by
`AlgebraicGeometry.Etale.exists_normalizedTower_and_boundedConstructibleIntegral_iff`.

## Implementation details

The coefficient stages `E` and `ℚ̄_ℓ`, and the finite-stage comparisons for the direct image, the
internal hom, Verdier biduality and the exceptional inverse image (beyond the formula
`Rf^! = 𝔻_X f^* 𝔻_Y`) are not formalised; the remarks are stated with the finite and integral
stages that are.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section Integral

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

/-- The ideal `Iⁿ` of `I = (ϖ)` is principal. -/
lemma isPrincipal_pow_of_eq_span {ϖ : Λ} (hI : I = Ideal.span {ϖ}) (n : ℕ) :
    (I ^ n).IsPrincipal := by
  rw [hI, Ideal.span_singleton_pow]
  exact ⟨⟨_, rfl⟩⟩

/-- **Pullback at the integral stage.** If the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` of `K` are bounded
constructible of Tor amplitude in `[a, b]`, then so are the reductions of `Lf^* K`. Hence, as soon
as `Lf^* K` is derived complete, `Lf^*` carries `Dᵇc(Y, Λ)` into `Dᵇc(X, Λ)`, with the same
interval. -/
theorem boundedConstructibleIntegral_leftDerivedUpperStar_of_derivedComplete {X Y : Scheme.{u}}
    (f : X ⟶ Y) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : ∀ n : ℕ, boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K)) :
    (∀ n : ℕ, boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))) ∧
    (DerivedCategory.derivedComplete X.smallEtaleTopology I
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) →
      DerivedCategory.boundedConstructibleIntegral I X
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  have h (n : ℕ) : boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
    obtain ⟨e⟩ := nonempty_iso_reductionModIdeal_leftDerivedUpperStar Λ f (I ^ (n + 1))
    exact ⟨(boundedConstructible _ X).prop_of_iso (e.app K)
        (boundedConstructible_leftDerivedUpperStar _ f (hK n).1),
      (torAmplitudeIn _ X a b).prop_of_iso (e.app K)
        (torAmplitudeIn_leftDerivedUpperStar _ f a b (hK n).2)⟩
  exact ⟨h, fun hc ↦ ⟨hc, a, b, h⟩⟩

/-- **The trivial coefficient case.** The reduction `Λ_X ⊗ᴸ (Λ ⧸ J)_X` of the constant complex
`Λ_X` is the constant sheaf `(Λ ⧸ J)_X` placed in degree `0`, for every ideal `J`. More generally,
for any complex `L` on `X` with derived reductions `L_n = L ⊗ᴸ_Λ Λ ⧸ Iⁿ⁺¹`, the `L_n` form a
normalized tower. -/
theorem reductionModIdeal_constantComplex_and_exists_normalizedTower (X : Scheme.{u}) :
    (∀ J : Ideal Λ, Nonempty ((reductionModIdeal Λ X J).obj (constantComplex Λ X) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Λ ⧸ J))))) ∧
    ∀ (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (Ln : ∀ n : ℕ,
        _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n + 1)))))
      (η : ∀ n : ℕ, L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ (n + 1))) X).obj (Ln n)),
      (∀ n : ℕ, IsDerivedBaseChange (η n)) → ∃ M : NormalizedTower I X, M.obj = Ln :=
  ⟨fun _ ↦ ⟨λ_ _⟩,
    (exists_normalizedTower_and_boundedConstructibleIntegral_iff (I := I) (X := X)).1⟩

end Integral

section IntegralStage

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
  [HasCompactification aX] [HasCompactification aY]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
  (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
  [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

include hϖ hI hf in
/-- Proved coefficient transport and its domains.

At the integral stage (`Λ` a Noetherian domain complete for `I = (ϖ)`, `Λ ⧸ I` finite of
exponent invertible on `k`), for a separated finite-type `f : X ⟶ Y` of separated finite-type
`k`-schemes, the reductions `K ↦ K ⊗ᴸ Λ ⧸ Iⁿ` commute

* with pullback and tensor product
  (`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_leftDerivedUpperStar`), with the
  ordinary and the compactly supported direct image
  (`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isPrincipal`);
* with the internal Hom, for arbitrary first variables, with the finite internal Hom of the
  reductions;
* with the exceptional inverse image;

and a normalized DVR tower reconstructs with its stated reductions. -/
theorem coefficientTransport_status :
    (∀ n : ℕ, Nonempty (reductionModIdeal Λ Y (I ^ n) ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ X (I ^ n))) ∧
    (∀ (n : ℕ) (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      Nonempty ((reductionModIdeal Λ X (I ^ n)).obj
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) ≅
        ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj ((reductionModIdeal Λ X (I ^ n)).obj M))) ∧
    (∀ n : ℕ, Nonempty (R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ Y (I ^ n) ≅
      reductionModIdeal Λ X (I ^ n) ⋙ R((f)_*[ModuleCat.{u + 1} Λ]))) ∧
    (∀ n : ℕ, Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y (I ^ n) ≅
      reductionModIdeal Λ X (I ^ n) ⋙ R(f)_![ModuleCat.{u + 1} Λ])) ∧
    (∀ (n : ℕ) (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (Kn Ln : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n))))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn)
      (η' : L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Ln),
      IsDerivedBaseChange η → IsDerivedBaseChange η' →
        Nonempty ((reductionModIdeal Λ X (I ^ n)).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L) ≅
          (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
            (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X).obj (op Kn)).obj Ln))) ∧
    (∀ (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℕ),
        Nonempty ((reductionModIdeal Λ X (I ^ n)).obj
            ((R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L) ≅
          (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
            ((reductionModIdeal Λ Y (I ^ n)).obj L))) ∧
    ∀ (M : NormalizedTower I X) (c : Cone M.restrict), Pretriangulated.IsHomotopyLimit c →
      (∀ n : ℕ, IsDerivedBaseChange (φ := Ideal.Quotient.mk (I ^ (n + 1))) (c.π.app (op n))) ∧
        DerivedCategory.derivedComplete X.smallEtaleTopology I c.pt := by
  obtain ⟨-, hhom, -, -, -, -, heff⟩ := preservationMatrix_integral I hϖ hI aX aY f hf
  refine ⟨fun n ↦ nonempty_iso_reductionModIdeal_leftDerivedUpperStar Λ f (I ^ n),
    fun n K M ↦ ⟨α_ K M _⟩,
    fun n ↦ nonempty_iso_reductionModIdeal_rightDerivedLowerStar Λ f _
      (isPrincipal_pow_of_eq_span I hI n),
    fun n ↦ nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isPrincipal Λ f _
      (isPrincipal_pow_of_eq_span I hI n), hhom, fun L n ↦ ?_, heff⟩
  have := isTriangulated_rightDerivedUpperShriek (Λ := Λ) f
  subst hI
  obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint hϖ n L
  exact ⟨e.symm⟩

include hϖ hI hf in
/-- **Normalized DVR reconstruction and integral comparisons.** Every normalized DVR tower `M_n`
reconstructs: the canonical maps from its derived limit `R lim_n Res M_n` exhibit each `M_n` as
the reduction of the limit, which is derived complete. The integral internal Hom has the finite
internal Homs of the reductions as its reductions, and the integral exceptional
adjoint `G_f L` (the derived limit of the finite exceptional inverse images) is an object of
`Dᵇc(X, Λ)` identified with `Rf^! L` compatibly with the maps to the `Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)`. -/
theorem NormalizedTower.reconstruction_and_integral_comparisons :
    (∀ (M : NormalizedTower I X) (c : Cone M.restrict), Pretriangulated.IsHomotopyLimit c →
      (∀ n : ℕ, IsDerivedBaseChange (φ := Ideal.Quotient.mk (I ^ (n + 1))) (c.π.app (op n))) ∧
        DerivedCategory.derivedComplete X.smallEtaleTopology I c.pt) ∧
    (∀ (n : ℕ) (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (Kn Ln : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n))))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Kn)
      (η' : L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj Ln),
      IsDerivedBaseChange η → IsDerivedBaseChange η' →
        Nonempty ((reductionModIdeal Λ X (I ^ n)).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L) ≅
          (derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
            (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X).obj (op Kn)).obj Ln))) ∧
    ∀ L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.boundedConstructibleIntegral I Y L →
      ∀ c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint), Pretriangulated.IsHomotopyLimit c →
        DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
          ∃ e : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L ≅ c.pt, ∀ n : ℕ,
            e.hom ≫ c.π.app (op n) = (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.map
              ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n)) := by
  obtain ⟨-, hhom, -, -, hexc, -, heff⟩ := preservationMatrix_integral I hϖ hI aX aY f hf
  exact ⟨heff, hhom, fun L hL c hc ↦ ⟨(hexc L hL c hc).1, (hexc L hL c hc).2.1⟩⟩

include hϖ hI hf in
/-- **Admissibility on the constructible domains.** On the integral constructible categories the
exceptional adjoint is transported along the coefficient reductions: for `L ∈ Dᵇc(Y, Λ)` the
derived limit `G_f L` of the `Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)` lies in `Dᵇc(X, Λ)`, is `Rf^! L`, and has the
`Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)` as reductions. Moreover, every normalized DVR tower reconstructs from its
derived limit. -/
theorem exceptionalAdjoint_admissibility_constructible :
    (∀ L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.boundedConstructibleIntegral I Y L →
      ∀ c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint), Pretriangulated.IsHomotopyLimit c →
        DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
          (∃ e : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L ≅ c.pt, ∀ n : ℕ,
            e.hom ≫ c.π.app (op n) = (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.map
              ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n))) ∧
          ∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj c.pt ≅
            (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
              ((reductionModIdeal Λ Y (I ^ n)).obj L))) ∧
    ∀ (M : NormalizedTower I X) (c : Cone M.restrict), Pretriangulated.IsHomotopyLimit c →
      (∀ n : ℕ, IsDerivedBaseChange (φ := Ideal.Quotient.mk (I ^ (n + 1))) (c.π.app (op n))) ∧
        DerivedCategory.derivedComplete X.smallEtaleTopology I c.pt := by
  obtain ⟨-, -, -, -, hexc, -, heff⟩ := preservationMatrix_integral I hϖ hI aX aY f hf
  exact ⟨hexc, heff⟩

include hϖ hI hf in
/-- **Coefficient clauses in trace admissibility.** The coefficient comparisons used by the trace
admissibility hypothesis on the integral constructible categories: the compactly supported direct
image commutes with the reductions `K ↦ K ⊗ᴸ Λ ⧸ Iⁿ`, and the integral exceptional adjoint `G_f L`
of `L ∈ Dᵇc(Y, Λ)` lies in `Dᵇc(X, Λ)`, is identified with `Rf^! L` compatibly with the maps to
the `Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)` (so that the units and counits of `Rf_! ⊣ Rf^!` are transported), and has
these as reductions. -/
theorem exceptionalAdjoint_traceAdmissibility_coefficients :
    (∀ n : ℕ, Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y (I ^ n) ≅
      reductionModIdeal Λ X (I ^ n) ⋙ R(f)_![ModuleCat.{u + 1} Λ])) ∧
    ∀ L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.boundedConstructibleIntegral I Y L →
      ∀ c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint), Pretriangulated.IsHomotopyLimit c →
        DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
          (∃ e : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L ≅ c.pt, ∀ n : ℕ,
            e.hom ≫ c.π.app (op n) = (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.map
              ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n))) ∧
          ∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj c.pt ≅
            (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
              ((reductionModIdeal Λ Y (I ^ n)).obj L)) :=
  ⟨fun n ↦ nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isPrincipal Λ f _
      (isPrincipal_pow_of_eq_span I hI n),
    (exceptionalAdjoint_admissibility_constructible I hϖ hI aX aY f hf).1⟩

end IntegralStage

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
  (f : X ⟶ Y) (hf : f ≫ aY = aX)

include hf in
/-- **The direct image on both sites.** For `k` algebraically closed, a finite `Λ` whose exponent
is invertible on `k` and a separated morphism `f : X ⟶ Y` of finite-type `k`-schemes with
`dim X ≤ d`:

* on the small étale site, `Rf_*` preserves `Dctf` and sends a bounded constructible complex of
  Tor amplitude `[a, b]` to one of Tor amplitude `[a, b + 2d]`;
* on the small pro-étale site, `Rf_*` sends a bounded constructible complex of Tor amplitude
  `[a, b]` to a bounded constructible complex of Tor amplitude `[a, b + 2d]`. -/
theorem constructibleFiniteTor_rightDerivedLowerStar_proofStatus [IsAlgClosed k] [IsSeparated aX]
    [HasCompactification aX] [IsSeparated aY] [HasCompactification aY] [QuasiCompact f]
    [HasCompactification f] :
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
            ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
    ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))),
      ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
              ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) ∧
            ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
              ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) := by
  obtain ⟨-, -, ⟨h₁, h₂⟩, -⟩ := constructibleFiniteTor_stability Λ aX aY f hf
  exact ⟨h₁, h₂, (torAmplitudeIn_preservation Λ aX aY f hf).2.2.1⟩

include hf in
/-- **Constructible exceptional inverse images, the finite stage.** For `k` algebraically closed,
a finite `Λ` whose exponent is invertible on `k` and a separated finite-type `f : X ⟶ Y` of
separated finite-type `k`-schemes, the exceptional inverse image carries `Dctf(Y, Λ)` into
`Dctf(X, Λ)`, it is `Rf^! ≅ 𝔻_X f^* 𝔻_Y` there, and it is right adjoint to `Rf_!` on the
constructible finite-Tor categories. -/
theorem exceptionalInverseImage_coefficientStages [IsAlgClosed k] [IsSeparated aX]
    [HasCompactification aX] [IsSeparated aY] [HasCompactification aY]
    [HasInvertibleExponent Λ Y] [QuasiCompact f] [HasCompactification f] :
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj K) ∧
          Nonempty ((R(f)^![Λ]).obj K ≅
            (verdierDual Λ aX).obj
              (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
                ((verdierDual Λ aY).obj (op K)))))) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
      DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f) :=
  ⟨fun _ hK ↦ ⟨constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hK,
      nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY f hf hK⟩,
    ⟨DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f⟩⟩

omit [HasInvertibleExponent Λ (Spec (.of k))] in
/-- **The verified domains of the six functors.** For a finite `Λ` whose exponent is invertible
on `Y` and a separated finite-type `f : X ⟶ Y` of finite-type `k`-schemes, the restrictions of
`Lf^*`, `Rf_*`, `Rf_!` and `Rf^!` to the constructible finite-Tor categories form adjunctions
`Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!` there, with the units and counits of the ambient adjunctions. -/
theorem DerivedCategoryFiniteTor.ctfDescent [HasInvertibleExponent Λ Y] [IsSeparated f]
    [QuasiCompact f] [HasCompactification f] :
    Nonempty (DerivedCategoryFiniteTor.leftDerivedUpperStar (ModuleCat.{u + 1} Λ) f ⊣
      DerivedCategoryFiniteTor.rightDerivedLowerStar Λ aX aY f hf) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
      DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f) :=
  ⟨⟨DerivedCategoryFiniteTor.leftDerivedUpperStarAdjunction Λ aX aY f hf⟩,
    ⟨DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f⟩⟩

include aX in
/-- **The dimension-free internal-Hom bound needs a site-perfect first variable.** For `X` of
finite type over an algebraically closed `k`, `dim X ≤ m`, and bounded constructible `K`, `M` of
Tor amplitude `[a, b]` and `[c, d]`, `RHom(K, M)` has Tor amplitude in `[c - b - 2m, d - a + 2m]`,
and in `[c - b, d - a]` when `K` is dualizable; but the interval `[c - b, d - a]` fails for
general constructible `K`. -/
theorem torAmplitudeIn_derivedHom_scope [IsAlgClosed k] [Nontrivial Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] :
    (∀ m : ℕ, topologicalKrullDim X ≤ (m : WithBot ℕ∞) → ∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    (∀ (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K → IsDualizable K →
          boundedConstructible (ModuleCat.{u + 1} Λ) X M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
                (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M)) ∧
    ¬ ∀ (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
      (a b c d : ℤ)
      (K M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      boundedConstructible (ModuleCat.{u + 1} Λ) Z K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b K →
          boundedConstructible (ModuleCat.{u + 1} Λ) Z M →
            torAmplitudeIn (ModuleCat.{u + 1} Λ) Z c d M →
              torAmplitudeIn (ModuleCat.{u + 1} Λ) Z (c - b) (d - a)
                (((RHom(Z)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  exact ⟨fun m hm a b c d K M hK hKt hM hMt ↦
      torAmplitudeIn_derivedHom Λ aX m hm a b c d hK hKt hM hMt,
    fun a b c d K M hK hKt hKd hM hMt ↦
      torAmplitudeIn_derivedHom_of_isDualizable Λ aX a b c d hK hKt hKd hM hMt,
    not_forall_torAmplitudeIn_derivedHom Λ⟩

end Finite

end Etale

end AlgebraicGeometry
