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

This file formalises the remarks of the blueprint subsection `sk-thm-sf-ctf-stability` that
accompany `thm-sf-ctf-stability` (`AlgebraicGeometry.Etale.constructibleFiniteTor_stability`).
Each remark with mathematical content is a theorem bundling the statements it points to:

- `AlgebraicGeometry.Etale.boundedConstructibleIntegral_leftDerivedUpperStar`
  (`rem-sf-tor-toolbox-stages`): the integral form of clause (i);
- `AlgebraicGeometry.Etale.reductionModIdeal_constantComplex_and_exists_normalizedTower`
  (`rem-sf-constant-tower-trivial-model`): the constant coefficient tower;
- `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar_proofStatus`
  (`rem-sf-direct-image-proof-status`): the two sites of clause (iii);
- `AlgebraicGeometry.Etale.coefficientTransport_status` (`rem-sf-clause-vii-status`);
- `AlgebraicGeometry.Etale.NormalizedTower.reconstruction_and_integral_comparisons`
  (`rem-sf-finite-level-comparison-ingredient`);
- `AlgebraicGeometry.Etale.exceptionalInverseImage_coefficientStages`
  (`rem-ptr-weil-exceptional-inverse-image-16`),
  `AlgebraicGeometry.Etale.exceptionalAdjoint_admissibility_constructible`
  (`rem-ptr-weil-exceptional-adjoint-admissibility-10`),
  `AlgebraicGeometry.Etale.exceptionalAdjoint_traceAdmissibility_coefficients`
  (`rem-ptr-trf-admissibility-14`);
- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.ctfDescent`
  (`rem-sf-ctf-descent`): the verified domains entering the six-functor datum;
- `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_scope` (`open-sf-preservation-gaps`): the
  sharp internal-Hom bound holds for a site-perfect first variable and fails in general.

The remark `rem-sf-tower-shapes-occurring` is
`AlgebraicGeometry.Etale.exists_normalizedTower_and_boundedConstructibleIntegral_iff`.

## Where this feeds (`rem-sf-feeds`, `sk-rem-sf-feeds`)

The package `prop-functor-package` is consumed as follows. The smooth-purity chapter needs
clause (7), the relative product theorem, as the relative input for its affine-line orientation
and its affine-space case. The duality chapter is re-based on clauses (3) and (6): its global
duality, pairing identification, derived duality, degreewise, proper, trace and
reciprocal-eigenvalue nodes are read off from `thm-sf-global-duality`, `thm-sf-identification`
and the pairing statements. The trace-formula and final chapters use clause (8) (stability,
perfectness of compact-support cohomology), the trace-layer statements
`prop-trf-compact-support-perfectness`, `lem-trf-open-ctf` and `thm-trf-internal-hom-pullback`,
and, outside the package, the Künneth–Verdier isomorphism `thm-trf-kunneth-verdier`, on which
their supported pairing and local-term nodes rest. This remark is editorial and has no Lean
counterpart.

## Implementation notes

The coefficient stages `E` and `ℚ̄_ℓ`, and the finite-stage comparisons
`lem-coef-finite-direct-image`, `thm-coef-finite-hom`, `cor-coef-finite-verdier`,
`lem-coef-finite-exceptional` (beyond the formula `Rf^! = 𝔻_X f^* 𝔻_Y`), `thm-coef-rational-verdier`,
`lem-coef-rational-operations` and `thm-coef-qbar-verdier` are not formalised; the remarks are
stated with the finite and integral stages that are.
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

/-- Blueprint `rem-sf-tor-toolbox-stages`: The four coefficient stages.

The integral form of clause (i) of `thm-sf-ctf-stability`: pullback commutes with the reductions
`K ↦ K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` (`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_leftDerivedUpperStar`,
`Lf^*` being monoidal and carrying the constant sheaf `Λ ⧸ Iⁿ⁺¹` to the constant sheaf), so the
finite-stage pullback statements give that the reductions of `Lf^* K` are bounded constructible
of Tor amplitude in the same interval as those of `K`. Hence, as soon as `Lf^* K` is derived
complete, `Lf^*` carries `Dᵇc(Y, Λ)` into `Dᵇc(X, Λ)`, with the same interval. -/
theorem boundedConstructibleIntegral_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : ∀ n : ℕ, boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K)) :
    (∀ n : ℕ, boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))) ∧
    (DerivedCategory.derivedComplete X.smallEtaleTopology I
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) →
      DerivedCategory.boundedConstructibleIntegral I X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
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

/-- Blueprint `rem-sf-constant-tower-trivial-model`: The trivial coefficient case, in one line.

The constant local system is its own reduction tower: the reduction `Λ_X ⊗ᴸ (Λ ⧸ J)_X` of the
constant complex `Λ_X` is the constant sheaf `(Λ ⧸ J)_X` placed in degree `0`, for every ideal
`J`. More generally, for any single complex `L` on `X` and derived reductions
`L_n = L ⊗ᴸ_Λ Λ ⧸ Iⁿ⁺¹`, the `L_n` form a normalized tower
(`AlgebraicGeometry.Etale.NormalizedTower.ofIsDerivedBaseChange`): putting the local model equal
to `L` exhibits the tower as the reduction tower of one complex, with no construction needed. -/
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

section IntegralStage

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
  [HasCompactification aX] [HasCompactification aY]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
  (f : X ⟶ Y) (hf : f ≫ aY = aX) [QuasiCompact f] [HasCompactification f]
  [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

include hϖ hI hf in
/-- Blueprint `rem-sf-clause-vii-status`: Proved coefficient transport and its domains.

At the integral stage (`Λ` a Noetherian domain complete for `I = (ϖ)`, `Λ ⧸ I` finite of
exponent invertible on `k`), for a separated finite-type `f : X ⟶ Y` of separated finite-type
`k`-schemes, the reductions `K ↦ K ⊗ᴸ Λ ⧸ Iⁿ` commute

* with pullback and tensor product (`lem-fix-operation-reduction`;
  `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_leftDerivedUpperStar`), with the
  ordinary and the compactly supported direct image
  (`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isPrincipal`);
* with the internal Hom, for arbitrary first variables, with the finite internal Hom of the
  reductions (`lem-coef-integral-hom-reduction`);
* with the exceptional inverse image (`prop-coef-integral-exceptional-adjoint`);

and a normalized DVR tower reconstructs with its stated reductions
(`lem-coef-normalized-dvr-effectivity`). -/
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
        Nonempty ((reductionModIdeal Λ X (I ^ n)).obj ((R(f)^![ModuleCat.{u + 1} Λ]).obj L) ≅
          (R(f)^![ModuleCat.{u + 1} Λ]).obj ((reductionModIdeal Λ Y (I ^ n)).obj L))) ∧
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
  obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal (R(f)^![ModuleCat.{u + 1} Λ]) hϖ n L
  exact ⟨e.symm⟩

include hϖ hI hf in
/-- Blueprint `rem-sf-finite-level-comparison-ingredient`: The local-model proof and normalized
DVR reconstruction.

Every normalized DVR tower `M_n` reconstructs, with no common stratification or lisse local
model: the canonical maps from its derived limit `R lim_n Res M_n` exhibit each `M_n` as the
reduction of the limit, which is derived complete (`lem-coef-normalized-dvr-effectivity`).
Independently, the integral internal Hom has the finite internal Homs of the reductions as its
reductions (`lem-coef-integral-hom-reduction`), and the integral exceptional adjoint `G_f L`
(the derived limit of the finite exceptional inverse images) is an object of `Dᵇc(X, Λ)`
identified with `Rf^! L` compatibly with the maps to the `Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)`
(`prop-coef-integral-exceptional-adjoint`). -/
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
        R(f)^![ModuleCat.{u + 1} Λ]), Pretriangulated.IsHomotopyLimit c →
        DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
          ∃ e : (R(f)^![ModuleCat.{u + 1} Λ]).obj L ≅ c.pt, ∀ n : ℕ,
            e.hom ≫ c.π.app (op n) = (R(f)^![ModuleCat.{u + 1} Λ]).map
              ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n)) := by
  obtain ⟨-, hhom, -, -, hexc, -, heff⟩ := preservationMatrix_integral I hϖ hI aX aY f hf
  exact ⟨heff, hhom, fun L hL c hc ↦ ⟨(hexc L hL c hc).1, (hexc L hL c hc).2.1⟩⟩

include hϖ hI hf in
/-- Blueprint `rem-ptr-weil-exceptional-adjoint-admissibility-10`: Admissibility on the proved
constructible domains.

On the integral constructible categories the exceptional adjoint is transported along the
coefficient reductions (`prop-coef-integral-exceptional-adjoint`): for `L ∈ Dᵇc(Y, Λ)` the
derived limit `G_f L` of the `Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)` lies in `Dᵇc(X, Λ)`, is `Rf^! L`, and has the
`Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)` as reductions; the reconstruction used for integral coefficients is the
normalized DVR theorem (`lem-coef-normalized-dvr-effectivity`). -/
theorem exceptionalAdjoint_admissibility_constructible :
    (∀ L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.boundedConstructibleIntegral I Y L →
      ∀ c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
        R(f)^![ModuleCat.{u + 1} Λ]), Pretriangulated.IsHomotopyLimit c →
        DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
          (∃ e : (R(f)^![ModuleCat.{u + 1} Λ]).obj L ≅ c.pt, ∀ n : ℕ,
            e.hom ≫ c.π.app (op n) = (R(f)^![ModuleCat.{u + 1} Λ]).map
              ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n))) ∧
          ∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj c.pt ≅
            (R(f)^![ModuleCat.{u + 1} Λ]).obj ((reductionModIdeal Λ Y (I ^ n)).obj L))) ∧
    ∀ (M : NormalizedTower I X) (c : Cone M.restrict), Pretriangulated.IsHomotopyLimit c →
      (∀ n : ℕ, IsDerivedBaseChange (φ := Ideal.Quotient.mk (I ^ (n + 1))) (c.π.app (op n))) ∧
        DerivedCategory.derivedComplete X.smallEtaleTopology I c.pt := by
  obtain ⟨-, -, -, -, hexc, -, heff⟩ := preservationMatrix_integral I hϖ hI aX aY f hf
  exact ⟨hexc, heff⟩

include hϖ hI hf in
/-- Blueprint `rem-ptr-trf-admissibility-14`: Coefficient clauses in trace admissibility.

The coefficient comparisons used by the trace admissibility hypothesis on the integral
constructible categories: the compactly supported direct image commutes with the reductions
`K ↦ K ⊗ᴸ Λ ⧸ Iⁿ`, and the integral exceptional adjoint `G_f L` of `L ∈ Dᵇc(Y, Λ)` lies in
`Dᵇc(X, Λ)`, is identified with `Rf^! L` compatibly with the maps to the `Rf^!(L ⊗ᴸ Λ ⧸ Iⁿ)`
(so that the units and counits of `Rf_! ⊣ Rf^!` are transported), and has these as reductions
(`prop-coef-integral-exceptional-adjoint`). Geometric base-change assertions keep the scope of
their own theorems. -/
theorem exceptionalAdjoint_traceAdmissibility_coefficients :
    (∀ n : ℕ, Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y (I ^ n) ≅
      reductionModIdeal Λ X (I ^ n) ⋙ R(f)_![ModuleCat.{u + 1} Λ])) ∧
    ∀ L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.boundedConstructibleIntegral I Y L →
      ∀ c : Cone (DerivedCategory.derivedCompletionDiagram Y.smallEtaleTopology I L ⋙
        R(f)^![ModuleCat.{u + 1} Λ]), Pretriangulated.IsHomotopyLimit c →
        DerivedCategory.boundedConstructibleIntegral I X c.pt ∧
          (∃ e : (R(f)^![ModuleCat.{u + 1} Λ]).obj L ≅ c.pt, ∀ n : ℕ,
            e.hom ≫ c.π.app (op n) = (R(f)^![ModuleCat.{u + 1} Λ]).map
              ((DerivedCategory.derivedCompletionCone Y.smallEtaleTopology I L).π.app (op n))) ∧
          ∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj c.pt ≅
            (R(f)^![ModuleCat.{u + 1} Λ]).obj ((reductionModIdeal Λ Y (I ^ n)).obj L)) :=
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
/-- Blueprint `rem-sf-direct-image-proof-status`: Status of the recorded argument for clause
(iii).

For a finite `Λ` whose exponent is invertible on `k` and a separated morphism `f : X ⟶ Y` of
finite-type `k`-schemes with `dim X ≤ d`, clause (iii) of `thm-sf-ctf-stability` holds on both
sites with the interval `[a, b + 2d]`:

* on the small étale site it is unconditional (`cor-sf-direct-image-ctf-nonproper`): `Rf_*`
  preserves `Dctf` and sends a bounded constructible complex of Tor amplitude `[a, b]` to one of
  Tor amplitude `[a, b + 2d]` (`sk-thm-sf-direct-image-tor-amplitude`, whose uniform bound is
  the étale direct-image vanishing `lem-sf-etale-direct-image-vanishing`);
* on the small pro-étale site the same holds for every bounded constructible complex
  (`cor-sf-direct-image-ctf-proetale`). -/
theorem constructibleFiniteTor_rightDerivedLowerStar_proofStatus [IsSeparated aX]
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
/-- Blueprint `rem-ptr-weil-exceptional-inverse-image-16`: Constructible exceptional inverse
images at all coefficient stages, the finite stage.

For a finite `Λ` whose exponent is invertible on `k` and a separated finite-type `f : X ⟶ Y` of
separated finite-type `k`-schemes, the exceptional inverse image carries `Dctf(Y, Λ)` into
`Dctf(X, Λ)`, it is `Rf^! ≅ 𝔻_X f^* 𝔻_Y` there (the dual formula of `lem-coef-finite-exceptional`),
and it is right adjoint to `Rf_!` on the constructible finite-Tor categories
(`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction`). The
integral construction and adjunction are
`AlgebraicGeometry.Etale.exceptionalAdjoint_admissibility_constructible`
(`prop-coef-integral-exceptional-adjoint`). -/
theorem exceptionalInverseImage_coefficientStages [IsSeparated aX] [HasCompactification aX]
    [IsSeparated aY] [HasCompactification aY] [HasInvertibleExponent Λ Y] [QuasiCompact f]
    [HasCompactification f] :
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) ∧
          Nonempty ((R(f)^![ModuleCat.{u + 1} Λ]).obj K ≅
            (verdierDual (ModuleCat.{u + 1} Λ) aX).obj
              (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
                ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K)))))) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
      DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f) :=
  ⟨fun _ hK ↦ ⟨constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hK,
      nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY f hf hK⟩,
    ⟨DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f⟩⟩

omit [HasInvertibleExponent Λ (Spec (.of k))] in
/-- Blueprint `rem-sf-ctf-descent`: How the verified domains enter the formal framework.

The clauses of `thm-sf-ctf-stability` enter the six-functor datum `def-sf-datum` only on their
displayed domains: for a finite `Λ` whose exponent is invertible on `Y` and a separated
finite-type `f : X ⟶ Y` of finite-type `k`-schemes, the restrictions of `Lf^*`, `Rf_*`, `Rf_!`
and `Rf^!` to the constructible finite-Tor categories form adjunctions `Lf^* ⊣ Rf_*` and
`Rf_! ⊣ Rf^!` there, with the units and counits of the ambient adjunctions. -/
theorem DerivedCategoryFiniteTor.ctfDescent [HasInvertibleExponent Λ Y] [IsSeparated f]
    [QuasiCompact f] [HasCompactification f] :
    Nonempty (DerivedCategoryFiniteTor.leftDerivedUpperStar (ModuleCat.{u + 1} Λ) f ⊣
      DerivedCategoryFiniteTor.rightDerivedLowerStar Λ aX aY f hf) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
      DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f) :=
  ⟨⟨DerivedCategoryFiniteTor.leftDerivedUpperStarAdjunction Λ aX aY f hf⟩,
    ⟨DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f⟩⟩

/-- Blueprint `open-sf-preservation-gaps`: Scope beyond the constructible coefficient category.

The dimension-free internal-Hom bound needs a site-perfect first variable. For `X` of finite type
over an algebraically closed `k`, `dim X ≤ m`, and bounded constructible `K`, `M` of Tor
amplitude `[a, b]` and `[c, d]`, `RHom(K, M)` has Tor amplitude in `[c - b - 2m, d - a + 2m]`,
and in `[c - b, d - a]` when `K` is dualizable; but the interval `[c - b, d - a]` fails for
general constructible `K` (`rem-sf-proetale-hom-status`,
`AlgebraicGeometry.Etale.not_forall_torAmplitudeIn_derivedHom`, which uses the normalisation of
the Tate twist). The remaining items of the remark (general duality at the field stages, towers
outside the normalized DVR systems, ambient adjunctions) are scope statements with no formal
content here. -/
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
