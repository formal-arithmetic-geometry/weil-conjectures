/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.BrownComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.TateTwist.ProEtaleConstructible

/-!

# Smooth purity for the `ℓ`-adic coefficient rings

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
objects `X : Over (Spec (.of k))`, separated and of finite type over `Spec k`. Let `Λ` be an
`ℓ`-adic coefficient ring, `[IsEllAdicFinitenessCoefficient ℓ Λ]` (`𝒪̲_E`, `E̲` or `ℚ̲̄_ℓ`), under
`ℤ̲_ℓ` through `φ : ℤ̲_ℓ ⟶ Λ`, with Tate twists `Λ_X(d)` along `φ`
(`WeilConjectures.TateTwist.ProEtale`). For these rings the categories `Dctf(X, Λ)` of the
blueprint are the bounded constructible categories `Dᵇc(X)⟦Λ⟧`.

For `f : X ⟶ Y` smooth of pure relative dimension `d`, this file states and proves smooth purity
in the form of blueprint `sk-thm-purity-transport` for these coefficient rings:

* the *twisted inverse image* `K ↦ Lf^* K(d)[2d]`, a functor `Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧`
  (`ProEtale.CondensedRing.boundedConstructibleTwistShiftPullback`), is right adjoint to `Rf_!`
  (`ProEtale.CondensedRing.HasSmoothPurityAdjunction`, the adjunction
  `ProEtale.CondensedRing.smoothPurityAdjunction`);
* there is a unique isomorphism `γ_f : Lf^*(-)(d)[2d] ≅ Rf^!` of functors on `Dᵇc(Y)⟦Λ⟧`
  compatible with the counits of `Rf_! ⊣ Lf^*(-)(d)[2d]` and `Rf_! ⊣ Rf^!`
  (`ProEtale.CondensedRing.existsUnique_smoothPurityNatIso`), the *purity isomorphism*
  `ProEtale.CondensedRing.smoothPurityNatIso`.

The finite coefficient case of `sk-thm-purity-transport` is
`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.exists_existsUnique_smoothPurityNatIso`
(`WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`).

## Inputs from other subsections

The adjunction `Rf_! ⊣ Lf^*(-)(d)[2d]` is, for each `ℓ`-adic ring, a proposition of another
subsection of the blueprint, stated here (`sorry`) as exactly that node:

- `ProEtale.CondensedRing.exists_adjunction_iso_twistShiftPullback_padicIntegers`
  (`det-sp-integral-adjunction-bijection`, `Λ = 𝒪_E`): a right adjoint `H` of `Rf_!`, isomorphic
  to the twisted inverse image; the blueprint's `H` is the derived limit
  `R lim_n f^!_{𝒪_E/ℓ^n}(K/ℓ^n)` of the finite exceptional inverse images, whose construction (the
  tower model of `Dᵇc(-)⟦𝒪̲_E⟧`) is not formalized, so only its existence is recorded;
- `ProEtale.CondensedRing.nonempty_twistShiftPullbackAdjunction_normedExtension`
  (`det-sp-rational-adjunction`, (1), `Λ = E`);
- `ProEtale.CondensedRing.nonempty_twistShiftPullbackAdjunction_padicAlgCl`
  (`det-sp-qbar-adjunction`, `Λ = ℚ̄_ℓ`).

Only the existence of the adjunctions is recorded, not the normalization of their counits by
integration on the affine line: there is no affine-line integration map in the pro-étale
formalism. Accordingly the purity isomorphism is the counit-compatible isomorphism for a chosen
adjunction (`smoothPurityAdjunction`). The constructibility of the twisted inverse image rests on
that of the Tate twists,
`ProEtale.CondensedRing.boundedConstructible_shiftFunctor_tateTwistDerived`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ]
  [IsCommMonObj Λ] [IsEllAdicFinitenessCoefficient ℓ Λ]
  (φ : Profinite.continuousMapRingObj.{u} ℤ_[ℓ] ⟶ Λ) [IsMonHom φ]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ)

/-! ### The twisted inverse image -/

/-- The **twisted inverse image** `K ↦ Lf^* K(d)[2d] = Lf^* K ⊗ᴸ Λ_X(d)[2d]`, as a functor
`Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧`: the derived pullback followed by the derived tensor product with the
shifted Tate twist `Λ_X(d)[2d]` (`boundedConstructibleTateTwist`), which is bounded
constructible. -/
noncomputable def boundedConstructibleTwistShiftPullback : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  boundedConstructibleUpperStar Λ ℓ f ⋙
    tensorRight (boundedConstructibleTateTwist φ X d (2 * d))

/-- The twisted inverse image `K ↦ Lf^* K(d)[2d]` is right adjoint to `Rf_!` on the bounded
constructible categories. This holds for `f` smooth of pure relative dimension `d` and the
`ℓ`-adic coefficient rings (`ProEtale.CondensedRing.hasSmoothPurityAdjunction_padicIntegers`,
`ProEtale.CondensedRing.hasSmoothPurityAdjunction_normedExtension`,
`ProEtale.CondensedRing.hasSmoothPurityAdjunction_padicAlgCl`). -/
class HasSmoothPurityAdjunction : Prop where
  nonempty_adjunction :
    Nonempty (boundedConstructibleLowerShriek Λ ℓ f ⊣ boundedConstructibleTwistShiftPullback φ f d)

/-- The adjunction `Rf_! ⊣ Lf^*(-)(d)[2d]` on the bounded constructible categories, a chosen one
(`HasSmoothPurityAdjunction`). Its counit at `K` is the smooth trace `Tr_f(K)`
(`ProEtale.CondensedRing.map_smoothPurityNatIso_hom_app_comp_counit`). -/
noncomputable def smoothPurityAdjunction [HasSmoothPurityAdjunction φ f d] :
    boundedConstructibleLowerShriek Λ ℓ f ⊣ boundedConstructibleTwistShiftPullback φ f d :=
  (HasSmoothPurityAdjunction.nonempty_adjunction (φ := φ) (f := f) (d := d)).some

/-- Blueprint `det-sp-comparison-brown-explicit`: The twisted inverse image is right adjoint to
`Rf_!` for every admissible coefficient ring (`ℓ`-adic coefficients).

For `f` smooth of pure relative dimension `d` and `Λ ∈ {𝒪_E, E, ℚ̄_ℓ}`, the functor
`K ↦ Lf^* K(d)[2d]`, `Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧`, is right adjoint to `Rf_!`. For `𝒪_E` this is the
adjunction of `det-sp-integral-adjunction-bijection` transported along `γ^H_f`
(`nonempty_twistShiftPullbackAdjunction_padicIntegers`), for `E` and `ℚ̄_ℓ` it is
`det-sp-rational-adjunction` (1) and `det-sp-qbar-adjunction`; the instances
`hasSmoothPurityAdjunction_padicIntegers`, `hasSmoothPurityAdjunction_normedExtension` and
`hasSmoothPurityAdjunction_padicAlgCl` record them. The normalization of the counit by
integration on the affine line is not formalized. The finite coefficient case is
`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.exists_twistShiftPullbackAdjunction`. -/
theorem nonempty_twistShiftPullbackAdjunction [HasSmoothPurityAdjunction φ f d] :
    Nonempty (boundedConstructibleLowerShriek Λ ℓ f ⊣
      boundedConstructibleTwistShiftPullback φ f d) :=
  ⟨smoothPurityAdjunction φ f d⟩

/-! ### Comparison with the exceptional inverse image -/

section UpperShriek

variable [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint]

/-- Blueprint `det-sp-comparison-brown-unique`: Identification of the explicit adjoint with the
exceptional inverse image (`ℓ`-adic coefficients).

The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` is a right adjoint of
`Rf_! : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` (`boundedConstructibleUpperShriekAdjunction`, the same `Rf_!`
being the left adjoint), and for every adjunction `adj : Rf_! ⊣ Lf^*(-)(d)[2d]` on the bounded
constructible categories, for instance the explicit one of `det-sp-comparison-brown-explicit`,
there is a unique isomorphism `Lf^*(-)(d)[2d] ≅ Rf^!` of functors on `Dᵇc(Y)⟦Λ⟧` compatible with
the counits (`det-sp-unique-right-adjoint`). In the pro-étale formalism `Rf^!` is constructed
directly on the bounded constructible categories, as a right adjoint of `Rf_!`, rather than as
the restriction of the Brown adjoint on the localizing hulls. -/
theorem existsUnique_twistShiftPullbackIso_counit
    (adj : boundedConstructibleLowerShriek Λ ℓ f ⊣ boundedConstructibleTwistShiftPullback φ f d) :
    ∃! γ : boundedConstructibleTwistShiftPullback φ f d ≅ boundedConstructibleUpperShriek Λ ℓ f,
      ∀ K : Dᵇc(Y.left)⟦Λ⟧,
        (boundedConstructibleLowerShriek Λ ℓ f).map (γ.hom.app K) ≫
          (boundedConstructibleUpperShriekAdjunction Λ ℓ f).counit.app K =
        adj.counit.app K :=
  Adjunction.existsUnique_iso_counit adj (boundedConstructibleUpperShriekAdjunction Λ ℓ f)

variable [HasSmoothPurityAdjunction φ f d]

/-- The **purity isomorphism** `γ_f : Lf^*(-)(d)[2d] ≅ Rf^!` of functors
`Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧`: the unique isomorphism compatible with the counits of
`Rf_! ⊣ Lf^*(-)(d)[2d]` (`smoothPurityAdjunction`) and `Rf_! ⊣ Rf^!`
(`existsUnique_smoothPurityNatIso`). -/
noncomputable def smoothPurityNatIso :
    boundedConstructibleTwistShiftPullback φ f d ≅ boundedConstructibleUpperShriek Λ ℓ f :=
  (smoothPurityAdjunction φ f d).rightAdjointUniq (boundedConstructibleUpperShriekAdjunction Λ ℓ f)

/-- The smooth trace `Tr_f(K) = ε_f(K) ∘ Rf_!(γ_f(K))` is the counit of the adjunction
`Rf_! ⊣ Lf^*(-)(d)[2d]`: the purity isomorphism is compatible with the counits. -/
@[reassoc]
lemma map_smoothPurityNatIso_hom_app_comp_counit (K : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleLowerShriek Λ ℓ f).map ((smoothPurityNatIso φ f d).hom.app K) ≫
        (boundedConstructibleUpperShriekAdjunction Λ ℓ f).counit.app K =
      (smoothPurityAdjunction φ f d).counit.app K :=
  Adjunction.rightAdjointUniq_hom_app_counit _ _ K

/-- Blueprint `sk-thm-purity-transport`: Smooth purity for all admissible coefficients
(`ℓ`-adic coefficients `𝒪_E`, `E`, `ℚ̄_ℓ`).

Let `f : X ⟶ Y` be smooth of pure relative dimension `d` and `Λ` an `ℓ`-adic coefficient ring
under `ℤ̲_ℓ`. The functor `K ↦ Lf^* K(d)[2d]`, `Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧`, is right adjoint to
`Rf_!`, and there is a *unique* isomorphism of functors `γ_f : Lf^*(-)(d)[2d] ≅ Rf^!` compatible
with the counits of the two adjunctions; it is `smoothPurityNatIso` for the adjunction
`smoothPurityAdjunction`. The adjunction is an instance for the three `ℓ`-adic rings
(`hasSmoothPurityAdjunction_padicIntegers`, `hasSmoothPurityAdjunction_normedExtension`,
`hasSmoothPurityAdjunction_padicAlgCl`, from blueprint `sk-prop-sp-integral-adjunction`,
`sk-prop-sp-rational` and `sk-thm-sp-qbar`); the uniqueness is `det-sp-unique-right-adjoint`.
For étale `f` (`d = 0`) it gives `Rf^! ≅ f^*(-) ⊗ Λ_X(0)[0] ≅ f^*`.

The finite coefficient case is
`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.exists_existsUnique_smoothPurityNatIso`. The
normalization of the counit by integration on the affine line, and the compatibilities with base
change and composition, are not part of this statement; the compatibility with change of
coefficients is `ProEtale.CondensedRing.smoothPurityNatIso_coefficientChange`. -/
theorem existsUnique_smoothPurityNatIso :
    ∃ adj : boundedConstructibleLowerShriek Λ ℓ f ⊣ boundedConstructibleTwistShiftPullback φ f d,
      ∃! γ : boundedConstructibleTwistShiftPullback φ f d ≅ boundedConstructibleUpperShriek Λ ℓ f,
        ∀ K : Dᵇc(Y.left)⟦Λ⟧,
          (boundedConstructibleLowerShriek Λ ℓ f).map (γ.hom.app K) ≫
            (boundedConstructibleUpperShriekAdjunction Λ ℓ f).counit.app K =
          adj.counit.app K :=
  ⟨smoothPurityAdjunction φ f d, existsUnique_twistShiftPullbackIso_counit φ f d _⟩

end UpperShriek

/-! ### The adjunctions for the `ℓ`-adic coefficient rings -/

section Integral

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- Blueprint `det-sp-integral-adjunction-bijection`: The derived limit of the tower adjunction
is an integral adjunction.

Let `f` be smooth of pure relative dimension `d` and `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ`.
There is a functor `H_{f,𝒪_E} : Dᵇc(Y)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` right adjoint to `Rf_!`, together
with an isomorphism `γ^H_f : Lf^*(-)(d)[2d] ≅ H_{f,𝒪_E}`. In the blueprint `H_{f,𝒪_E}(K)` is the
derived limit `R lim_n f^!_{𝒪_E/ℓ^n}(K/ℓ^n)` of the finite exceptional inverse images, and
`γ^H_f` the derived limit of the finite purity isomorphisms; the tower model of
`Dᵇc(-)⟦𝒪̲_E⟧` is not formalized, so only their existence is stated. -/
theorem exists_adjunction_iso_twistShiftPullback_padicIntegers
    [SmoothOfRelativeDimension d f.left] :
    ∃ H : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤
        Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧,
      Nonempty (boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ f ⊣ H) ∧
      Nonempty (boundedConstructibleTwistShiftPullback
        (Profinite.padicIntRingObjToPadicIntegers ℓ E) f d ≅ H) :=
  sorry

/-- Blueprint `det-sp-comparison-brown-explicit`: The twisted inverse image is right adjoint to
`Rf_!` (coefficients `𝒪_E`).

For `f` smooth of pure relative dimension `d`, the functor `K ↦ Lf^* K(d)[2d]` on
`Dᵇc(-)⟦𝒪̲_E⟧` is right adjoint to `Rf_!`: the adjunction `Rf_! ⊣ H_{f,𝒪_E}` of
`det-sp-integral-adjunction-bijection` transported along `γ^H_f : Lf^*(-)(d)[2d] ≅ H_{f,𝒪_E}`. -/
theorem nonempty_twistShiftPullbackAdjunction_padicIntegers [SmoothOfRelativeDimension d f.left] :
    Nonempty (boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ f ⊣
      boundedConstructibleTwistShiftPullback (Profinite.padicIntRingObjToPadicIntegers ℓ E) f
        d) := by
  obtain ⟨H, ⟨adj⟩, ⟨e⟩⟩ := exists_adjunction_iso_twistShiftPullback_padicIntegers (ℓ := ℓ) f d E
  exact ⟨adj.ofNatIsoRight e.symm⟩

instance hasSmoothPurityAdjunction_padicIntegers [SmoothOfRelativeDimension d f.left] :
    HasSmoothPurityAdjunction (Profinite.padicIntRingObjToPadicIntegers ℓ E) f d :=
  ⟨nonempty_twistShiftPullbackAdjunction_padicIntegers (ℓ := ℓ) f d E⟩

end Integral

section Rational

variable (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

/-- Blueprint `det-sp-rational-adjunction`: The rational purity adjunction and the purity map
over `E`, clause (1).

For `f` smooth of pure relative dimension `d` and a finite extension `E` of `ℚ_ℓ`, the functor
`K ↦ Lf^* K(d)[2d]` on `Dᵇc(-)⟦E̲⟧` is right adjoint to `Rf_!`. In the blueprint the adjunction
is defined on integral models, with unit and counit the scalar extensions of the integral ones;
only its existence is stated here. -/
theorem nonempty_twistShiftPullbackAdjunction_normedExtension
    [SmoothOfRelativeDimension d f.left] :
    Nonempty (boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ f ⊣
      boundedConstructibleTwistShiftPullback
        (Profinite.padicIntRingObjToNormedExtension ℓ E) f d) :=
  sorry

instance hasSmoothPurityAdjunction_normedExtension [SmoothOfRelativeDimension d f.left] :
    HasSmoothPurityAdjunction (Profinite.padicIntRingObjToNormedExtension ℓ E) f d :=
  ⟨nonempty_twistShiftPullbackAdjunction_normedExtension (ℓ := ℓ) f d E⟩

end Rational

section AlgebraicClosure

/-- Blueprint `det-sp-qbar-adjunction`: The `ℚ̄_ℓ` purity adjunction and purity map.

For `f` smooth of pure relative dimension `d`, the functor `K ↦ Lf^* K(d)[2d]` on
`Dᵇc(-)⟦ℚ̲̄_ℓ⟧` is right adjoint to `Rf_!`. In the blueprint the adjunction is defined by descent
to finite extensions `E` of `ℚ_ℓ`, with unit and counit transported from them; only its
existence is stated here. -/
theorem nonempty_twistShiftPullbackAdjunction_padicAlgCl [SmoothOfRelativeDimension d f.left] :
    Nonempty (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f ⊣
      boundedConstructibleTwistShiftPullback (Profinite.padicIntRingObjToPadicAlgCl ℓ) f d) :=
  sorry

instance hasSmoothPurityAdjunction_padicAlgCl [SmoothOfRelativeDimension d f.left] :
    HasSmoothPurityAdjunction (Profinite.padicIntRingObjToPadicAlgCl ℓ) f d :=
  ⟨nonempty_twistShiftPullbackAdjunction_padicAlgCl f d⟩

end AlgebraicClosure

end AlgebraicGeometry.ProEtale.CondensedRing
