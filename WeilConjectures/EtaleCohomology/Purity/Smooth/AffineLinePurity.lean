/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineTrace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Twist
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarLeftProjection

/-!
# Affine-line purity

Let `Y` be a scheme on which the exponent of the finite coefficient ring `Λ` is invertible,
`p : 𝔸¹_Y → Y` the projection, `j : 𝔸¹_Y ↪ ℙ¹_Y` the standard chart and `q : ℙ¹_Y → Y` the
projection. Write `T = Λ(1)[2]`.

## The projective-line adjunction

The projective-line trace `t_q : Rq_* T ⟶ Λ_Y` (`def-amb-p1-trace`) extends to the *counit*

`ε_K : Rq_*(Lq^* K ⊗ T) ≅ K ⊗ Rq_* T ⟶ K ⊗ Λ_Y ≅ K`

through the proper projection formula, and `Rq_* ⊣ Lq^*(-) ⊗ T` with this counit
(`thm-amb-p1-adjunction`, of subsection `sk-prop-sf-cbc`, stated here as
`AlgebraicGeometry.Etale.bijective_projectiveLineCounit`).

## The affine-line comparison

Restricting `ε` along the open immersion `j` (that is, composing with `j_! ⊣ j^*`) gives the
counit

`ε'_K : Rp_!(Lp^* K ⊗ T) = Rq_* j_!(j^*(Lq^* K ⊗ T)) ⟶ Rq_*(Lq^* K ⊗ T) ⟶ K`,

which on `K = Λ_Y` is the integration map `∫_p` of `AlgebraicGeometry.Etale.affineLineTrace`.
The *affine-line purity comparison* (`def-pur-affine-line-purity-comparison`)

`γ_{p,K} : Lp^* K(1)[2] ⟶ Rp^! K`

is the transpose under `Rp_! ⊣ Rp^!` of `ε'_K`, read through `Lp^* K(1)[2] ≅ Lp^* K ⊗ T`. It is an
isomorphism (`thm-pur-affine-line-purity`): `ε'` is the counit of the adjunction obtained by
composing `j_! ⊣ j^*` with the projective-line adjunction, so `Rp_!` has the right adjoint
`Lp^*(-) ⊗ T` with counit `ε'`, and `γ` is the comparison of two right adjoints.

## Main definitions

- `AlgebraicGeometry.Etale.projectiveLineCounit`: `ε_K`.
- `AlgebraicGeometry.Etale.projectiveLineAdjunction`: `Rq_* ⊣ Lq^*(-) ⊗ T`.
- `AlgebraicGeometry.Etale.affineLineCounit`: `ε'_K`.
- `AlgebraicGeometry.Etale.affineLineIntegration`: `Rp_!(Lp^* K(1)[2]) ⟶ K`.
- `AlgebraicGeometry.Etale.affineLinePurity`: `γ_{p,K}`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_affineLineCounit`: `Rp_! ⊣ Lp^*(-) ⊗ T` with counit `ε'`.
- `AlgebraicGeometry.Etale.isIso_affineLinePurity`: `γ_{p,K}` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (Y : Scheme.{u})
  [HasInvertibleExponent Λ Y] [HasKummerClass.IsNormalized Λ]

/-! ### The projective-line adjunction -/

section ProjectiveLine

/-- Blueprint `def-amb-p1-trace`: Projective-line trace before an exceptional adjoint

The *counit* of the projective-line adjunction: for `K` on `Y`,

`ε_K : Rq_*(Lq^* K ⊗ Λ(1)[2]) ≅ K ⊗ Rq_* Λ(1)[2] ⟶ K ⊗ Λ_Y ≅ K`,

the inverse of the proper projection formula
(`AlgebraicGeometry.Etale.rightDerivedLowerStarLeftProjectionIso`), followed by `1 ⊗ t_q` for the
projective-line trace `t_q` (`AlgebraicGeometry.Etale.projectiveLineTrace`) and the right unitor. -/
noncomputable def projectiveLineCounit
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) (ProjectiveLine Y)).obj
          ((L((ProjectiveLine Y ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
            ((tateObject Λ (ProjectiveLine Y) 1)⟦(2 : ℤ)⟧)) ⟶ K :=
  (rightDerivedLowerStarLeftProjectionIso Λ (ProjectiveLine Y ↘ Y) K _).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).map (projectiveLineTrace Λ Y) ≫
      (derivedTensorRightUnitor _ Y K).hom

/-- Blueprint `thm-amb-p1-adjunction`: The full projective-line adjunction

On the whole derived categories of étale `Λ`-modules, `Rq_* ⊣ Lq^*(-) ⊗ Λ(1)[2]` for the
projection `q : ℙ¹_Y ⟶ Y`, with counit the counit `ε` of `def-amb-p1-trace`
(`AlgebraicGeometry.Etale.projectiveLineCounit`): for every `M` on `ℙ¹_Y` and `K` on `Y`,
`φ ↦ ε_K ∘ Rq_* φ` is a bijection

`Hom(M, Lq^* K ⊗ Λ(1)[2]) ≅ Hom(Rq_* M, K)`.

The unit `M ⟶ Lq^* Rq_* M ⊗ Λ(1)[2]` is induced by the supported class of the diagonal of
`ℙ¹_Y ×_Y ℙ¹_Y`, and the triangle identities reduce, by the projective-line decomposition and
proper base change, to `t_q(h) = 1` on the fibres of the two projections. -/
theorem bijective_projectiveLineCounit
    (M : _root_.DerivedCategory (Sheaf (ProjectiveLine Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (fun φ : M ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) (ProjectiveLine Y)).obj
          ((L((ProjectiveLine Y ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
            ((tateObject Λ (ProjectiveLine Y) 1)⟦(2 : ℤ)⟧) ↦
      R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).map φ ≫ projectiveLineCounit Λ Y K) :=
  sorry

end ProjectiveLine

/-! ### The affine line -/

section AffineLine

/-- The identification `Lp^* K ⊗ Λ(1)[2] ≅ j^*(Lq^* K ⊗ Λ(1)[2])` along the standard chart
`j : 𝔸¹_Y ↪ ℙ¹_Y`, from `p = j ≫ q`, `Λ_{𝔸¹}(1)[2] ≅ Lj^* Λ_{ℙ¹}(1)[2]` and the monoidal
structure of `Lj^*`. -/
noncomputable def affineLineRestrictionIso
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Y)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧) ≅
      D((affineLineChart Y)^*[ModuleCat.{u + 1} Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) (ProjectiveLine Y)).obj
          ((L((ProjectiveLine Y ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
            ((tateObject Λ (ProjectiveLine Y) 1)⟦(2 : ℤ)⟧)) :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Y)).mapIso
      ((leftDerivedUpperStarComp _ (affineLineChart Y) (ProjectiveLine Y ↘ Y)
        (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) (affineLineChart_over Y).symm).app K)).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Y)).obj _).mapIso
      (leftDerivedUpperStarTateShiftIso Λ (affineLineChart Y) 1).symm ≪≫
    (leftDerivedUpperStarTensorIso _ (affineLineChart Y) _ _).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory _ (affineLineChart Y)).app _

/-- The *counit* of the affine-line adjunction: the restriction of the projective-line counit
`ε` (`AlgebraicGeometry.Etale.projectiveLineCounit`) along the standard chart,

`ε'_K : Rp_!(Lp^* K ⊗ Λ(1)[2]) = Rq_* j_!(Lp^* K ⊗ Λ(1)[2]) ⟶ Rq_*(Lq^* K ⊗ Λ(1)[2]) ⟶ K`,

the middle map being the transpose under `j_! ⊣ j^*` of
`AlgebraicGeometry.Etale.affineLineRestrictionIso`. At `K = Λ_Y` it is the integration map
`∫_p = t_q ∘ (forget supports)` of `AlgebraicGeometry.Etale.affineLineTrace`. -/
noncomputable def affineLineCounit
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Y)).obj
          ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
            ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧)) ⟶ K :=
  (rightDerivedLowerShriekIso Λ (affineLineCompactification Y)).inv.app _ ≫
    R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).map
      (((derivedOpenImmersionLowerShriekUpperStarAdjunction _ (affineLineChart Y)).homEquiv
        _ _).symm
        (affineLineRestrictionIso Λ Y K).hom) ≫
    projectiveLineCounit Λ Y K

/-- Blueprint `cor-amb-affine-space-adjunction`: Affine-space ambient adjunction

*The case of the affine line.* `Rp_! ⊣ Lp^*(-) ⊗ Λ(1)[2]` with counit `ε'`
(`AlgebraicGeometry.Etale.affineLineCounit`): for every `M` on `𝔸¹_Y` and `K` on `Y`,
`φ ↦ ε'_K ∘ Rp_! φ` is a bijection `Hom(M, Lp^* K ⊗ Λ(1)[2]) ≅ Hom(Rp_! M, K)`. It is the
composite of `j_! ⊣ j^*` with the projective-line adjunction
(`AlgebraicGeometry.Etale.bijective_projectiveLineCounit`), since
`Rp_! = Rq_* j_!` and `Lp^*(-) ⊗ Λ(1)[2] ≅ j^*(Lq^*(-) ⊗ Λ(1)[2])`. -/
theorem bijective_affineLineCounit
    (M : _root_.DerivedCategory (Sheaf 𝔸(ULift.{u} (Fin 1); Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (fun φ : M ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ)
          𝔸(ULift.{u} (Fin 1); Y)).obj
          ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
            ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧) ↦
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map φ ≫
        affineLineCounit Λ Y K) := by
  set e := rightDerivedLowerShriekIso Λ (affineLineCompactification Y)
  set adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
    (affineLineChart Y)
  have h : (fun φ : M ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ)
          𝔸(ULift.{u} (Fin 1); Y)).obj
          ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
            ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧) ↦
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map φ ≫
        affineLineCounit Λ Y K) =
      (fun ψ ↦ e.inv.app M ≫ ψ) ∘
        (fun ψ ↦ R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).map ψ ≫
          projectiveLineCounit Λ Y K) ∘ (adj.homEquiv _ _).symm ∘
        (fun φ ↦ φ ≫ (affineLineRestrictionIso Λ Y K).hom) := by
    funext φ
    simp only [Function.comp_apply, affineLineCounit, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc]
    rw [NatTrans.naturality_assoc]
    rfl
  rw [h]
  refine (Function.Bijective.comp ?_ (Function.Bijective.comp
    (bijective_projectiveLineCounit Λ Y _ K) (Function.Bijective.comp (Equiv.bijective _) ?_)))
  · exact ⟨fun _ _ h ↦ by simpa using h, fun ψ ↦ ⟨e.hom.app M ≫ ψ, by simp⟩⟩
  · exact ⟨fun _ _ h ↦ by simpa using h,
      fun ψ ↦ ⟨ψ ≫ (affineLineRestrictionIso Λ Y K).inv, by simp⟩⟩

/-- The *integration map* `Rp_!(Lp^* K(1)[2]) ⟶ K` of the affine line: the counit `ε'_K`
(`AlgebraicGeometry.Etale.affineLineCounit`) read through the twist reassociation
`Lp^* K(1)[2] ≅ Lp^* K ⊗ Λ(1)[2]` (`AlgebraicGeometry.Etale.twistShiftObjIso`). In the
blueprint it is `Rp_! Lp^* K(1)[2] ≅ K ⊗ Rp_! Λ(1)[2] ⟶ K`, the projection formula followed by
`1 ⊗ ∫_p`. -/
noncomputable def affineLineIntegration
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj
          ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K)) ⟶ K :=
  (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
      ((twistShiftObjIso Λ 𝔸(ULift.{u} (Fin 1); Y) 1 _).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Y)).obj _).map
          (twistShiftConstantComplexIso Λ 𝔸(ULift.{u} (Fin 1); Y) 1).hom) ≫
    affineLineCounit Λ Y K

/-- Blueprint `def-pur-affine-line-purity-comparison`: Affine-line purity comparison

For the projection `p : 𝔸¹_Y ⟶ Y` and `K` on `Y`, the *affine-line purity comparison*

`γ_{p,K} : Lp^* K(1)[2] ⟶ Rp^! K`

is the transpose under `Rp_! ⊣ Rp^!` of the integration map
`Rp_! Lp^* K(1)[2] ≅ K ⊗ Rp_! Λ(1)[2] ⟶ K` (`AlgebraicGeometry.Etale.affineLineIntegration`),
built from the projective-line trace restricted to the affine line. -/
noncomputable def affineLinePurity
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj
        ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^![ModuleCat.{u + 1} Λ]).obj K :=
  (rightDerivedUpperShriekAdjunction _ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).homEquiv _ _
    (affineLineIntegration Λ Y K)

/-- Blueprint `thm-pur-affine-line-purity`: Affine-line purity

The affine-line purity comparison `γ_{p,K} : Lp^* K(1)[2] ⟶ Rp^! K`
(`AlgebraicGeometry.Etale.affineLinePurity`) is an isomorphism, for every `K` on `Y`.

`Rp_!` has the two right adjoints `Rp^!` and `Lp^*(-) ⊗ Λ(1)[2]`, the latter with counit the
restricted trace `ε'` (`AlgebraicGeometry.Etale.bijective_affineLineCounit`), and `γ_{p,K}` is the
transpose of `ε'_K`: so `Hom(M, Lp^* K(1)[2]) ⟶ Hom(M, Rp^! K)`, `φ ↦ γ_{p,K} ∘ φ`, is the
composite of the bijections `φ ↦ ε'_K ∘ Rp_! φ` and `Hom(Rp_! M, K) ≅ Hom(M, Rp^! K)`, and
`γ_{p,K}` is an isomorphism by the Yoneda lemma. The hypothesis `K ∈ D^b_{ctf}` of the blueprint
is not needed. -/
theorem isIso_affineLinePurity
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (affineLinePurity Λ Y K) := by
  refine isIso_of_yoneda_map_bijective _ fun M ↦ ?_
  set adj := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)
  set ι := (twistShiftObjIso Λ 𝔸(ULift.{u} (Fin 1); Y) 1 _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Y)).obj _).mapIso
      (twistShiftConstantComplexIso Λ 𝔸(ULift.{u} (Fin 1); Y) 1))
  have h : (fun x : M ⟶ (twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj
        ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj K) ↦
      x ≫ affineLinePurity Λ Y K) =
      adj.homEquiv _ _ ∘ (fun φ ↦ (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map φ ≫
        affineLineCounit Λ Y K) ∘ (fun x ↦ x ≫ ι.hom) := by
    funext x
    simp only [Function.comp_apply, affineLinePurity, affineLineIntegration, ι, Iso.trans_hom,
      Functor.mapIso_hom, ← Adjunction.homEquiv_naturality_left, Functor.map_comp,
      Category.assoc]
    rfl
  rw [h]
  exact (Equiv.bijective _).comp ((bijective_affineLineCounit Λ Y M K).comp
    ⟨fun _ _ h ↦ by simpa using h, fun ψ ↦ ⟨ψ ≫ ι.inv, by simp⟩⟩)

end AffineLine

end Etale

end AlgebraicGeometry
