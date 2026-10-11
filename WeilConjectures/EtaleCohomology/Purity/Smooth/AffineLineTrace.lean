/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# The trace of the affine line and the affine-line purity comparison

Let `Y` be a scheme on which the exponent of the finite coefficient ring `Λ` is invertible,
`p : 𝔸¹_Y → Y` the projection, `j : 𝔸¹_Y ↪ ℙ¹_Y` the standard chart `t ↦ [t : 1]`,
`q : ℙ¹_Y → Y` the projection and `∞ : Y → ℙ¹_Y` the section at infinity. This file
constructs the *integration map* of the affine line

`∫_p : Rp_! Λ(1)[2] = Rq_* j_! Λ(1)[2] ⟶ Rq_* Λ(1)[2] ⟶ Λ_Y`

out of the projective-line trace `t_q`, and its transpose, the *affine-line purity comparison*

`γ_{p,K} : Lp^* K(1)[2] ⟶ Rp^! K`

(blueprint `def-pur-affine-line-purity-comparison`).

## The projective-line trace

Write `σ_p : Λ_Y ⟶ Rp_! Λ(1)[2]` for the *class of the zero section*: the orientation
`pur_s : Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` (the adjoint of the Kummer boundary `∂κ(t)`, blueprint
`sk-prop-a1`) pushed forward along `Rp_!`, with `R(s ≫ p)_! ≅ Rp_! Rs_!` and `s ≫ p` an
isomorphism. Its image `h ∈ H²(ℙ¹_Y, Λ(1))` in `Rq_* Λ(1)[2]` is the class of the divisor
`[0 : 1]`, that is the Kummer first Chern class of `𝒪(1)`. The projective line decomposes as

`(1, h) : Λ_Y(1)[2] ⊕ Λ_Y ≅ Rq_* Λ(1)[2]`

(blueprint `thm-amb-p1-decomposition`, of subsection `sk-prop-sf-cbc`), and the trace `t_q` is
the projection onto the second summand (`def-amb-p1-trace`). By construction `t_q(h) = 1`, which
is the normalization `∫_p σ_p = 1` of the integration map.

## Main definitions

- `AlgebraicGeometry.Etale.affineLineCompactification`: `𝔸¹_Y ↪ ℙ¹_Y ⟶ Y`.
- `AlgebraicGeometry.Etale.affineLineZeroClass`: `σ_p : Λ_Y ⟶ Rp_! Λ(1)[2]`.
- `AlgebraicGeometry.Etale.projectiveLineDecomposition`: `(1, h)`.
- `AlgebraicGeometry.Etale.projectiveLineTrace`: `t_q : Rq_* Λ(1)[2] ⟶ Λ_Y`.
- `AlgebraicGeometry.Etale.affineLineTrace`: `∫_p : Rp_! Λ(1)[2] ⟶ Λ_Y`.

## Main statements

- `AlgebraicGeometry.Etale.affineLineZeroClass_affineLineTrace`: `∫_p σ_p = 1`.
- `AlgebraicGeometry.Etale.isIso_affineLineTrace`: `∫_p` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-! ### The standard compactification of the affine line -/

section Compactification

variable (Y : Scheme.{u})

/-- The standard affine chart `𝔸¹_Y ↪ ℙ¹_Y`, `t ↦ [t : 1]`, of
`AlgebraicGeometry.ProjectiveLine.affineChart`, read on `𝔸¹_Y = 𝔸(ULift (Fin 1); Y)`. -/
noncomputable def affineLineChart : 𝔸(ULift.{u} (Fin 1); Y) ⟶ ProjectiveLine Y :=
  (AffineSpace.reindexIso Y (Equiv.ofUnique PUnit.{u + 1} (ULift.{u} (Fin 1)))).hom ≫
    ProjectiveLine.affineChart Y

instance : IsOpenImmersion (affineLineChart Y) := by
  rw [affineLineChart]
  infer_instance

@[reassoc (attr := simp)]
lemma affineLineChart_over :
    affineLineChart Y ≫ ProjectiveLine Y ↘ Y = 𝔸(ULift.{u} (Fin 1); Y) ↘ Y := by
  simp [affineLineChart, AffineSpace.reindexIso, AffineSpace.reindex_over]

/-- The standard compactification `𝔸¹_Y ↪ ℙ¹_Y ⟶ Y` of the affine line. -/
noncomputable def affineLineCompactification :
    Compactification (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) where
  Z := ProjectiveLine Y
  g := ProjectiveLine Y ↘ Y
  i := affineLineChart Y
  comm := (affineLineChart_over Y).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The section at infinity is the closed complement of the affine chart. -/
lemma range_infinity_eq_compl_range_affineLineChart :
    Set.range (ProjectiveLine.infinity Y).base = (Set.range (affineLineChart Y).base)ᶜ := by
  have h := ProjectiveLine.range_infinity Y
  have h' : Set.range (affineLineChart Y).base =
      ((ProjectiveLine.affineChart Y).opensRange : Set (ProjectiveLine Y)) := by
    rw [affineLineChart, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 (AffineSpace.reindexIso Y _).hom.surjective, Set.image_univ]
    rfl
  rw [h']
  exact h

/-- The zero section `V(t) ⟶ 𝔸¹_Y`, followed by the projection, is an isomorphism `V(t) ≅ Y`:
it is the inverse of `AlgebraicGeometry.AffineSpace.zeroSectionIsoZeroLocusSubscheme`. -/
lemma zeroLocusSubschemeι_coord_over :
    𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)} ≫
        𝔸(ULift.{u} (Fin 1); Y) ↘ Y =
      (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) Y
        (s := {AffineSpace.coord Y (ULift.up 0)}) Set.range_unique).inv := by
  rw [← cancel_epi (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) Y
      (s := {AffineSpace.coord Y (ULift.up 0)}) Set.range_unique).hom, Iso.hom_inv_id,
    AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι_assoc,
    AffineSpace.zeroSection_over]

instance : IsIso (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
    {AffineSpace.coord Y (ULift.up 0)} ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y) := by
  rw [zeroLocusSubschemeι_coord_over]
  infer_instance

end Compactification

/-! ### The class of the zero section and the projective-line trace -/

section Trace

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (Y : Scheme.{u})

/-- For an isomorphism `e : X ⟶ Y`, the identification `Λ_Y ⟶ Re_! Λ_X`: the unit
`Λ_Y ⟶ Re_* Le^* Λ_Y`, read through `Le^* Λ_Y ≅ Λ_X` and `Re_! ≅ Re_*`. -/
noncomputable def constantComplexToLowerShriekOfIsIso {X Z : Scheme.{u}} (e : X ⟶ Z)
    [IsIso e] :
    constantComplex Λ Z ⟶ (R(e)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e).unit.app
      (constantComplex Λ Z) ≫
    R((e)_*[ModuleCat.{u + 1} Λ]).map (leftDerivedUpperStarConstantComplexIso Λ e).hom ≫
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) e).inv.app
      (constantComplex Λ X)

/-- The *class of the zero section* `σ_p : Λ_Y ⟶ Rp_! Λ(1)[2]` of the affine line
`p : 𝔸¹_Y ⟶ Y`: the orientation `pur_s : Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` of the zero section
`s : V(t) ⟶ 𝔸¹_Y` (`AlgebraicGeometry.Etale.affineLineOrientation`, the adjoint of the Kummer
boundary `∂κ(t)`), followed by the counit `Rs_! Rs^! ⟶ 𝟭` and pushed forward along `Rp_!`,
read through `Λ_Y ≅ R(s ≫ p)_! Λ_{V(t)} ≅ Rp_! Rs_! Λ_{V(t)}` (`s ≫ p` is an isomorphism). It is
the image of `∂κ(t) ∈ H²_{s(Y)}(𝔸¹_Y, Λ(1))` in `H⁰(Y, Rp_! Λ(1)[2]) = H²_c(𝔸¹_Y/Y, Λ(1))`. -/
noncomputable def affineLineZeroClass :
    constantComplex Λ Y ⟶ (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).obj
      ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧) :=
  constantComplexToLowerShriekOfIsIso Λ (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
      {AffineSpace.coord Y (ULift.up 0)} ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫
    (rightDerivedLowerShriekCompIso Λ (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
      {AffineSpace.coord Y (ULift.up 0)}) (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).hom.app
        (constantComplex Λ _) ≫
    (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
      ((R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
          {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ]).map
        (affineLineOrientation Λ Y) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ)
          (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
            {AffineSpace.coord Y (ULift.up 0)})).counit.app
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧))

/-- The identification `j^* Λ_{ℙ¹}(1)[2] ≅ Λ_{𝔸¹}(1)[2]` along the affine chart. -/
noncomputable def affineLineChartTateShiftIso :
    (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧ ≅
      D((affineLineChart Y)^*[ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ (ProjectiveLine Y) 1)⟦(2 : ℤ)⟧) :=
  (leftDerivedUpperStarTateShiftIso Λ (affineLineChart Y) 1).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory _ (affineLineChart Y)).app _

/-- The *forget-supports map* `Rp_! Λ(1)[2] = Rq_* j_! Λ(1)[2] ⟶ Rq_* Λ(1)[2]` of the standard
compactification `𝔸¹_Y ↪ ℙ¹_Y`: the counit `j_! j^* ⟶ 𝟭` pushed forward along `Rq_*`, read
through the independence of the compactification. -/
noncomputable def affineLineForgetSupports :
    (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧) ⟶
      R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ (ProjectiveLine Y) 1)⟦(2 : ℤ)⟧) :=
  (rightDerivedLowerShriekIso Λ (affineLineCompactification Y)).inv.app _ ≫
    R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).map
      (D((affineLineChart Y)_!open[ModuleCat.{u + 1} Λ]).map
          (affineLineChartTateShiftIso Λ Y).hom ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction _ (affineLineChart Y)).counit.app _)

/-- The *hyperplane class* `h ∈ H²(ℙ¹_Y, Λ(1))`, as a map `Λ_Y ⟶ Rq_* Λ(1)[2]`: the class of the
divisor `[0 : 1]`, the image of the class of the zero section of the affine chart
(`AlgebraicGeometry.Etale.affineLineZeroClass`) under the forget-supports map. Since
`𝒪(1) ≅ 𝒪([0 : 1])`, it is the Kummer first Chern class `c₁(𝒪(1))` of the blueprint. -/
noncomputable def projectiveLineHyperplaneClass :
    constantComplex Λ Y ⟶ R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).obj
      ((tateObject Λ (ProjectiveLine Y) 1)⟦(2 : ℤ)⟧) :=
  affineLineZeroClass Λ Y ≫ affineLineForgetSupports Λ Y

/-- The pullback `Λ_Y(1)[2] ⟶ Rq_* q^* Λ_Y(1)[2] ≅ Rq_* Λ_{ℙ¹}(1)[2]` along `q : ℙ¹_Y ⟶ Y`. -/
noncomputable def projectiveLinePullback :
    (tateObject Λ Y 1)⟦(2 : ℤ)⟧ ⟶ R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).obj
      ((tateObject Λ (ProjectiveLine Y) 1)⟦(2 : ℤ)⟧) :=
  (derivedUpperStarLowerStarAdjunction _ (ProjectiveLine Y ↘ Y)).unit.app _ ≫
    R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).map
      (leftDerivedUpperStarTateShiftIso Λ (ProjectiveLine Y ↘ Y) 1).hom

/-- The decomposition map `(1, h) : Λ_Y(1)[2] ⊕ Λ_Y ⟶ Rq_* Λ(1)[2]` of the projective line: the
pullback on the first summand and the hyperplane class on the second. -/
noncomputable def projectiveLineDecomposition :
    (tateObject Λ Y 1)⟦(2 : ℤ)⟧ ⊞ constantComplex Λ Y ⟶
      R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ (ProjectiveLine Y) 1)⟦(2 : ℤ)⟧) :=
  biprod.desc (projectiveLinePullback Λ Y) (projectiveLineHyperplaneClass Λ Y)

/-- Blueprint `thm-amb-p1-decomposition`: the projective-line decomposition

For `q : ℙ¹_Y ⟶ Y` and `h = c₁(𝒪(1))`, the map

`(1, h) : Λ_Y(1)[2] ⊕ Λ_Y ⟶ Rq_* Λ_{ℙ¹}(1)[2]`

is an isomorphism (twisted by `(1)[2]`, this is `Λ_Y ⊕ Λ_Y(-1)[-2] ≅ Rq_* Λ_{ℙ¹}`): on a
geometric fibre the cohomology of `ℙ¹` is free of rank one in degrees `0` and `2`, the class of
`𝒪(1)` generating `H²`, and proper base change concludes. Here `h` is realized as the class of
the divisor `[0 : 1]` (`AlgebraicGeometry.Etale.projectiveLineHyperplaneClass`), whose
normalization is the rank-one normalization of the Kummer classes. -/
theorem isIso_projectiveLineDecomposition [HasKummerClass.IsNormalized Λ]
    [HasInvertibleExponent Λ Y] :
    IsIso (projectiveLineDecomposition Λ Y) :=
  sorry

variable [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ Y]

/-- Blueprint `def-amb-p1-trace`: the projective-line trace

The *trace* `t_q : Rq_* Λ(1)[2] ⟶ Λ_Y` of the projective line `q : ℙ¹_Y ⟶ Y`: the projection
onto the second summand of the decomposition `Rq_* Λ(1)[2] ≅ Λ_Y(1)[2] ⊕ Λ_Y`
(`AlgebraicGeometry.Etale.isIso_projectiveLineDecomposition`). Thus `t_q(h) = 1`. -/
noncomputable def projectiveLineTrace :
    R((ProjectiveLine Y ↘ Y)_*[ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ (ProjectiveLine Y) 1)⟦(2 : ℤ)⟧) ⟶ constantComplex Λ Y :=
  have := isIso_projectiveLineDecomposition Λ Y
  inv (projectiveLineDecomposition Λ Y) ≫ biprod.snd

/-- The trace is normalized by the hyperplane class: `t_q(h) = 1`. -/
@[reassoc (attr := simp)]
lemma projectiveLineHyperplaneClass_projectiveLineTrace :
    projectiveLineHyperplaneClass Λ Y ≫ projectiveLineTrace Λ Y = 𝟙 _ := by
  have := isIso_projectiveLineDecomposition Λ Y
  rw [projectiveLineTrace, ← biprod.inr_desc (projectiveLinePullback Λ Y)
    (projectiveLineHyperplaneClass Λ Y), Category.assoc, ← projectiveLineDecomposition,
    IsIso.hom_inv_id_assoc, biprod.inr_snd]

/-- The trace kills the classes pulled back from the base. -/
@[reassoc (attr := simp)]
lemma projectiveLinePullback_projectiveLineTrace :
    projectiveLinePullback Λ Y ≫ projectiveLineTrace Λ Y = 0 := by
  have := isIso_projectiveLineDecomposition Λ Y
  rw [projectiveLineTrace, ← biprod.inl_desc (projectiveLinePullback Λ Y)
    (projectiveLineHyperplaneClass Λ Y), Category.assoc, ← projectiveLineDecomposition,
    IsIso.hom_inv_id_assoc, biprod.inl_snd]

/-- The *integration map* `∫_p : Rp_! Λ(1)[2] = Rq_* j_! Λ(1)[2] ⟶ Rq_* Λ(1)[2] ⟶ Λ_Y` of the
affine line `p : 𝔸¹_Y ⟶ Y`: the restriction of the projective-line trace
(`AlgebraicGeometry.Etale.projectiveLineTrace`) along the forget-supports map of the standard
compactification. -/
noncomputable def affineLineTrace :
    (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧) ⟶ constantComplex Λ Y :=
  affineLineForgetSupports Λ Y ≫ projectiveLineTrace Λ Y

/-- The integration map of the affine line sends the class of the zero section to `1`:
`∫_p σ_p = 1`, that is, `t_q(h) = 1`. -/
@[reassoc (attr := simp)]
lemma affineLineZeroClass_affineLineTrace :
    affineLineZeroClass Λ Y ≫ affineLineTrace Λ Y = 𝟙 _ := by
  rw [affineLineTrace, ← Category.assoc, ← projectiveLineHyperplaneClass,
    projectiveLineHyperplaneClass_projectiveLineTrace]

end Trace

end Etale

end AlgebraicGeometry
