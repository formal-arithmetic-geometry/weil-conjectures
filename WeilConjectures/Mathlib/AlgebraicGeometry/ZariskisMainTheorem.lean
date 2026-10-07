/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Zariski's Main Theorem: the finite factorization

Mathlib's `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` proves Grothendieck's form of
Zariski's Main Theorem: a separated, quasi-compact, locally quasi-finite morphism `f : X ⟶ S`
locally of finite type factors as an open immersion into the relative normalization of `S` in
`X` followed by an integral morphism. Over a quasi-compact quasi-separated base we deduce the
factorization through a *finite* `S`-scheme (Stacks Project Tag 05K0), by writing the relative
normalization as a cofiltered limit of finite `S`-schemes and descending the open immersion to
a finite stage.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.FiniteApproximation`: a presentation of `f : X ⟶ S` as a
  cofiltered limit of finite `S`-schemes.

## Main results

- `AlgebraicGeometry.Scheme.Hom.exists_finiteApproximation_of_isIntegralHom`: an integral
  morphism to a qcqs scheme is a limit of finite morphisms of finite presentation
  (Stacks Project Tag 09YZ).
- `AlgebraicGeometry.Scheme.Hom.FiniteApproximation.exists_isOpenImmersion_isClosedImmersion`:
  a quasi-compact open of such a limit is open in a closed subscheme of some stage
  (blueprint `thm-pqf-immersion-descent`).
- `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite`:
  **Zariski's Main Theorem**, finite factorization (Stacks Project Tag 05K0; blueprint
  `thm-pqf-zmt-factorization`).

## Blueprint

This file formalises part (i) of `sk-prop-nagata-sketch-zmt`. The refinement for morphisms
locally of finite presentation is
`AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A **finite approximation** of a morphism `f : X ⟶ S` is a cofiltered system `D` of
schemes finite over `S` together with a limit cone with point `X` whose projections are
compatible with `f`: it presents `X` as a cofiltered limit of finite `S`-schemes. The transition
morphisms are then affine (`Scheme.Hom.FiniteApproximation.isAffineHom_map`).

An integral morphism to a quasi-compact quasi-separated scheme admits one, with stages of
finite presentation (`Scheme.Hom.exists_finiteApproximation_of_isIntegralHom`, Stacks Project
Tag 09YZ). This is the "finite approximation tail" of the proof of blueprint
`thm-pqf-zmt-factorization`. -/
structure Scheme.Hom.FiniteApproximation {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The index category of the inverse system. -/
  I : Type u
  /-- The category structure on the index type. -/
  [smallCategory : SmallCategory I]
  /-- The index category is cofiltered. -/
  [isCofiltered : IsCofiltered I]
  /-- The diagram of finite `S`-schemes. -/
  D : I ⥤ Scheme.{u}
  /-- The structure morphisms of the stages to `S`. -/
  p (i : I) : D.obj i ⟶ S
  /-- The transition morphisms are `S`-morphisms. -/
  map_p {i j : I} (g : i ⟶ j) : D.map g ≫ p j = p i
  /-- Every stage is finite over `S`. -/
  isFinite_p (i : I) : IsFinite (p i)
  /-- The morphisms from `X` to the stages. -/
  π : (Functor.const I).obj X ⟶ D
  /-- `X` is the limit of the stages. -/
  isLimit : IsLimit (Cone.mk X π)
  /-- The morphisms from `X` to the stages are compatible with `f`. -/
  π_p (i : I) : π.app i ≫ p i = f

namespace Scheme.Hom.FiniteApproximation

attribute [instance] smallCategory isCofiltered isFinite_p

variable {X S : Scheme.{u}} {f : X ⟶ S} (F : f.FiniteApproximation)

/-- The transition morphisms of a finite approximation are affine. -/
instance isAffineHom_map {i j : F.I} (g : i ⟶ j) : IsAffineHom (F.D.map g) := by
  have : IsAffineHom (F.D.map g ≫ F.p j) := by rw [F.map_p]; infer_instance
  exact IsAffineHom.of_comp _ (F.p j)

instance compactSpace_obj [CompactSpace S] (i : F.I) : CompactSpace (F.D.obj i) :=
  QuasiCompact.compactSpace_of_compactSpace (F.p i)

instance quasiSeparatedSpace_obj [QuasiSeparatedSpace S] (i : F.I) :
    QuasiSeparatedSpace (F.D.obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (F.p i)

end Scheme.Hom.FiniteApproximation

/-- **An integral morphism is a limit of finite morphisms of finite presentation** (Stacks
Project Tag 09YZ). If `f : X ⟶ S` is integral and `S` is quasi-compact and quasi-separated,
then `X` is a cofiltered limit of schemes finite and of finite presentation over `S`.

This is Step 2 ("the finite approximation tail") of the proof of blueprint
`thm-pqf-zmt-factorization`: `f_* 𝒪_X` is the filtered union of its finite quasi-coherent
subalgebras. -/
@[stacks 09YZ]
theorem Scheme.Hom.exists_finiteApproximation_of_isIntegralHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegralHom f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ F : f.FiniteApproximation, ∀ i, LocallyOfFinitePresentation (F.p i) :=
  sorry

/-- **Descent of the immersion to a finite stage** (blueprint `thm-pqf-immersion-descent`).
Let `ν : N ⟶ S` be presented as a cofiltered limit of finite `S`-schemes `T_λ`, with `S`
quasi-compact and quasi-separated, and let `ι : X ⟶ N` be a quasi-compact open immersion with
`X` locally of finite type over `S`. Then there are an index `λ₀` and a factorization
`X ⟶ T ⟶ T_{λ₀}` of `X ⟶ N ⟶ T_{λ₀}` into a quasi-compact open immersion followed by a closed
immersion. If `S` is locally Noetherian, `T_{λ₀}` is moreover of finite presentation over `S`.

The image of `X` descends to a quasi-compact open `U` of some stage (Stacks Project Tag 01Z4),
`X ⟶ U` is a closed immersion from some stage on (Tag 081B), and the quasi-compact immersion
`X ⟶ U ⟶ T_{λ₀}` factors through its scheme-theoretic image (Tag 01QV). -/
theorem Scheme.Hom.FiniteApproximation.exists_isOpenImmersion_isClosedImmersion
    {X N S : Scheme.{u}} {ν : N ⟶ S} (F : ν.FiniteApproximation) [CompactSpace S]
    [QuasiSeparatedSpace S] (ι : X ⟶ N) [IsOpenImmersion ι] [QuasiCompact ι]
    [LocallyOfFiniteType (ι ≫ ν)] :
    ∃ (i : F.I) (T : Scheme.{u}) (j : X ⟶ T) (k : T ⟶ F.D.obj i), IsOpenImmersion j ∧
      QuasiCompact j ∧ IsClosedImmersion k ∧ j ≫ k = ι ≫ F.π.app i ∧
      (IsLocallyNoetherian S → LocallyOfFinitePresentation (F.p i)) := by
  have : CompactSpace N := Scheme.compactSpace_of_isLimit F.D _ F.isLimit
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace ι
  have (i : F.I) : LocallyOfFiniteType (ι ≫ (Cone.mk N F.π).π.app i ≫ F.p i) := by
    change LocallyOfFiniteType (ι ≫ F.π.app i ≫ F.p i)
    rw [F.π_p]; infer_instance
  obtain ⟨i, U, g, hU, hg, hgU⟩ :=
    Scheme.exists_isClosedImmersion_of_isOpenImmersion_of_isLimit F.isLimit F.p ι
  have : QuasiCompact U.ι := U.quasiCompact_ι hU
  let h := g ≫ U.ι
  have : QuasiCompact h.toImage := QuasiCompact.of_comp h.toImage h.imageι
  refine ⟨i, h.image, h.toImage, h.imageι, inferInstance, inferInstance, inferInstance, ?_,
    fun _ ↦ inferInstance⟩
  rw [Scheme.Hom.toImage_imageι]
  exact hgU

/-- **Zariski's Main Theorem, finite factorization** (Stacks Project Tag 05K0; blueprint
`thm-pqf-zmt-factorization`, statement (i) of blueprint `sk-prop-nagata-sketch-zmt`). A
separated, quasi-compact, locally quasi-finite morphism `f : X ⟶ S` locally of finite type to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion `j : X ⟶ T`
followed by a finite morphism `p : T ⟶ S`.

By Grothendieck's form of Zariski's Main Theorem, `X` is a quasi-compact open of the relative
normalization of `S` in `X`, which is integral over `S` and hence a limit of finite
`S`-schemes (Tag 09YZ); the immersion descends to a finite stage
(`Scheme.Hom.FiniteApproximation.exists_isOpenImmersion_isClosedImmersion`). -/
@[stacks 05K0]
theorem Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f]
    [QuasiCompact f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsFinite p ∧ j ≫ p = f := by
  obtain ⟨F, -⟩ := f.fromNormalization.exists_finiteApproximation_of_isIntegralHom
  have : LocallyOfFiniteType (f.toNormalization ≫ f.fromNormalization) := by
    rw [f.toNormalization_fromNormalization]; infer_instance
  obtain ⟨i, T, j, k, hj, hjc, hk, hjk, -⟩ := F.exists_isOpenImmersion_isClosedImmersion
    f.toNormalization
  refine ⟨T, j, k ≫ F.p i, hj, hjc, inferInstance, ?_⟩
  rw [reassoc_of% hjk, F.π_p, f.toNormalization_fromNormalization]

end AlgebraicGeometry
