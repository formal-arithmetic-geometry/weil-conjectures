/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat

/-!
# Right derived functors and coproducts of uniformly bounded below complexes

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, where `C` has
enough injectives. If `F` commutes with coproducts of shape `J` and coproducts of shape `J` of
`F`-acyclic objects are `F`-acyclic, then the unbounded right derived functor
`RF : D(C) ⥤ D(D)` commutes with coproducts of families `K : J → D(C)` which are *uniformly*
bounded below, i.e. all `K j` are in `D^{≥ a}` for a common `a`
(`CategoryTheory.Functor.preservesColimit_discrete_rightDerivedFunctor_of_isGE`). This holds in
particular when all the classical right derived functors `RᵠF` commute with coproducts of
shape `J`
(`CategoryTheory.Functor.preservesColimit_discrete_rightDerivedFunctor_of_isGE_of_rightDerived`).

Indeed, choose for each `K j` a representative `E j` which is a complex of injective objects
strictly concentrated in degrees `≥ a`. The coproduct `∐ E j` of complexes is a coproduct in
`D(C)` (`DerivedCategory.isColimitCofanMkQObj`), and it is a complex of `F`-acyclic objects
strictly concentrated in degrees `≥ a`, so that `RF` is computed by applying `F` termwise on it
(`CategoryTheory.Functor.isIso_rightDerivedFunctorUnitQ_of_isStrictlyGE`), as well as on the
`E j`. Hence `RF(∐ E j) ≅ F(∐ E j) ≅ ∐ F(E j) ≅ ∐ RF(E j)`.

This is the bounded below analogue of
`CategoryTheory.Functor.preservesColimitsOfShape_rightDerivedFunctor`, where finite
cohomological dimension of `F` replaces the uniform lower bound.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C] [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- **Right derived functors commute with coproducts of uniformly bounded below complexes of
injectives.** Let `F` commute with coproducts of shape `J`, coproducts of shape `J` of `F`-acyclic
objects being `F`-acyclic. For a family `E` of complexes of injective objects which are strictly
concentrated in degrees `≥ a`, the right derived functor `RF` preserves the coproduct of the
`Q(E j)`: `RF` is computed by applying `F` termwise on the `E j` and on `∐ E j`. -/
theorem preservesColimit_discrete_rightDerivedFunctor_of_isStrictlyGE {J : Type*}
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) D]
    [PreservesColimitsOfShape (Discrete J) F]
    (hJ : ∀ X : J → C, (∀ j, F.rightAcyclic (X j)) → F.rightAcyclic (∐ X))
    (E : J → CochainComplex C ℤ) (a : ℤ) [∀ j, (E j).IsStrictlyGE a]
    (hE : ∀ j n, Injective ((E j).X n)) :
    PreservesColimit (Discrete.functor fun j ↦ DerivedCategory.Q.obj (E j))
      F.rightDerivedFunctor := by
  have (j : J) : (E j).IsKInjective :=
    have := hE j
    CochainComplex.isKInjective_of_injective (E j) a
  have heval (n : ℤ) : (∐ E).X n ≅ ∐ fun j ↦ (E j).X n :=
    PreservesCoproduct.iso (HomologicalComplex.eval C (.up ℤ) n) E
  have : (∐ E).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    refine IsZero.of_iso ?_ (heval n)
    exact (coproductIsCoproduct fun j ↦ (E j).X n).isZero_pt
      (Functor.isZero _ fun j ↦ (E j.as).isZero_of_isStrictlyGE a n hn)
  have hu (j : J) : IsIso (F.rightDerivedFunctorUnitQ (E j)) :=
    F.isIso_rightDerivedFunctorUnitQ_of_isStrictlyGE _ a fun n ↦
      have := hE j n
      rightAcyclic_of_injective _
  have huP : IsIso (F.rightDerivedFunctorUnitQ (∐ E)) :=
    F.isIso_rightDerivedFunctorUnitQ_of_isStrictlyGE _ a fun n ↦
      F.rightAcyclic.prop_of_iso (heval n).symm (hJ _ fun j ↦
        have := hE j n
        rightAcyclic_of_injective _)
  -- the image under `F` of the coproduct cofan is a coproduct in `D(D)`
  have hFc : IsColimit (Cofan.mk (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj (∐ E)))
      fun j ↦ DerivedCategory.Q.map ((F.mapHomologicalComplex _).map (Sigma.ι E j))) :=
    DerivedCategory.isColimitCofanMkQObj
      ((isColimitMapCoconeCofanMkEquiv (F.mapHomologicalComplex (.up ℤ)) E (Sigma.ι E)).1
        (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) (coproductIsCoproduct E)))
  refine preservesColimit_of_preserves_colimit_cocone
    (DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct E))
    ((isColimitMapCoconeCofanMkEquiv _ _ _).2 ?_)
  refine (IsColimit.equivOfNatIsoOfIso
    (Discrete.natIso fun j ↦ asIso (F.rightDerivedFunctorUnitQ (E j.as))) _ _
    (Cocone.ext (asIso (F.rightDerivedFunctorUnitQ (∐ E))) fun j ↦ ?_)) hFc
  dsimp
  rw [Category.assoc, rightDerivedFunctorUnitQ_naturality]
  simp

/-- **Right derived functors commute with uniformly bounded below coproducts.** Let `F` commute
with coproducts of shape `J`, coproducts of shape `J` of `F`-acyclic objects being `F`-acyclic.
Then `RF` preserves the coproduct of a family `K : J → D(C)` such that all `K j` are in
`D^{≥ a}`, for a common `a`: each `K j` is represented by a complex of injective objects strictly
concentrated in degrees `≥ a`
(`CategoryTheory.Functor.preservesColimit_discrete_rightDerivedFunctor_of_isStrictlyGE`). -/
theorem preservesColimit_discrete_rightDerivedFunctor_of_isGE {J : Type*}
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) D]
    [PreservesColimitsOfShape (Discrete J) F]
    (hJ : ∀ X : J → C, (∀ j, F.rightAcyclic (X j)) → F.rightAcyclic (∐ X))
    (K : J → DerivedCategory C) (a : ℤ) (hK : ∀ j, (K j).IsGE a) :
    PreservesColimit (Discrete.functor K) F.rightDerivedFunctor := by
  have representative (j : J) : ∃ E : CochainComplex C ℤ,
      E.IsStrictlyGE a ∧ (∀ n, Injective (E.X n)) ∧
        Nonempty (DerivedCategory.Q.obj E ≅ K j) := by
    have := hK j
    obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE (K j) a
    obtain ⟨E, φ, hφ, hE, hEa⟩ :=
      CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L a
    have : QuasiIso φ := hφ
    exact ⟨E, hEa, hE, ⟨(asIso (DerivedCategory.Q.map φ)).symm ≪≫ e.symm⟩⟩
  choose E hEa hE e using representative
  have := hEa
  have := F.preservesColimit_discrete_rightDerivedFunctor_of_isStrictlyGE hJ E a hE
  exact preservesColimit_of_iso_diagram _
    (K₁ := Discrete.functor fun j ↦ DerivedCategory.Q.obj (E j))
    (Discrete.natIso fun j ↦ (e j.as).some)

/-- **Right derived functors commute with uniformly bounded below coproducts**, when all the
classical right derived functors `RᵠF` commute with coproducts of shape `J`: `R⁰F ≅ F` commutes
with them, and a coproduct of `F`-acyclic objects is `F`-acyclic
(`CategoryTheory.Functor.preservesColimit_discrete_rightDerivedFunctor_of_isGE`). -/
theorem preservesColimit_discrete_rightDerivedFunctor_of_isGE_of_rightDerived {J : Type*}
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) D]
    (hJ : ∀ q, PreservesColimitsOfShape (Discrete J) (F.rightDerived q))
    (K : J → DerivedCategory C) (a : ℤ) (hK : ∀ j, (K j).IsGE a) :
    PreservesColimit (Discrete.functor K) F.rightDerivedFunctor :=
  have : PreservesColimitsOfShape (Discrete J) F :=
    have := hJ 0
    preservesColimitsOfShape_of_natIso F.rightDerivedZeroIsoSelf
  F.preservesColimit_discrete_rightDerivedFunctor_of_isGE (fun X hX q ↦
    have := hJ (q + 1)
    IsZero.of_iso ((IsZero.iff_id_eq_zero _).2
        (Sigma.hom_ext _ _ fun j ↦ (hX j q).eq_of_src _ _))
      (PreservesCoproduct.iso (F.rightDerived (q + 1)) X)) K a hK

end CategoryTheory.Functor
