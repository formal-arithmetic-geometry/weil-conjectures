/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluation
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.LocalTensorFiniteFreeZeroModel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties

/-! # Local models of augmented self-Ext/self-Tor resolutions

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 068C](https://stacks.math.columbia.edu/tag/068C)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Local zero-differential models for the pullback of an augmented K-flat resolution,
and K-injectivity for the restriction of an augmented K-injective resolution. -/
theorem selfExt_tor_resolution_local
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ) (J : CochainComplex Z.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (b : (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
      (SheafOfModules.unit Z.ringCatSheaf) ⟶ J)
    (_hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a)
    (_hflat : ∀ k : ℤ, SheafOfModules.IsFlat (P.X k))
    (_hb : QuasiIso b) (_hJ : J.IsKInjective) :
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    ∀ (V : Z.Opens) (U : Y.affineOpens)
      (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f),
      let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
      let Fc := moduleOpenOverComplexFunctor Z V W
      CochainComplex.IsKInjective (Fc.obj J) ∧
        HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W) (Fc.obj T) := by
  dsimp
  intro V U hU
  let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
  constructor
  · let := _hJ
    let F := Scheme.Modules.restrictFunctor V.ι
    let G := SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    let : F.Additive := inferInstance
    let : F.PreservesKInjectiveComplexes :=
      (openImmersion_restriction_derived_properties V.ι).2
    let Jv : CochainComplex V.toScheme.Modules ℤ := (F.mapHomologicalComplex (.up ℤ)).obj J
    let : CochainComplex.IsKInjective Jv := Functor.PreservesKInjectiveComplexes.isKInjective_map J
    have hzero : G.PreservesZeroMorphisms := by
      constructor
      intro M N
      ext A x
      rfl
    exact isKInjective_restrict_localized V.toScheme.ringCatSheaf W
      hzero Jv
  · exact local_tensor_has_finite_free_zero_model i P a _hP _hflat V U hU

end AlgebraicGeometry
