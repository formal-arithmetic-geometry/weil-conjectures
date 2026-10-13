/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
import Sheaf.AlgebraicGeometry.SingleComplexTensorStalkCoordinates

/-! # Tensor inheritance of the single-complex base-change condition

Source: Stacks Project, perfect.tex, Tag 0DJA, part (1)
(blueprint: lem-pc-rf-single-complex-inherited-tensor-condition).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Tensoring a map satisfying the single-complex stalkwise base-change condition by an
arbitrary quasi-coherent derived object preserves that condition. The comparison is the
canonical derived pullback tensor map, pinned on K-flat representatives by the module
pullback tensor map and the shared left-derived counit.
Source: Stacks Project, perfect.tex, Tag 0DJA, part (1).  Proof: at a stalk, apply the
transitivity of derived tensor products to the stalk of `E` and the assumed comparison for
`K`; the stalk ring of the fibre product is a localization, hence flat, so cohomology commutes
with the final scalar extension.  This is exactly the local computation in the node proof,
using the localized module tensor inheritance and the stalk coordinate comparison.
(blueprint: lem-pc-rf-single-complex-inherited-tensor-condition). -/
theorem singleComplexInheritedTensorCondition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S)
    (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : schemeDerivedQCohCategory X) (K' : schemeDerivedQCohCategory X')
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K.obj K'.obj φ)
    (τ : ∀ E L : schemeDerivedCategory X,
      (derivedPullback g').obj (E ⊗ L) ⟶
        (derivedPullback g').obj E ⊗ (derivedPullback g').obj L)
    (hτ : IsCanonicalPullbackTensorComparison g' τ) :
    Nonempty (Functor.Monoidal (derivedPullback g')) ∧
    ∀ E : schemeDerivedQCohCategory X,
      SingleComplexBaseChange.StalkCondition f f' g g' sq
        (E.obj ⊗ K.obj) (((derivedPullback g').obj E.obj) ⊗ K'.obj)
        (τ E.obj K.obj ≫
          ((derivedPullback g').obj E.obj ◁ φ)) := by
  obtain ⟨m, _⟩ := exists_derivedPullbackMonoidalModel g'
  refine ⟨⟨m.toMonoidal⟩, ?_⟩
  intro E c z i
  let _ := SingleComplexBaseChange.leftAlgebra f g' z
  let _ := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let _ := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let _ := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
  let _ := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
  obtain ⟨d, Q, hflat, hQ, hP, γ, hγ, hcomparison⟩ :=
    SingleComplexBaseChange.singleComplex_tensor_stalk_coordinates
      f f' g g' sq τ hτ E K K' φ c z
  let P := SingleComplexBaseChange.stalkComplex g' z d.P
  let N := ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
    (.up ℤ)).obj d.N
  let t := (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z d.P).hom ≫
    ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)).map d.t
  have hinput : ∀ j : ℤ, IsIso (ModuleCat.localizedTensorComparison
      (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g' z)
      (SingleComplexBaseChange.B f' z) (SingleComplexBaseChange.C z)
      (SingleComplexBaseChange.cohomologyModel f f' g g' sq z d.P) t j) := by
    intro j
    simpa only [ModuleCat.localizedTensorComparison, t,
      HomologicalComplex.homologyMap_comp, Category.assoc,
      SingleComplexBaseChange.stalkComparison] using h_stalk d z j
  have htensor := ModuleCat.localizedTensorComparison_inheritance
    (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g' z)
    (SingleComplexBaseChange.B f' z) (SingleComplexBaseChange.C z)
    hflat Q P hQ hP N t γ hγ
    (SingleComplexBaseChange.cohomologyModel f f' g g' sq z d.P)
    (ModuleCat.baseDerivedTensorCohomologyModel
      (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g' z)
      (SingleComplexBaseChange.B f' z)
      (CochainComplex.mapBifunctor Q P (curriedTensor _))
      (SingleComplexBaseChange.C z)) hinput i
  obtain ⟨a, b, hab⟩ := hcomparison i
  rw [hab]
  exact IsIso.comp_isIso

end AlgebraicGeometry
