/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.Coefficient

/-! # Independent coefficient/pullback infrastructure: FiniteRoots -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

section RootsOfUnity

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] (X : Scheme.{u})

/-- Under `finiteCoefficientModEquivalence`, the forgetful functor from module objects over
`Λ_X` corresponds to taking the underlying abelian sheaf. -/
noncomputable def finiteCoefficientModEquivalenceInverseCompForgetIso :
    (finiteCoefficientModEquivalence X T).inverse ⋙
        Mod.forget (condensedRingObj (coeffRing T) X) ≅
      sheafCompose _ (forget₂ (ModuleCat.{u + 1} (coeffType.{u} T)) Ab.{u + 1}) :=
  Functor.isoWhiskerLeft _
      (eqToIso (finiteCoefficientModEquivalence_functor_comp_sheafCompose X T).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteCoefficientModEquivalence X T).counitIso _ ≪≫
    Functor.leftUnitor _

/-- **Free modules over `Λ_X` and extension of scalars on étale sheaves commute with `ν^*`**:
`Λ_X ⊗ ν^* F ≅ ν^*(T ⊗_ℤ F)` for an étale abelian sheaf `F`, the left-hand side read as a
pro-étale sheaf of `T`-modules. Both functors are left adjoint to the functor taking a pro-étale
sheaf of `T`-modules to the restriction to the étale site of its underlying abelian sheaf. -/
noncomputable def comparisonUpperStarFreeIso :
    ν^*(X)[Ab.{u + 1}] ⋙ Mod.freeFunctor (condensedRingObj (coeffRing T) X) ⋙
        (finiteCoefficientModEquivalence X T).functor ≅
      Etale.extendScalars (coeffType.{u} T) X ⋙
        ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} T)] :=
  (((comparisonAdjunction Ab.{u + 1} X).comp
    (Mod.freeForgetAdjunction (condensedRingObj (coeffRing T) X))).comp
      (finiteCoefficientModEquivalence X T).toAdjunction).leftAdjointUniq
    (((Etale.extendScalarsAdjunction (coeffType.{u} T) X).comp
      (comparisonAdjunction _ X)).ofNatIsoRight
      ((NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
        Functor.isoWhiskerRight (finiteCoefficientModEquivalenceInverseCompForgetIso T X).symm
          ν_*(X)[Ab.{u + 1}]))

end RootsOfUnity


variable (X : Scheme.{u}) (N : ℕ)

noncomputable def finiteCoefficientModEquivalenceFreeRootsOfUnityIso (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T]
    (hN : 0 < N) (hX : IsUnit (N : Γ(X, ⊤))) :
    (finiteCoefficientModEquivalence X T).functor.obj
        ((Mod.freeFunctor (condensedRingObj (coeffRing T) X)).obj
          (rootsOfUnitySheaf X N)) ≅
      ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} T)].obj
        ((Etale.extendScalars (coeffType.{u} T) X).obj (X.rootsOfUnitySheaf N)) :=
  (finiteCoefficientModEquivalence X T).functor.mapIso
      ((Mod.freeFunctor _).mapIso (comparisonUpperStarRootsOfUnityIso X N hN hX).symm) ≪≫
    (comparisonUpperStarFreeIso T X).app (X.rootsOfUnitySheaf N)

end AlgebraicGeometry.ProEtale.Strategy3
