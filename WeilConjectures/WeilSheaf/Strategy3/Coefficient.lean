/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.Pullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar

/-! # A separate coefficient interface and finite module equivalence -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

/-- Coefficient types used uniformly by the duplicate construction. -/
def coeffType (T : Type) := ULift.{u + 1} T

instance (T : Type) [CommRing T] : CommRing (coeffType.{u} T) :=
  inferInstanceAs (CommRing (ULift.{u + 1} T))

instance (T : Type) [Finite T] : Finite (coeffType.{u} T) :=
  inferInstanceAs (Finite (ULift.{u + 1} T))

/-- The condensed coefficient object, retained as a named constructor. -/
noncomputable def coeffRing (T : Type) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObj T

noncomputable instance (T : Type) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] : MonObj (coeffRing.{u} T) :=
  inferInstanceAs (MonObj (Profinite.continuousMapRingObj.{u} T))

instance (T : Type) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] : IsCommMonObj (coeffRing.{u} T) :=
  inferInstanceAs (IsCommMonObj (Profinite.continuousMapRingObj.{u} T))

/-- A constant global section typed using the duplicate coefficient object. -/
noncomputable def coeffSection (T : Type) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] (t : T) : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶
      coeffRing T :=
  (Profinite.continuousMapConstRingHom.{u} T t).hom

variable (X : Scheme.{u})

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- For a finite discrete ring `T`, the comparison `T_X ⟶ Λ_X = p_X^* T̲` from the constant ring
sheaf `T` on `X_proét` to the pullback of the condensed ring `T̲ = C(-, T)`: the composite
```
T_X ≅ π_X^* T_{Spec ℤ} ≅ π_X^* p^* T_* ≅ π_X^* p^* T̲ = p_X^* T̲
```
of the comparisons `constantSheafToUpperStarToSpecZ`, `constantSheafToPointUpperStar` for
constant sheaves and the identification `T_* ≅ T̲` of
`Profinite.constRingSheafToContinuousMapRingObj`. -/
noncomputable def constRingSheafToCondensedRingObj :
    Sheaf.constRingSheaf (Scheme.ProEt.topology X) (coeffType.{u} T) ⟶
      condensedRingObj (coeffRing T) X :=
  (constantSheafToUpperStarToSpecZ X).app (AddCommGrpCat.of (coeffType.{u} T)) ≫
    (toSpecZ X)^*[Ab.{u + 1}].map
      (constantSheafToPointUpperStar.app (AddCommGrpCat.of (coeffType.{u} T))) ≫
    (upperStarFromPoint X).map (Profinite.constRingSheafToContinuousMapRingObj T)

instance : IsIso (constRingSheafToCondensedRingObj X T) := by
  dsimp only [constRingSheafToCondensedRingObj]
  infer_instance

/-- The comparison `T_X ⟶ Λ_X` is a morphism of ring objects. -/
instance : IsMonHom (constRingSheafToCondensedRingObj X T) := by
  let R := AddCommGrpCat.of (coeffType.{u} T)
  let cX := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let cS := constantSheaf (Scheme.ProEt.topology specZ.{u}) Ab.{u + 1}
  let cP := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let π := (toSpecZ X)^*[Ab.{u + 1}]
  have hA : @IsMonHom _ _ _ _ _ (cX.monObjObj R) (π.monObjObj (cS.obj R))
      ((constantSheafToUpperStarToSpecZ X).app R) :=
    IsMonHom.of_eq _ rfl (Functor.monObjObj_comp cS π R)
      (hf := NatTrans.isMonHom_app (constantSheafToUpperStarToSpecZ X) R)
  have hB : @IsMonHom _ _ _ _ _ (cS.monObjObj R) (pointUpperStar.monObjObj (cP.obj R))
      (constantSheafToPointUpperStar.app R) :=
    IsMonHom.of_eq _ rfl (Functor.monObjObj_comp cP pointUpperStar R)
      (hf := NatTrans.isMonHom_app constantSheafToPointUpperStar R)
  have hκ : @IsMonHom _ _ _ _ _ (cP.monObjObj R) _
      (Profinite.constRingSheafToContinuousMapRingObj T) :=
    IsMonHom.of_eq _ (Functor.monObjObj_comp (Functor.const _) (presheafToSheaf _ _) R).symm rfl
  have hD : @IsMonHom _ _ _ _ _
      (π.monObjObj (pointUpperStar.obj (cP.obj R))) _
      ((upperStarFromPoint X).map (Profinite.constRingSheafToContinuousMapRingObj T)) :=
    IsMonHom.of_eq _ (Functor.monObjObj_comp pointUpperStar π (cP.obj R)) rfl
  have hC : @IsMonHom _ _ _ _ _ (π.monObjObj (cS.obj R))
      (π.monObjObj (pointUpperStar.obj (cP.obj R))) (π.map (constantSheafToPointUpperStar.app R)) :=
    @Functor.map.instIsMonHom _ _ _ _ _ _ π _ _ _ _ _ _ hB
  have : @IsMonHom _ _ _ _ _ (cX.monObjObj R) _ (constRingSheafToCondensedRingObj X T) :=
    @instIsMonHomComp _ _ _ _ _ _ (cX.monObjObj R) (π.monObjObj (cS.obj R))
      ((upperStarFromPoint X).monObjObj _) _ _ hA
      (@instIsMonHomComp _ _ _ _ _ _ (π.monObjObj (cS.obj R))
        (π.monObjObj (pointUpperStar.obj (cP.obj R))) ((upperStarFromPoint X).monObjObj _) _ _
        hC hD)
  exact IsMonHom.of_eq (h₁ := cX.monObjObj R) _
    (Functor.monObjObj_comp (Functor.const _) (presheafToSheaf _ _) R) rfl

section CommRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **The two models of pro-étale sheaves with finite coefficients agree.** For a finite
discrete commutative ring `T`, module objects over the coefficient ring `Λ_X = p_X^* T̲` in
abelian sheaves on `X_proét` are the sheaves of `T`-modules on `X_proét`: restriction of
scalars along the isomorphism of ring objects `T_X ≅ Λ_X`
(`ProEtale.constRingSheafToCondensedRingObj`), followed by the identification of modules over
the constant ring sheaf `T_X` with sheaves of `T`-modules
(`CategoryTheory.Sheaf.modConstRingSheafEquivalence`). The underlying abelian sheaf is
preserved (`ProEtale.finiteCoefficientModEquivalence_functor_comp_sheafCompose`). -/
noncomputable def finiteCoefficientModEquivalence :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coeffRing T) X) ≌
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (coeffType.{u} T)) :=
  (Mod.comapEquivalenceOfIsIso (constRingSheafToCondensedRingObj X T)).trans
    (Sheaf.modConstRingSheafEquivalence _ (coeffType.{u} T))

/-- The equivalence `finiteCoefficientModEquivalence` keeps the underlying abelian sheaf. -/
lemma finiteCoefficientModEquivalence_functor_comp_sheafCompose :
    (finiteCoefficientModEquivalence X T).functor ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u + 1} (coeffType.{u} T)) Ab.{u + 1}) =
      Mod.forget (condensedRingObj (coeffRing T) X) :=
  rfl

end CommRing


end AlgebraicGeometry.ProEtale.Strategy3
