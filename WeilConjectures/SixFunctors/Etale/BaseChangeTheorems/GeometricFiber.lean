/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProperTorsion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# The geometric fibre formula for proper morphisms

Let `f : X ⟶ Y` be a proper morphism and `ȳ : Spec Ω ⟶ Y` a geometric point, `Ω` separably
closed. Form the geometric fibre

```
X_ȳ --i--> X
 |         |
 a         f
 v         v
Spec Ω --ȳ--> Y
```

(`X_ȳ = pullback f ȳ`, `i = pullback.fst f ȳ`, `a = pullback.snd f ȳ`). Specialising proper base
change to this square gives:

- for a finite coefficient ring `Λ`, the base change morphism `ȳ^* Rf_* K ⟶ Ra_* i^* K` is an
  isomorphism for every `K ∈ D⁺(X_ét, Λ)`
  (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_geometricFiber`);
- for a torsion sheaf `F` — in particular every sheaf of modules over a finite ring — the stalk
  of `Rᵠf_* F` at `ȳ` is the stalk of `Rᵠa_* (F|_{X_ȳ})` at the tautological geometric point
  of `Spec Ω` (`AlgebraicGeometry.Etale.sheafFiberHigherDirectImageGeometricFiberIso`).

The étale site of `Spec Ω` has only split covers, so taking the stalk at its tautological point
is the global sections functor, and the stalk of `Rᵠa_* G` there is the étale cohomology
`Hᵠ(X_ȳ, G)` of the geometric fibre. The comparison of this derived-category description of
`Hᵠ(X_ȳ, G)` with the `Ext`-description `CategoryTheory.Sheaf.H` is not formalised here (see
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine` for
the same gap).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

omit [IsSepClosed Ω] in
/-- **Finite-coefficient geometric fibre formula, derived form**: for a proper morphism
`f : X ⟶ Y`, a geometric point `ȳ : Spec Ω ⟶ Y` and a finite coefficient ring `Λ`, the base
change morphism `ȳ^* Rf_* K ⟶ Ra_{ȳ,*} i_ȳ^* K` of the geometric fibre square is an isomorphism
for every `K ∈ D⁺(X_ét, Λ)`.
This is blueprint `cor-weil-pbc-geometric-fiber-finite` (first assertion). -/
theorem Etale.isIso_derivedBaseChangeMapPlus_geometricFiber [Finite Λ] :
    IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback f y).toCommSq) :=
  Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite
    (IsPullback.of_hasPullback f y)

/-- **Finite-coefficient geometric fibre formula, stalk form**: for a proper morphism
`f : X ⟶ Y`, a geometric point `ȳ : Spec Ω ⟶ Y`, a torsion sheaf `F` of `Λ`-modules on `X_ét`
(e.g. any sheaf of modules over a finite ring `Λ`) and `q ∈ ℤ`, the stalk of `Rᵠf_* F` at `ȳ`
is isomorphic to the stalk at the tautological geometric point of `Spec Ω` of `Rᵠa_* (i^* F)`,
the `q`-th cohomology of the restriction of `F` to the geometric fibre `X_ȳ`. The isomorphism is
the stalk at `ȳ` of the degree-`q` exchange map of the geometric fibre square
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isProper_of_isTorsionSheaf`), composed
with `(ȳ^* G)_{Spec Ω} ≅ G_ȳ` (`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`).
This is blueprint `cor-weil-pbc-geometric-fiber-finite` (second assertion). -/
noncomputable def Etale.sheafFiberHigherDirectImageGeometricFiberIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionModuleSheaf F] (q : ℤ) :
    (pointSmallEtale y).sheafFiber.obj (Etale.higherDirectImage Λ f q F) ≅
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj
        (Etale.higherDirectImage Λ (pullback.snd f y) q
          ((pullback.fst f y)^*[ModuleCat.{u + 1} Λ].obj F)) :=
  have := Etale.isIso_baseChangeHomologyMap_of_isProper_of_isTorsionSheaf Λ
    (IsPullback.of_hasPullback f y) F q
  eqToIso (by rw [Category.id_comp]; rfl) ≪≫
    ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) y (𝟙 _)).app _).symm ≪≫
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.mapIso
      ((Etale.baseChangeSourceFunctorIso Λ y f q).app F).symm ≪≫
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.mapIso
      (asIso (Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback f y) q F)) ≪≫
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.mapIso
      ((Etale.baseChangeTargetFunctorIso Λ (pullback.fst f y) (pullback.snd f y) q).app F)

end AlgebraicGeometry
