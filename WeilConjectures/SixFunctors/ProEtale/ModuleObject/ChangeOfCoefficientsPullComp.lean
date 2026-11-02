/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull

/-!

# Compatibility of the derived (Pull) isomorphisms with composition

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and write `T` for the derived
extension of scalars along `a`. This file states the compatibility of the derived (Pull)
isomorphisms `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso a h`, from
`Lh^*_Λ ⋙ T` to `T ⋙ Lh^*_Λ'`, with the composition isomorphisms of derived pullbacks
(`ProEtale.CondensedRing.DerivedUpperStarExtendScalarsIsoCompCoherence`), and defines their mates
`Rh_*^Λ ⋙ T ⟶ T ⋙ Rh_*^Λ'` (`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The isomorphisms `derivedUpperStarExtendScalarsIso a : Lh^*_Λ ⋙ T ≅ T ⋙ Lh^*_Λ'` are
compatible with the composition isomorphisms `L(p ≫ q)^* ≅ Lq^* ⋙ Lp^*` along `p` and `q`:
for every `M`,
```
T L(p ≫ q)^* M ⟶ L(p ≫ q)^* T M ⟶ Lp^* Lq^* T M
  = T L(p ≫ q)^* M ⟶ T Lp^* Lq^* M ⟶ Lp^* T Lq^* M ⟶ Lp^* Lq^* T M.
```
-/
def DerivedUpperStarExtendScalarsIsoCompCoherenceAt {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) : Prop :=
  ∀ M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
    (derivedUpperStarExtendScalarsIso a (p ≫ q)).hom.app M ≫
        (leftDerivedUpperStarComp Λ' p q).hom.app
          ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.obj M) =
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
          ((leftDerivedUpperStarComp Λ p q).hom.app M) ≫
        (derivedUpperStarExtendScalarsIso a p).hom.app ((q)^*⟦Λ⟧.leftDerivedFunctor.obj M) ≫
        (p)^*⟦Λ'⟧.leftDerivedFunctor.map ((derivedUpperStarExtendScalarsIso a q).hom.app M)

/-- The compatibility `DerivedUpperStarExtendScalarsIsoCompCoherenceAt a p q` for all composable
morphisms `p` and `q` of schemes. -/
def DerivedUpperStarExtendScalarsIsoCompCoherence : Prop :=
  ∀ ⦃X Y Z : Scheme.{u}⦄ (p : X ⟶ Y) (q : Y ⟶ Z),
    DerivedUpperStarExtendScalarsIsoCompCoherenceAt a p q

/-- The comparison `Rh_*^Λ ⋙ T ⟶ T ⋙ Rh_*^Λ'` between the derived pushforwards and the derived
extensions of scalars along an arbitrary coefficient change: the mate of the inverse of
`derivedUpperStarExtendScalarsIso a h` along the derived adjunctions `Lh^* ⊣ Rh_*`. -/
noncomputable def derivedUpperStarExtendScalarsPushHom {X Y : Scheme.{u}} (h : X ⟶ Y) :
    R((h)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R((h)_*⟦Λ'⟧) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ h) (derivedUpperStarLowerStarAdjunction Λ' h)
    (derivedUpperStarExtendScalarsIso a h).inv).natTrans

end AlgebraicGeometry.ProEtale.CondensedRing
