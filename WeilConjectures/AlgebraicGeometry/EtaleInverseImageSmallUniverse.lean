/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Étale inverse image preserves small coefficient universes

## References

* Stacks Project, Tags 03Q1, 03PU and 03PT
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem ulift_fiber_small {X : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{u} X.smallEtaleTopology)
    (G : Sheaf X.smallEtaleTopology (Type u)) :
    Small.{u} (Φ.sheafFiber.obj
      ((sheafCompose X.smallEtaleTopology uliftFunctor.{u + 1, u}).obj G)) := by
  let e := (Φ.sheafFiberCompIso uliftFunctor.{u + 1, u}).app G
  exact small_of_injective (e.toEquiv.trans Equiv.ulift).injective

private theorem pullback_fiber_small {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type u))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T) :
    Small.{u} ((pointSmallEtale s).sheafFiber.obj ((etaleSetPullback f).obj
      ((sheafCompose S.smallEtaleTopology uliftFunctor.{u + 1, u}).obj G))) := by
  let e : etaleSetPullback f ⋙ (pointSmallEtale s).sheafFiber ≅
      (pointSmallEtale (s ≫ f)).sheafFiber :=
    Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafPullbackIso f.Etale
        (Type (u + 1)) S.smallEtaleTopology T.smallEtaleTopology).symm _ ≪≫
      (GrothendieckTopology.Point.sheafFiberComapIso (pointSmallEtale s) f.Etale
        (Hom.coverPreserving_etale f) (Type (u + 1))).symm ≪≫
      GrothendieckTopology.Point.sheafFiberIso (pointSmallEtaleComapIso f s)
  let := ulift_fiber_small (pointSmallEtale (s ≫ f)) G
  exact small_of_injective (e.app _).toEquiv.injective

/-- The sections of the étale inverse image of a `u`-small sheaf, viewed in the larger universe,
form a `u`-small type (Stacks, Tags 03Q1, 03PU and 03PT). -/
theorem etale_setPullback_small {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type u)) (B : T.Etale) :
    Small.{u} ((((etaleSetPullback f).obj
      ((sheafCompose S.smallEtaleTopology uliftFunctor.{u + 1, u}).obj G)).obj.obj
        (Opposite.op B))) := by
  classical
  let Ψ : T → GrothendieckTopology.Point.{u} T.smallEtaleTopology := fun t ↦
    pointSmallEtale ((SpecToEquivOfField (SeparableClosure (T.residueField t)) _).2
      ⟨t, CommRingCat.ofHom (algebraMap (T.residueField t) _)⟩)
  let P : ObjectProperty (GrothendieckTopology.Point.{u + 1} T.smallEtaleTopology) :=
    ObjectProperty.ofObj (fun t ↦ (Ψ t).ulift.{u + 1})
  have hP : P.IsConservativeFamilyOfPoints :=
    CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.ulift.{u + 1, u} Ψ
      (isConservativeFamilyOfPoints_pointSmallEtale' T)
  let H := (etaleSetPullback f).obj
    ((sheafCompose S.smallEtaleTopology uliftFunctor.{u + 1, u}).obj G)
  let A := (T.smallEtaleTopology.uliftYoneda.{u + 1}).obj B
  let D : P.FullSubcategory → Type (u + 1) := fun Φ ↦
    Φ.obj.sheafFiber.obj A ⟶ Φ.obj.sheafFiber.obj H
  have hsmall : ∀ Φ, Small.{u} (D Φ) := by
    rintro ⟨Φ, ⟨t⟩⟩
    have hsA : Small.{u} ((Ψ t).sheafFiber.obj A) := by
      exact ulift_fiber_small (Ψ t) (T.smallEtaleTopology.yoneda.obj B)
    have hsH : Small.{u} ((Ψ t).sheafFiber.obj H) :=
      pullback_fiber_small f G _
    have hsA' : Small.{u} (((Ψ t).ulift.{u + 1}).sheafFiber.obj A) := by
      let := hsA
      exact small_of_injective (((Ψ t).uliftSheafFiberIso
        (Type (u + 1))).app A).toEquiv.injective
    have hsH' : Small.{u} (((Ψ t).ulift.{u + 1}).sheafFiber.obj H) := by
      let := hsH
      exact small_of_injective (((Ψ t).uliftSheafFiberIso
        (Type (u + 1))).app H).toEquiv.injective
    let := hsA'
    let := hsH'
    have : Small.{u} ((((Ψ t).ulift.{u + 1}).sheafFiber.obj A) →
        (((Ψ t).ulift.{u + 1}).sheafFiber.obj H)) := inferInstance
    exact small_of_injective TypeCat.homEquiv.injective
  let := hsmall
  have hh : Small.{u} (A ⟶ H) := by
    apply small_of_injective (f := fun k : A ⟶ H ↦
      (fun Φ : P.FullSubcategory ↦ Φ.obj.sheafFiber.map k))
    intro k l h
    exact (hP.jointlyFaithful (Type (u + 1))).map_injective (fun Φ ↦ congrFun h Φ)
  let := hh
  exact small_of_injective
    (T.smallEtaleTopology.uliftYonedaEquiv.{u + 1}).symm.injective

end AlgebraicGeometry.Scheme
