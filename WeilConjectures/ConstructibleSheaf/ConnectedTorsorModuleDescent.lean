/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

import WeilConjectures.ConstructibleSheaf.TorsorModuleDescentEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Associated module sheaves on a connected finite torsor

For a connected finite Galois cover `c.P ⟶ V` with group `P`, descent along the cover gives an
additive functor `T` from `ℤ/ℓ`-representations of `P` to sheaves of `ℤ/ℓ`-modules on `V`,
compatible with geometric stalks. Every sheaf whose pullback to `c.P` is constant with
finite-dimensional value is of the form `T(M)` for a finite-dimensional representation `M`.

## Main results

- `AlgebraicGeometry.Scheme.GaloisCover.exists_module_descent_stalk_functor`

## Implementation details

The representation `M` is recovered from the sheaf `F` via the inverse of the descent
equivalence, not chosen as an arbitrary representation with the right stalk dimension.
Connectedness of `c.P` is used to see that the transition maps of the descent datum are
constant.

## References

- Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Descent on a connected finite Galois cover `c` of `V` with group `P`. Let `F` be a sheaf of
`ℤ/ℓ`-modules on `V` whose pullback to `c.P` is constant with finite-dimensional value `A`.
Then there are an additive functor `T` from `ℤ/ℓ`-representations of `P` to sheaves on `V`
and a finite-dimensional representation `M` such that the geometric stalk of `T(N)` at every
point is naturally the underlying module of `N`, `T(M) ≅ F`, and `T` sends the trivial
rank-one representation to the constant sheaf `ℤ/ℓ`. -/
theorem Scheme.GaloisCover.exists_module_descent_stalk_functor
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    [FiniteDimensional (ULift.{u + 1} (ZMod ℓ)) A]
    (hF : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A)) :
    ∃ (M : Rep.{u + 1} (ZMod ℓ) P) (_ : FiniteDimensional (ZMod ℓ) M.V)
      (T : Rep.{u + 1} (ZMod ℓ) P ⥤
        Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
      (_ : T.Additive),
      (∀ x : V, Nonempty
        (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
              (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ⋙
            ModuleCat.restrictScalars.{u + 1}
              (ULift.ringEquiv.symm.toRingHom : ZMod ℓ →+* ULift.{u + 1} (ZMod ℓ)) ≅
          forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)))) ∧
      Nonempty (T.obj M ≅ F) ∧
      Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
        (constantSheaf V.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by
  classical
  let := c.etale
  let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
  let D : ObjectProperty (Sheaf V.smallEtaleTopology C) := fun G ↦
    ∃ B : C, Nonempty ((c.π)^*[C].obj G ≅
      (constantSheaf c.P.smallEtaleTopology C).obj B)
  obtain ⟨E, hT, ⟨eπ⟩, hunit⟩ := c.exists_module_descent_equivalence ℓ P
  let T := E.functor ⋙ D.ι
  -- The inverse equivalence recovers the representation from the sheaf itself.
  let G : D.FullSubcategory := ⟨F, A, hF⟩
  let M := E.inverse.obj G
  let eF : T.obj M ≅ F := D.ι.mapIso (E.counitIso.app G)
  obtain ⟨y⟩ := (inferInstance : Nonempty c.P)
  let Φ := c.P.uliftPointSmallEtale y
  let U := forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ))
  let S := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)
  obtain ⟨iF⟩ := hF
  -- Compare the two constant pullbacks at one geometric point upstairs.
  let iA : S.obj (U.obj M) ≅ A :=
    (Φ.sheafFiberConstantSheafIso (S.obj (U.obj M))).symm ≪≫
      Φ.sheafFiber.mapIso ((eπ.app M).symm ≪≫
        ((c.π)^*[C]).mapIso eF ≪≫ iF) ≪≫ Φ.sheafFiberConstantSheafIso A
  let f : A →ₛₗ[ULift.ringEquiv.toRingHom] M.V :=
    { toFun := iA.inv
      map_add' := iA.inv.hom.map_add
      map_smul' := fun r a ↦ iA.inv.hom.map_smul r a }
  have hM : FiniteDimensional (ZMod ℓ) M.V :=
    Module.Finite.of_surjective f iA.toLinearEquiv.symm.surjective
  refine ⟨M, hM, T, hT, ?_, ⟨eF⟩, hunit⟩
  intro x
  -- Lift the geometric point, then use the natural pullback and constant-stalk isomorphisms.
  obtain ⟨z, hz⟩ := c.surjective.surj x
  obtain ⟨s, hs, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed c.π
    (V.algClosurePoint x) z (by simpa using hz)
  let Ψ := (Scheme.pointSmallEtale s).ulift.{u + 1}
  let ebase : (c.π)^*[C] ⋙ Ψ.sheafFiber ≅
      (V.uliftPointSmallEtale x).sheafFiber :=
    (upperStarCompUliftSheafFiberIso C c.π s) ≪≫
      (eqToIso (by rw [hs]; rfl))
  let econst := Ψ.constantSheafCompSheafFiberIso c.P.smallEtaleTopology C
  let R := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.symm.toRingHom : ZMod ℓ →+* ULift.{u + 1} (ZMod ℓ))
  let ering : S ⋙ R ≅ 𝟭 (ModuleCat.{u + 1} (ZMod ℓ)) :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{u + 1} (ZMod ℓ) ≃+* ZMod ℓ)).unitIso.symm
  let e : T ⋙ (V.uliftPointSmallEtale x).sheafFiber ≅ U ⋙ S :=
    Functor.isoWhiskerLeft T ebase.symm ≪≫
      (Functor.associator T ((c.π)^*[C]) Ψ.sheafFiber).symm ≪≫
      Functor.isoWhiskerRight eπ Ψ.sheafFiber ≪≫
      Functor.associator U (S ⋙ constantSheaf c.P.smallEtaleTopology C) Ψ.sheafFiber ≪≫
      Functor.isoWhiskerLeft U
        (Functor.associator S (constantSheaf c.P.smallEtaleTopology C) Ψ.sheafFiber) ≪≫
      Functor.isoWhiskerLeft U (Functor.isoWhiskerLeft S econst) ≪≫
      Functor.isoWhiskerLeft U (Functor.rightUnitor S)
  exact ⟨(Functor.associator T (V.uliftPointSmallEtale x).sheafFiber R).symm ≪≫
    Functor.isoWhiskerRight e R ≪≫ Functor.associator U S R ≪≫
    Functor.isoWhiskerLeft U ering ≪≫ Functor.rightUnitor U⟩

end AlgebraicGeometry
