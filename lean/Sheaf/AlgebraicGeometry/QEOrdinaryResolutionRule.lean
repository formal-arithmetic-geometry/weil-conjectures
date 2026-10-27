/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.GabberModificationData
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Regular-functorial ordinary resolution rules on quasi-excellent rational schemes

Source: ILO, Travaux de Gabber, VIII 2.3.1, 2.3.4, Remark 2.3.5(i) and
Theorem 2.3.10, printed pp. 91--93 (blueprint: def-per-qe-ordinary-resolution-rule).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The full Noetherian quasi-excellent rational domain, without finite-type, separation
or dimension restrictions. Quasi-excellence uses the existing affine-local predicate.
Source: ILO VIII 2.3.9--2.3.10 (blueprint: def-per-qe-ordinary-resolution-rule). -/
structure QERationalResolutionInput where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of (ULift.{u} ℚ))
  reduced : IsReduced scheme
  noetherian : IsNoetherian scheme
  quasiExcellent : GabberModification.QuasiExcellent scheme

/-- Flatness and geometric regularity of the fibres, tested after every finite residue-field
extension. The field universe is the scheme universe, so these tests include the residue
field itself. No finite-type assumption on the morphism is made.
Source: ILO VIII 2.1.12, 2.3.10 (blueprint: def-per-qe-ordinary-resolution-rule). -/
def IsResolutionRegular {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  Flat f ∧ ∀ (x : X) (K : Type u) [Field K] [Algebra (X.residueField x) K]
    [Module.Finite (X.residueField x) K],
    IsRegularScheme (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
        X.fromSpecResidueField x))

/-- A single ordinary resolution rule on all inputs, with contracted cartesian pullbacks
along regular morphisms. The existing comparison keeps the extended ideals in order and
contracts exactly the unit ideals. Identity and composition laws concern both counts and
actual level maps. Regularity proofs for identities and composites are explicit arguments
of those laws; this avoids choosing any proofs or postulating closure as extra data.
Coherence is asserted using the full finite-type-kernel definition, in addition to the
existing regular-resolution predicate. The empty scheme has tower length zero.
Source: ILO VIII 2.3.1, 2.3.4--2.3.5(i), 2.3.10
(blueprint: def-per-qe-ordinary-resolution-rule). -/
structure RegularFunctorialQEOrdinaryResolution where
  tower : ∀ S : QERationalResolutionInput.{u}, OrdinaryBlowupTower S.scheme
  resolves : ∀ S, (tower S).IsRegularResolution
  coherent_centers : ∀ S (i : Fin (tower S).length),
    RingedSpace.IsCoherent ((tower S).level i.castSucc).toRingedSpace
      ((tower S).center i).toModules
  comparison : ∀ (S T : QERationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (_over : h ≫ S.structureMap = T.structureMap) (_regular : IsResolutionRegular h),
    OrdinaryResolutionComparison h (tower S) (tower T)
  identity_count : ∀ S (hr : IsResolutionRegular (𝟙 S.scheme)) i,
    (comparison S S (𝟙 S.scheme) (by simp) hr).count i = i
  identity_map : ∀ S (hr : IsResolutionRegular (𝟙 S.scheme)) i,
    eqToHom (congrArg (tower S).level (identity_count S hr i).symm) ≫
      (comparison S S (𝟙 S.scheme) (by simp) hr).levelMap i = 𝟙 ((tower S).level i)
  composition_count : ∀ (S T U : QERationalResolutionInput.{u})
    (h : T.scheme ⟶ S.scheme) (k : U.scheme ⟶ T.scheme)
    (overH : h ≫ S.structureMap = T.structureMap)
    (overK : k ≫ T.structureMap = U.structureMap)
    (hr : IsResolutionRegular h) (kr : IsResolutionRegular k)
    (khr : IsResolutionRegular (k ≫ h)) i,
    (comparison S U (k ≫ h) (by rw [Category.assoc, overH, overK]) khr).count i =
      (comparison T U k overK kr).count ((comparison S T h overH hr).count i)
  composition_map : ∀ (S T U : QERationalResolutionInput.{u})
    (h : T.scheme ⟶ S.scheme) (k : U.scheme ⟶ T.scheme)
    (overH : h ≫ S.structureMap = T.structureMap)
    (overK : k ≫ T.structureMap = U.structureMap)
    (hr : IsResolutionRegular h) (kr : IsResolutionRegular k)
    (khr : IsResolutionRegular (k ≫ h)) i,
    eqToHom (congrArg (tower U).level
      (composition_count S T U h k overH overK hr kr khr i)) ≫
        (comparison T U k overK kr).levelMap ((comparison S T h overH hr).count i) ≫
          (comparison S T h overH hr).levelMap i =
      (comparison S U (k ≫ h) (by rw [Category.assoc, overH, overK]) khr).levelMap i
  surjective_no_deletion : ∀ (S T : QERationalResolutionInput.{u})
    (h : T.scheme ⟶ S.scheme) (over : h ≫ S.structureMap = T.structureMap)
    (hr : IsResolutionRegular h) [Surjective h],
    Function.Surjective (comparison S T h over hr).retainedStage
  empty_input : ∀ S, IsEmpty S.scheme → (tower S).length = 0

end AlgebraicGeometry
