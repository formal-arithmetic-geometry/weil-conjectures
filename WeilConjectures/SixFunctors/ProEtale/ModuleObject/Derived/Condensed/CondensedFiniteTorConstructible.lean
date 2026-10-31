/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleConeCounterexample
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeTriangulated

/-! # Intrinsic finite-Tor constructible condensed module objects

Source: latest blueprint sk-def-sf-operations, finite-Tor domain;
(blueprint: def-weil-finite-tor-amplitude).

The existing test by ordinary relative derived tensor against every module in degree
zero applies directly to native module objects. This interface retains the recorded
site presentations and adds their intrinsic ordinary condensed-module specialization.
It does not define the field category by rationalization or by a common-stage model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Bounded constructible objects of finite Tor amplitude in the ordinary derived
category of modules over the pulled-back condensed ring. `finiteTorAmplitude`
tests the actual relative derived tensor with every module placed in degree zero.
The same definition applies to every commutative condensed coefficient ring.
Source: latest blueprint sk-def-sf-operations, finite-Tor domain.
(blueprint: def-weil-finite-tor-amplitude). -/
def condensedConstructibleFiniteTor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :=
  boundedConstructible (condensedRingObj Λ T) ⊓ _root_.DerivedCategory.finiteTorAmplitude _

/-- The intrinsic full Dctf subcategory; its morphisms are those of the ordinary
module-derived category. No completion or lattice choice enters this definition.
Source: latest blueprint sk-def-sf-operations, finite-Tor domain.
(blueprint: def-weil-finite-tor-amplitude). -/
abbrev CondensedConstructibleFiniteTor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :=
  (condensedConstructibleFiniteTor Λ T).FullSubcategory

end AlgebraicGeometry.ProEtale.CondensedRing
