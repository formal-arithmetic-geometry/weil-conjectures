/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.Field.ULift

/-! # Raw pairs and smooth-center histories for jet levels

Source: ILO VIII 2.3.11--2.3.13, pp.93--94; BMT §6.1; the finite-history
convention in `lem-trf-jet-level-topology-reachable-dcc`
(blueprint: def-trf-jet-level-blowup-history).

No geometric regularity is part of a raw pair. In particular the relation does not
assume its later ambients smooth or its later intrinsic schemes reduced.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- An intrinsic scheme mapping to a rational ambient, without regularity assumptions.
The rational lift only places the ground field in the scheme universe.
Source: ILO VIII 2.3.11--2.3.13; BMT §6.1
(blueprint: def-trf-jet-level-blowup-history). -/
structure JetLevelPair where
  X : Scheme.{u}
  Z : Scheme.{u}
  p : Z ⟶ Spec (.of (ULift.{u} ℚ))
  i : X ⟶ Z

/-- A smooth center contained scheme-theoretically in the intrinsic scheme, with locally
constant intrinsic Hilbert--Samuel level. The actual blowup and strict transform determine
the successor up to isomorphisms commuting with the inclusions and rational structure maps.
There is no boundary condition, maximum condition or restriction on empty centers.
Source: ILO VIII 2.3.11--2.3.13; BMT §6.1
(blueprint: def-trf-jet-level-blowup-history). -/
def JetLevelBlowup (S T : JetLevelPair.{u}) : Prop :=
  ∃ (C : S.Z.IdealSheafData) (c : C.subscheme ⟶ S.X),
    IsClosedImmersion c ∧ c ≫ S.i = C.subschemeι ∧
    Smooth (C.subschemeι ≫ S.p) ∧
    (∀ a : C.subscheme, ∃ U : C.subscheme.Opens, a ∈ U ∧
      ∀ b : C.subscheme, b ∈ U →
        function (k := ULift.{u} ℚ) (S.i ≫ S.p) (c b) =
          function (k := ULift.{u} ℚ) (S.i ≫ S.p) (c a)) ∧
    ∃ (e : T.Z ≅ C.blowup) (q : T.X ≅ C.strictTransform S.i),
      e.hom ≫ C.blowupMap ≫ S.p = T.p ∧
      T.i ≫ e.hom = q.hom ≫ strictTransformMap S.i C.blowupMap C.support.compl

/-- All finite histories, including the empty history. Each step is an actual ambient
blowup with its scheme-theoretic strict transform, rather than an arbitrary transition map.
Source: BMT §6.1; the finite-history convention in the owning jet-level lemma
(blueprint: def-trf-jet-level-blowup-history). -/
def JetLevelReachable (S T : JetLevelPair.{u}) : Prop :=
  Relation.ReflTransGen JetLevelBlowup S T

end AlgebraicGeometry.HilbertSamuel
