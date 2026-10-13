/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

/-! # Local representatives of annihilated stalk elements
Source: Stacks Project, Tag 01PO, final sentence of the proof.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry

/-- An annihilated germ has a representative annihilated by every local ideal section.
Source: Stacks Project, Tag 01PO, proof of (3), the omitted finite-generator argument.
(blueprint: lem-weil-pbc-annihilator-stalk-local-lift).

Proof: choose an affine neighborhood U of x and write F|U = M tilde, J|U = I tilde.
The finite-type ideal has generators g_1,...,g_t. Represent s by m/d in the
localization of M at the prime corresponding to x, with d outside that prime.
The hypothesis applied to each generator gives g_i m/d = 0. Clear a denominator
t_i outside the prime for each equality, and set t to their product. Then tm is
killed by every g_i, hence by I. On the principal neighborhood D(td), the section
(tm)/(td) has germ m/d = s and is killed by the restricted ideal. The affine
annihilation criterion gives the stated local annihilation condition. If I = 0,
use the empty product t = 1. The neighborhood may be shrunk to any initial affine
neighborhood; no choice of a global sheaf or morphism is needed.
-/
theorem annihilator_stalk_local_lift (X : Scheme.{u}) (J : X.IdealSheafData)
    [J.toModules.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (s : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)
    (hs : ∀ (U : X.Opens) (hx : x ∈ U), ∀ a ∈ J.idealOfOpens U,
      X.presheaf.germ U x hx a • s = 0) :
    ∃ (U : X.Opens) (hx : x ∈ U) (t : Γ(F, U)),
      F.presheaf.germ U x hx t = s ∧
      ∀ (V : X.Opens) (h : V ≤ U), ∀ a ∈ J.idealOfOpens V,
        a • F.presheaf.map (homOfLE h).op t = 0 := by
  sorry

end AlgebraicGeometry
