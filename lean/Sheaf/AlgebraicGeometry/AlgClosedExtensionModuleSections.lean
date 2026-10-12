/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Module sections after algebraically closed field extension

Source: Stacks Project, Tag 0A3I, applied to the underlying sheaf of sets.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Scalar extension preserves global sections of every module-valued etale sheaf.
Source: Stacks Project, Tag 0A3I; the coefficient-forgetting comparison is the
Kan-extension/sheafification comparison of inverse images.
(blueprint: lem-sc-algclosed-extension-module-sections)

Proof: forget the module structure of G to obtain a sheaf of sets. By Tag 0A3I,
restriction on its global sections along X_K -> X is bijective, since k is separably
closed. The module forgetful functor preserves limits and filtered colimits, hence
commutes with inverse image: compute the Kan extension by filtered etale neighborhoods,
then sheafify. The comparison respects the adjunction unit. Evaluation at the terminal
etale object and the global-sections/terminal-sections isomorphisms therefore identify
the underlying function of the displayed module map with that restriction, conjugated
by the comparison bijections. A bijective module homomorphism is an isomorphism. No
quasi-compactness, torsion, primality, or invertibility assumption is needed. This
includes n = 0, n = 1, and the empty scheme. -/
theorem isIso_globalSectionsUpperStarMap_algClosed_extension
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) :
    IsIso (globalSectionsUpperStarMap
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) G) := by sorry

end AlgebraicGeometry.Etale
