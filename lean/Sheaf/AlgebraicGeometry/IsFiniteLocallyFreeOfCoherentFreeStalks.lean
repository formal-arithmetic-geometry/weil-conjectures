/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Coherent modules with finite free stalks are finite locally free

Source: Stacks Project, Algebra, Tag 0GWM, applied on Noetherian affine opens;
Cohomology of Schemes, Tag 01XZ; Divisors, Tag 0CC4
(blueprint: lem-sc-coherent-free-stalks-locally-free).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on a locally Noetherian scheme whose stalks are finite free is
finite locally free, with no requirement that the ranks on different opens be equal.
Source: Stacks Project, Algebra, Tag 0GWM, and Cohomology of Schemes, Tag 01XZ
(blueprint: lem-sc-coherent-free-stalks-locally-free).

Proof:
1. By `pqf-lem-coherent-ft-locnoeth`, coherence on a locally Noetherian scheme implies
   quasi-coherence and finite type. Choose the affine Noetherian covering supplied by
   `pqf-def-locnoeth`. On a member U = Spec A, the module M of sections is finite by
   `lem-weil-pbc-quasi-coherent-finite-type-affine` (c). The counit of
   `lem-weil-pbc-affine-tilde-gamma-adjunction` (3) identifies F restricted to U with tilde M.
2. By `lem-weil-pbc-spec-tilde-stalk-localization`, its stalk at the point corresponding
   to a prime p is M localized at p, over A localized at p. The hypothesis therefore gives
   finite free localizations at every prime. Apply `lem-sc-affine-finite-module-free-locus`
   to obtain a finite principal-open cover on which tilde M, hence F, is finite free.
3. Collect these covers over the original affine covering. They cover X and trivialize F
   with finite, possibly varying, ranks. This is precisely finite local freeness.
-/
theorem isFiniteLocallyFree_of_coherent_free_stalks
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    (hcoherent : RingedSpace.IsCoherent X.toRingedSpace F)
    (hfree : ∀ x : X,
      Module.Free (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) ∧
      Module.Finite (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} F := by
  sorry

end AlgebraicGeometry.Scheme.Modules
