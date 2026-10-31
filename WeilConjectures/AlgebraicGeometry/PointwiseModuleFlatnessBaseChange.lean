/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.PullbackStalkRelativeFlatExtension
import WeilConjectures.AlgebraicGeometry.PointwiseFlatnessBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Pointwise module flatness under base change

Source: Stacks Project, More on Morphisms, Tag 047C, clauses (1) and (2)
(blueprint: lem-sfb-pointwise-module-flatness-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Relative flatness of a quasi-coherent module stalk ascends under arbitrary base change
and is reflected by base change flat at the chosen image point.
Source: Stacks Project, More on Morphisms, Tag 047C, clauses (1) and (2)
(blueprint: lem-sfb-pointwise-module-flatness-base-change).

Proof:
1. Write x = fst(x'), y' = snd(x'), y = f(x) = g(y'), and R, A, B, C for the local
   rings of Y, X, Y', X' at these points. The projection equation gives a commutative
   square of actual local stalk maps (def-pc-fibre-product, def-weil-flat-morphism).
   By lem-weil-pbc-module-stalk-pullback, the pulled-back stalk is C tensor_A F_x,
   canonically symmetric to F_x tensor_A C, with its B-action through snd.stalkMap.
2. For ascent apply lem-pc-pullback-stalk-relative-flat-extension to M = F_x.
   Its conclusion is B-flatness of C tensor_A M, hence of the pulled-back stalk.
3. For reflection, g is flat at y'. Apply clause (1) of
   lem-sfb-pointwise-flatness-base-change to the square with its factors interchanged.
   The universal property identifies its base-changed projection with fst. Thus A to C
   is a flat local homomorphism. By lem-weil-pbc-flat-local-hom-faithfully-flat, C is
   faithfully flat over A.
4. The pulled-back stalk N is B-flat and B is R-flat, so lem-pc-module-flat-transitive
   makes N R-flat. The two R-actions agree by the commutative stalk square.
5. For any exact R-module sequence L, the balanced reassociation
   C tensor_A (M tensor_R L) = (C tensor_A M) tensor_R L sends
   c tensor (m tensor l) to (c tensor m) tensor l; the reverse formula is its inverse.
   The balancing relations agree and these maps commute with the maps of L.
   By lem-weil-pbc-flat-tensor-exact the right-hand complex is exact. Exactness is
   also exactness as A-modules, since kernels and images are the same underlying sets.
   Faithful flatness of C over A reflects this exactness by
   def-weil-pbc-faithfully-flat-ring-map. Hence M tensor_R L is exact, so M is R-flat.
-/
theorem pointwise_module_flatness_base_change
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (F : X.Modules) [SheafOfModules.IsQuasicoherent.{u} F] (x' : ↥(pullback f g)) :
    (Module.Flat (Y.presheaf.stalk (f ((pullback.fst f g) x')))
        ((ModuleCat.restrictScalars (f.stalkMap ((pullback.fst f g) x')).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace ((pullback.fst f g) x')).obj
            F)) →
      Module.Flat (Y'.presheaf.stalk ((pullback.snd f g) x'))
        ((ModuleCat.restrictScalars ((pullback.snd f g).stalkMap x').hom).obj
          ((RingedSpace.moduleStalkFunctor (pullback f g).toRingedSpace x').obj
            ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj F)))) ∧
    ((g.stalkMap ((pullback.snd f g) x')).hom.Flat →
      Module.Flat (Y'.presheaf.stalk ((pullback.snd f g) x'))
        ((ModuleCat.restrictScalars ((pullback.snd f g).stalkMap x').hom).obj
          ((RingedSpace.moduleStalkFunctor (pullback f g).toRingedSpace x').obj
            ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj F))) →
      Module.Flat (Y.presheaf.stalk (f ((pullback.fst f g) x')))
        ((ModuleCat.restrictScalars (f.stalkMap ((pullback.fst f g) x')).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace ((pullback.fst f g) x')).obj
            F))) := by
  sorry

end AlgebraicGeometry
