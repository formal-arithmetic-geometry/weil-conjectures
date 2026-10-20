/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Sheaf.TraceFormula.FlatAssociatedEquidimensional
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType
import WeilConjectures.RingTheory.FlatOfFlatClosedFiber
import WeilConjectures.Topology.FiniteTypeSurjectiveNearStalk
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.Paper.DerivedHomMayerVietoris

/-!
# Relative flatness and a flat fibre stalk give a free neighbourhood

Source: Stacks Project, More on Morphisms, Tag 080Q, lemma-flat-and-free-at-point-fibre
(blueprint: lem-trf-flat-fibre-free-neighbourhood).

The proof follows Tag 080Q.  First the fibre flatness criterion, applied to the local rings at
`x`, identifies the stalk as flat over `𝒪_{X,x}`.  Finite flatness over a local ring gives a finite
basis.  Spreading the basis gives a surjection from a finite free module; finite presentation makes
its kernel finite type, so the zero kernel at `x` vanishes after shrinking.  The resulting map is
the required local isomorphism.  The zero stalk case is the same argument with rank zero.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative flatness and flatness on the scheme-theoretic fibre imply local freeness.
(blueprint: lem-trf-flat-fibre-free-neighbourhood) -/
theorem exists_free_neighbourhood
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsFinitePresentation] (x : X)
    (hflat : moduleFlatAt f F x)
    (hfibre : Module.Flat ((f.fiber (f x)).toRingedSpace.presheaf.stalk (f.asFiber x))
      ((AlgebraicGeometry.RingedSpace.moduleStalkFunctor (f.fiber (f x)).toRingedSpace
        (f.asFiber x)).obj ((AlgebraicGeometry.Scheme.Modules.tensorPullback
          (f.fiberι (f x))).obj F))) :
    ∃ (W : X.Opens) (r : ℕ), x ∈ W ∧
      Nonempty (((restrictFunctor W.ι).obj F) ≅
        (restrictFunctor W.ι).obj
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
