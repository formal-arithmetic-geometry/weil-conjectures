/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # Shrinking to spread two specified stalk homotopies

Source: lem-pc-finite-free-stalk-homotopy-spread, proof steps 2 and 3.
(blueprint: lem-pc-finite-free-stalk-homotopy-pair-shrink)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Two specified pairs of endomorphisms become homotopic after shrinking.

Source: blueprint lem-pc-perfect-locus, finite matrix extension argument, as expanded
in lem-pc-finite-free-stalk-homotopy-spread, steps 2 and 3.
(blueprint: lem-pc-finite-free-stalk-homotopy-pair-shrink).

Proof: Work on an affine neighbourhood of y inside V, with finite bases in the
terms. Choose the two given stalk homotopies. Each has finitely many nonzero
components because P and the single complex are bounded. Represent the finitely
many homotopy matrix entries by sections near y. The homotopy equations for the
fixed endomorphisms a,b,c,e hold in the stalk, so their finitely many entrywise
identities hold on some smaller neighbourhood by the germ equality criterion.
Intersect all these neighbourhoods to obtain W contained in V. The represented
components, zero off the reverse differential relation, are actual homotopies
between the restrictions of the given maps. Outside the bounded supports the
identities are automatic by uniqueness of maps involving zero objects. The
stalk pullback along V.fromSpecStalkOfMem identifies the matrices with matrices
over O_{Y,y}, so it tests exactly these germs. Neither map pair is assumed to be
an inverse pair. The zero-rank and disjoint-support cases obey the same argument. -/
theorem exists_shrink_homotopy_pair_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i : ℤ) (r : ℕ) (y : Y)
    (V : Y.Opens) (hyV : y ∈ V)
    (a b : (((restrictFunctor V.ι).mapHomologicalComplex _).obj P) ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj P))
    (c e : (((restrictFunctor V.ι).mapHomologicalComplex _).obj
      ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))) ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj
      ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))))
    (hP : Nonempty (Homotopy
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map a)
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map b)))
    (hQ : Nonempty (Homotopy
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map c)
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map e))) :
    ∃ (W : Y.Opens) (hWV : W ≤ V), y ∈ W ∧
      Nonempty (Homotopy
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map a)
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map b)) ∧
      Nonempty (Homotopy
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map c)
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map e)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
