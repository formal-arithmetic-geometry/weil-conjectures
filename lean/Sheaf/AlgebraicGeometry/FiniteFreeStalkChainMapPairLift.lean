/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Lifting a pair of finite free chain maps from a stalk

Source: lem-pc-finite-free-stalk-homotopy-spread, proof steps 1 and 2.
(blueprint: lem-pc-finite-free-stalk-chain-map-pair-lift)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A given pair of chain maps over the stalk lifts, without imposing inverse identities.

Source: blueprint lem-pc-perfect-locus, finite matrix extension argument, as expanded
in lem-pc-finite-free-stalk-homotopy-spread, steps 1 and 2.
(blueprint: lem-pc-finite-free-stalk-chain-map-pair-lift).

Proof: Choose an affine neighbourhood and bases in every nonzero term. The source
complex has support [0,d] and the single complex has support {i}. The components
of the two prescribed chain maps are therefore finitely many matrices. Represent
each entry in the local ring by a section near y and intersect the neighbourhoods.
Each chain-map commutativity equation holds in the stalk. There are finitely many
such matrix equations; the equality criterion for germs makes each hold on a
smaller neighbourhood. Intersect these again and define all other components by
the unique maps involving zero objects. This constructs the two chain maps.
The canonical pullback-composition and restriction-pullback isomorphisms give eP
and eQ, and the represented entries give the stated exact equalities. No inverse
or homotopy identity is imposed, and no assumption of homotopy equivalence is used.
Ranks zero and i outside [0,d] cause only additional zero components. -/
theorem exists_restrict_chainMap_pair_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i : ℤ) (r : ℕ) (y : Y)
    (f : (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P) ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))))
    (g : (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))) ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P)) :
    ∃ (V : Y.Opens) (hyV : y ∈ V),
      let R := (restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)
      let S := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let T := (Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let Q := ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
      ∃ (eP : S.obj (R.obj P) ≅ T.obj P) (eQ : S.obj (R.obj Q) ≅ T.obj Q)
        (fV : R.obj P ⟶ R.obj Q) (gV : R.obj Q ⟶ R.obj P),
        S.map fV = eP.hom ≫ f ≫ eQ.inv ∧ S.map gV = eQ.hom ≫ g ≫ eP.inv := by
  sorry

end AlgebraicGeometry.Scheme.Modules
