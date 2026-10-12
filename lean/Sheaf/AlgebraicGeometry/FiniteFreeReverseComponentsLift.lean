/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # Lifting reverse-degree components without imposing homotopy equations

Source: lem-pc-perfect-locus, extension of the finite calculation near a point.
(blueprint: lem-pc-finite-free-reverse-components-lift)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Lift a family of reverse-degree maps, without any equations involving the differential.

Source: lem-pc-finite-free-stalk-homotopy-p-only, steps 1 and 2, expanding the finite
calculation in lem-pc-perfect-locus (first two proof paragraphs).
(blueprint: lem-pc-finite-free-reverse-components-lift)

Proof: Choose finite bases for the terms of P. Restriction preserves these bases by
restrictFunctorIsoPullback and pullbackFreeIso. Pullback to Spec O_{Y,y} preserves them
again. Only reverse-degree pairs with both indices in [0,d] can contribute: outside
that interval one of the two modules is zero. In these finitely many pairs, each map
is a finite matrix over O_{Y,y}, since global sections of Spec O_{Y,y} are O_{Y,y}.
Represent each entry by a structure-sheaf section near y inside V, and intersect the
finitely many neighbourhoods. Define k by those matrices in the chosen restricted
bases, and by zero at all other pairs. In particular k has reverse-degree support.
The equality of the matrices after taking germs gives the stated component equality.
The natural isomorphism e is obtained from restrictFunctorIsoPullback, pullbackComp,
and the identity U.fromSpecStalkOfMem y hyU composed with Y.homOfLE hUV equals
V.fromSpecStalkOfMem y hyV; the latter follows by cancellation of the open inclusion
V.ι. Thus e applies to every complex on V, not merely to P. No chain equation or
homotopy equation is asserted here. Empty matrices, d=0, and zero terms require no
coefficients to lift and are handled by the zero maps. -/
theorem exists_lift_reverse_components
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (h : ∀ i j : ℤ,
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)).X i ⟶
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)).X j)
    (hzero : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0) :
    ∃ (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U),
      let R := (restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let S := (Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let T := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let PV := ((restrictFunctor V.ι).mapHomologicalComplex _).obj P
      ∃ (e : R ⋙ S ≅ T) (k : ∀ i j : ℤ, (R.obj PV).X i ⟶ (R.obj PV).X j),
        (∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → k i j = 0) ∧
        ∀ i j, (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (k i j) =
          (e.app PV).hom.f i ≫ h i j ≫ (e.app PV).inv.f j := by sorry

end AlgebraicGeometry.Scheme.Modules
