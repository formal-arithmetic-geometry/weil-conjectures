/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Shrinking differential-commutativity defects

Source: lem-pc-finite-free-stalk-chain-map-lift-local, the zero-germ shrinking step.
(blueprint: lem-pc-finite-free-stalk-degreewise-shrink)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- An already defined degreewise family whose stalk commutes with differentials
can be restricted to a smaller neighbourhood where it commutes.

Source: lem-pc-finite-free-stalk-chain-map-lift-local, step 2 (vanishing of the
commutativity defects) and step 3 (compatibility of stalk restriction), expanding
lem-pc-perfect-locus's extension of the finite calculation.

Proof: In the restricted finite bases form, for every adjacent degree, the matrix
of g n followed by d_Q minus d_P followed by g (n+1). Its pullback to the stalk
scheme is zero by hcomm. Thus its entries have zero germ at y. Only degrees for
which both P.X n and Q.X (n+1) are nonzero need checking; boundedness makes this
list finite. For every entry the germ equality criterion gives a neighbourhood
inside U on which the entry vanishes. Intersect this finite collection to obtain
V containing y, with V <= U. Restrict every g n to V and transport along the
canonical comparison between direct restriction to V and restriction through U;
call the resulting family k. All adjacent chain equations now hold. Outside the
finite list either the source or target is zero, and the equation is automatic.
Restriction transitivity and pullback composition identify the stalk of k n with
the stalk of g n conjugated by the comparisons through Y. This is the displayed
component formula, with the inverse comparison at U followed by the one at V.
The compatibility follows by the associativity of pullback composition and the
identity of the composite maps from Spec O_{Y,y}. For an empty support interval,
rank-zero terms, or an already commuting family, the same construction works
with no equations or no further shrinking. The lemma extends no prescribed map:
it starts with the family g already defined on U.
(blueprint: lem-pc-finite-free-stalk-degreewise-shrink) -/
theorem exists_shrink_degreewise_comm_of_stalk
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (a b c e : ℤ)
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b)
    (hQc : Q.IsStrictlyGE c) (hQe : Q.IsStrictlyLE e)
    (hPfree : ∀ n : ℤ, IsZero (P.X n) ∨ ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hQfree : ∀ n : ℤ, IsZero (Q.X n) ∨ ∃ s : ℕ, Nonempty
      (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (U : Y.Opens) (hyU : y ∈ U)
    (g : ∀ n : ℤ,
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n)
    (hcomm : ∀ n : ℤ,
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g n) ≫
        (((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)).d
            n (n + 1) =
      (((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).d
          n (n + 1) ≫ (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g (n + 1))) :
    ∃ (V : Y.Opens), ∃ (hyV : y ∈ V), V ≤ U ∧ ∃ (k : ∀ n : ℤ,
      (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (∀ n : ℤ, k n ≫
        (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).d
          n (n + 1) =
        (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).d
          n (n + 1) ≫ k (n + 1)) ∧
      (∀ n : ℤ, (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map (k n) =
        ((stalkRestrictionComplexIso V y hyV).app P).hom.f n ≫
        ((stalkRestrictionComplexIso U y hyU).app P).inv.f n ≫
        (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g n) ≫
        ((stalkRestrictionComplexIso U y hyU).app Q).hom.f n ≫
        ((stalkRestrictionComplexIso V y hyV).app Q).inv.f n) := by sorry

end AlgebraicGeometry.Scheme.Modules
