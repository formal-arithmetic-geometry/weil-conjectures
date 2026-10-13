/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-! # Canonical completion of the derived tensor row

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Universal derived scalar extension preserves distinguished triangles for the
shift structure compatible with its universal counit.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, and Tag 05SE.

Proof: use exists_baseDerivedExtension_resolution to compute the universal
functor on K-flat resolutions. Its counit-compatible shift is induced by
shifting the resolutions. Extension of scalars preserves cone triangles on
these resolutions, hence the induced functor preserves distinguished triangles.
The right Kan universal property uniquely determines each shift comparison
commuting with the counit. Thus the supplied CommShift structure is the
resolution shift structure, transported through the unique universal functor
isomorphism. Restriction A to R is exact and induces a triangulated functor
D(A) to D(R). Compose it with this triangulated derived extension and apply it
to the distinguished image of T. Its factorization through the homotopy
quotient and Qh gives precisely the displayed triangle, including its third
arrow. No flatness, boundedness or nonzero-ring hypothesis is needed.
(blueprint: lem-pc-base-derived-extension-coherent-triangle). -/
theorem baseDerivedExtension_coherent_triangle_distinguished
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [(extendScalars.{u, u, u} (algebraMap R B)).Additive]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
    [HasDerivedCategory (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    [L.CommShift ℤ] [NatTrans.CommShift ε ℤ]
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles) :
    (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
      HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙
      L).mapTriangle.obj T) ∈
      Pretriangulated.distinguishedTriangles := by sorry

end ModuleCat
