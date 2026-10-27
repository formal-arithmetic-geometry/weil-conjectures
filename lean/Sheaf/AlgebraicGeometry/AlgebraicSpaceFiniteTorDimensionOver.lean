/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.RingTheory.Flat.Basic

/-! # Uniform relative Tor dimension on algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tag 08IS(3); sites-cohomology.tex,
Tags 08FZ, 08G1 and 0DJJ (finite Tor dimension and its stalk criterion)
(blueprint: def-sfb-space-finite-tor-dimension-over).

The geometric-stalk criterion retains restriction along the actual geometric local
ring map. The same two bounds work at every point, including on a non-quasi-compact
source. Bounded flat complexes compute derived tensors against all modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite Tor dimension over the inverse-image base structure sheaf, expressed by the
uniform geometric-stalk criterion. Choose a representative K of E. At each geometric
point x, restrict the complex of its geometric stalks along the canonical local ring
map O_{Y,f(x)} → O_{X,x}. It must admit a bounded flat representative in one fixed
interval [a,b], independent of x. There is no finiteness condition on the flat modules.
A bounded flat representative is K-flat, so this tests tensoring with every module
of the base geometric local ring, not only residue fields or quasi-coherent sheaves.
Exact conservative geometric stalks and the stalk criterion for flatness identify
this condition with Tor amplitude [a,b] of the scalar restriction over f^{-1}O_Y:
truncate a flat-term K-flat resolution at a and b, and test flatness of its boundary
cokernel on the stalks. Thus this is a global bound, not merely locally finite Tor
dimension. The standard localizations below are internal to the stalk test; the
ambient derived-category morphism universe w remains independent.
Source: Stacks Project, Tag 08IS(3); Cohomology on Sites, Tags 08FZ, 08G1 and 0DJJ
(blueprint: def-sfb-space-finite-tor-dimension-over). -/
def HasFiniteTorDimensionOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [HasDerivedCategory.{w} X.SmallModules] (E : X.DerivedModules) : Prop :=
  letI : ∀ (R : Type u) [CommRing R], HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
    fun _ _ ↦ HasDerivedCategory.standard _
  ∃ K : CochainComplex X.SmallModules ℤ,
    Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
    ∃ a b : ℤ, a ≤ b ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
        (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj),
        ∃ P : CochainComplex (ModuleCat.{u} (SingleComplex.stalkRing s
            (x ≫ f.hom.hom))) ℤ,
          (∀ n : ℤ, Module.Flat (SingleComplex.stalkRing s (x ≫ f.hom.hom)) (P.X n)) ∧
          (∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
          Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj
            (((SingleComplex.stalk s x ⋙
                ModuleCat.restrictScalars (SingleComplex.stalkMap f s x)).mapHomologicalComplex
              (.up ℤ)).obj K))

end AlgebraicGeometry.AlgebraicSpace
