/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Square-zero tests detect tensor exactness on an affine scheme

Source: the square-zero test in the proof of
lem-pc-affine-universally-exact-opcycles-flat, using Stacks Project, Tag 01IB.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Scheme base-change tests imply module tensor exactness in a fixed degree.
Source: Stacks Project, Tag 01IB, and steps 1--2 of
lem-pc-affine-universally-exact-opcycles-flat.
(blueprint: lem-pc-affine-universal-tensor-exact).

Proof: Write A = Gamma(S, top), and P for the complex of global sections.
The affine quasi-coherent equivalence identifies C with the associated-sheaf
complex of P, compatibly with differentials. For N form the explicit trivial
square-zero algebra A direct-sum N with product (a,x)(b,y) = (ab,ay+bx).
Its spectrum maps to S through the canonical affine spectrum isomorphism.
Quasi-coherent affine pullback is extension of scalars, so its global-sections
complex, restricted to A, is P tensor (A direct-sum N). Affine global sections
preserve homology on quasi-coherent complexes. The assumed zero homology in
this degree therefore gives zero homology of P tensor (A direct-sum N).
Distribute tensor over the two summands, and use the inclusion and projection
of N to exhibit P tensor N as a retract of that complex. These maps commute
with every differential by naturality of tensor. Homology preserves this
retraction, hence the homology of P tensor N is zero. This is ExactAt a.
No flatness of the terms is used. For N = 0 or the zero complex the retract
is zero. For the zero ring and empty affine scheme all modules are zero. -/
theorem affine_universal_tensor_exact (S : Scheme.{u}) (hS : IsAffine S)
    (C : CochainComplex S.Modules ℤ) (a : ℤ)
    (hqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hexact : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology a))
    (N : ModuleCat.{u} Γ(S, ⊤)) :
    (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj
      (((SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤) :
        S.Modules ⥤ ModuleCat.{u} Γ(S, ⊤)).mapHomologicalComplex
        (.up ℤ)).obj C)).ExactAt a := by sorry

end AlgebraicGeometry.Scheme.Modules
