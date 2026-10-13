/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat

/-! # Flat terms of the finite-projective ring dual

Source: Stacks Project, More on Algebra, Tags 0A6A and 064K.
(blueprint: lem-pc-perfect-ring-dual-term-flat)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The actual Hom complex into the ring in degree zero; no dual object is chosen.
Source: Stacks Project, More on Algebra, Tag 0A6A, finite-projective argument.
(blueprint: lem-pc-perfect-ring-dual-term-flat) -/
noncomputable def perfectRingDual {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) :
    CochainComplex (RingSiteModules A) ℤ :=
  homComplex (R := CochainComplex.onePointRingSheaf A) P
    ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A))))

/-- Every term of the dual of a complex of finite-projective ring modules is flat.
Source: Stacks Project, More on Algebra, Tag 0A6A, clause (1), finite-projective
representative argument; Mathlib `Module.dual_projective` and `Module.Flat.of_projective`.
(blueprint: lem-pc-perfect-ring-dual-term-flat)

Proof: in degree n the product defining Hom(P,A[0]) has only one possibly nonzero
factor, Hom(P^(-n),A). All other factors vanish because A[0] vanishes there.
Its projection to this factor is an isomorphism by the product universal property.
Evaluation at the unique object of the discrete one-object bottom-topology site
is an exact equivalence with A-modules and identifies sheaf tensor with module tensor.
A finite projective module is a summand of a finite free module. Applying Hom(-,A)
to its splitting exhibits its dual as a summand of the dual finite free module,
which is finite free by coordinate evaluation. Hence this dual is projective,
therefore flat. Under the evaluation equivalence tensoring with this sheaf
preserves finite limits and finite colimits, which is the predicate IsFlat.
This includes the zero ring, zero modules and rank-zero summands. No boundedness
or assertion about a second complex is used. -/
theorem perfectRingDual_term_isFlat {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ)
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hf : ∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) :
    ∀ n : ℤ, SheafOfModules.IsFlat ((perfectRingDual P).X n) := by sorry

end CategoryTheory
