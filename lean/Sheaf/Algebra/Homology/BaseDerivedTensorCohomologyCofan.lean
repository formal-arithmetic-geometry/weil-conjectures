/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Coproducts of universal base-derived tensor cohomology models

Source: Stacks Project, Tags 06Y6, 07D9 and 0DJA(1).
(blueprint: lem-pc-base-derived-tensor-cohomology-canonical-cofan). -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

/-- Canonical model maps out of a complex coproduct give a cohomology coproduct
before any further extension of scalars.
Source: Stacks Project, Tags 06Y6, 07D9 and 0DJA(1).

Proof: restrict the given cofan to R; restriction of module scalars preserves
coproducts degreewise. Resolve each restricted summand K-flatly. The sum of
these resolutions is K-flat: tensor with an acyclic complex commutes with
sums, and exactness of module sums makes the resulting sum acyclic. Their
summed augmentations are quasi-isomorphisms, again by exactness of sums.
Compute derived R-to-B extension using these resolutions and B in degree
zero. Ordinary extension preserves the sum. The images of these complexes
in D(B) form a coproduct by the derived direct-sum theorem. Universality of
the supplied counits identifies each supplied derived functor with this
common K-flat calculation, and counit compatibility identifies every δ_j
with the unique such comparison. Derived homology preserves this coproduct.
The hg equations identify its cohomology coprojections with the restrictions
of g_j. Thus the restricted cofan is colimiting in B-modules. Its universal
maps are E-linear for E = A tensor_R B: each a tensor 1 commutes with all
g_j by the model action equation and naturality at multiplication by a;
B-linearity supplies 1 tensor b, and tensor induction supplies all of E.
The universal map out of the B-module sum therefore respects E, giving an
E-module coproduct. The empty cofan is the zero complex and gives zero
cohomology, so the same universal property includes the empty case.
(blueprint: lem-pc-base-derived-tensor-cohomology-canonical-cofan). -/
theorem baseDerivedTensorCohomology_canonical_cofan
    {I : Type u} (M : I → CochainComplex (ModuleCat.{u} A) ℤ)
    (S : CochainComplex (ModuleCat.{u} A) ℤ) (s : ∀ j, M j ⟶ S)
    (hs : IsColimit (Cofan.mk S s))
    (m : ∀ j, BaseDerivedTensorCohomologyModel R A B (M j) C)
    (mS : BaseDerivedTensorCohomologyModel R A B S C) (i : ℤ)
    (δ : ∀ j, (m j).derived ⟶ mS.derived)
    (g : ∀ j, (m j).cohomology i ⟶ mS.cohomology i)
    (hδ : ∀ j, Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) (δ j) ≫
      mS.counit = (m j).counit)
    (hg : ∀ j, (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map (g j) ≫
          (mS.cohomologyIso i).hom =
      ((m j).cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          ((m j).derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex
                (.up ℤ)).map (s j))))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          ((δ j).app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj S))))) :
    Nonempty (IsColimit (Cofan.mk (mS.cohomology i) g)) := by
  sorry

end ModuleCat
