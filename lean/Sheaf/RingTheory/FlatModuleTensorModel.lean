/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Sheaf.RingTheory.ColimitEventuallyFlat
import Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import Sheaf.RingTheory.FlatModuleAtPrime
import Sheaf.RingTheory.LimitModuleFinitePresentation
import Sheaf.RingTheory.OpenFlatLocus

/-! # A flat model of a scalar extension of a finitely presented module

Source: Stacks Project, Algebra, Tag 02JO (1).
(blueprint: lem-pc-flat-module-tensor-model)
-/

@[expose] public section

universe v w

open scoped TensorProduct

namespace AlgebraicGeometry

/-- A flat scalar extension has a flat model over a finitely presented integer algebra.

Source: Stacks Project, Algebra, Tag 02JO (1), with the tensor identifications in (3).
(blueprint: lem-pc-flat-module-tensor-model)

Proof:
1. Give B its A-algebra structure through f. Since A is finite type over R and B
   is finitely presented over R, B is finitely presented over A. Tensor cancellation
   identifies C tensor_R B with (C tensor_R A) tensor_A B, and identifies its
   base change of M with (C tensor_R A) tensor_A M. Thus the algebra and module
   are finitely presented over their respective bases, and the module is flat
   over C tensor_R A by the hypothesis.
2. Apply finite-presentation approximation (Tag 00R1) to this algebra and module.
   The approximating base rings P and top rings Q are finite type over the
   integers and P respectively; they are Noetherian, so the finite modules L
   are finitely presented. Their transition squares and module maps are base changes.
3. At each prime of the limit top ring, localize the approximation at its contractions.
   Localization commutes with the colimits and the tensor base changes. The localized
   limit is flat over the localized base. Tag 00R6 gives a flat localized stage.
4. The flat loci are open by Tag 00RC and persist under base change and localization.
   Their inverse images cover the limit spectrum. Quasi-compactness gives one stage
   whose flat locus pulls back to the entire limit spectrum.
5. Write the closed complement as V(J). Its image ideal in the limit ring is the
   unit ideal. Lift the finitely many coefficients of a unit relation to a stage,
   and then lift its equality to 1. Persistence makes the entire later spectrum
   flat. The prime-local criterion makes L flat over P.
6. The approximation supplies the canonical algebra isomorphism e and its
   compatibility with the base inclusion. Its module base-change isomorphism is
   linear over C tensor_R B, with the Q-action induced by e on the right inclusion.
   Finite type over Noetherian rings gives the stated finite presentations.
-/
theorem exists_flat_module_tensor_model
    {R C : Type v} {A B M : Type w}
    [CommRing R] [CommRing C] [CommRing A] [CommRing B] [AddCommMonoid M]
    [Algebra R C] [Algebra R A] [Algebra R B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B]
    [Module B M] [Module.FinitePresentation B M] (f : A →ₐ[R] B)
    (hflat : letI : Module A M := Module.compHom M f.toRingHom
      letI : Algebra A (C ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
      Module.Flat (C ⊗[R] A) ((C ⊗[R] A) ⊗[A] M)) :
    ∃ (P Q L : Type (max v w)) (_ : CommRing P) (_ : CommRing Q)
      (_ : Algebra P Q) (_ : AddCommMonoid L) (_ : Module Q L)
      (_ : Algebra P (C ⊗[R] A)),
      Algebra.FinitePresentation ℤ P ∧ Algebra.FinitePresentation P Q ∧
      Module.FinitePresentation Q L ∧
      (letI : Module P L := Module.compHom L (algebraMap P Q); Module.Flat P L) ∧
      ∃ e : (C ⊗[R] A) ⊗[P] Q ≃+* C ⊗[R] B,
        e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
          (Algebra.TensorProduct.map (Algebra.ofId C C) f).toRingHom ∧
        (letI : Algebra Q (C ⊗[R] B) :=
          (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
         letI : Algebra B (C ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
         Nonempty ((C ⊗[R] B) ⊗[Q] L ≃ₗ[C ⊗[R] B] (C ⊗[R] B) ⊗[B] M)) := by
  sorry

end AlgebraicGeometry
