/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.RingTheory.Localization.Basic

/-! # Fractions before transport to tensor cohomology models

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-localization-derived-fractions).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology

/-- The derived scalar-extension functor sends the localization unit to a map whose
homology classes admit fractions. The denominator acts by the derived image of
multiplication on the localized input complex, before any tensor-coefficient
module structure or chosen cohomology model is introduced.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-localization-derived-fractions).

Proof in words: take a K-flat R-resolution F of B concentrated in degree zero.
The balanced derived tensor calculation computes the functor on an A-complex Q
by the total complex Q tensor_R F. It computes the localized input by the
localization of this same total complex: localization commutes with tensor
products and the direct sums defining totalization, and is exact. Each element
of the localized total complex is a fraction z/s. A cycle represented by z/s
has differential zero after localization, so a further denominator t kills dz.
Then tz is a cycle and its cohomology class, with denominator ts, gives the
required equation. The denominator endomorphism is multiplication by the image
of ts on the localized input. The balanced calculation is natural for the unit
and these scalar endomorphisms. The universal counit identifies any supplied
left derived scalar-extension functor with this calculation, so applying
homology and transporting the cycle equation proves the displayed assertion.
This argument only clears finitely many denominators of an individual element,
so no boundedness of Q is needed. When zero lies in S, the localized complex is
zero and the zero denominator works; for S = {1} the unit is an isomorphism. -/
theorem derivedLocalization_fractions
    (R A Aq B : Type u) [CommRing R] [CommRing A] [CommRing Aq] [CommRing B]
    [Algebra R A] [Algebra R Aq] [Algebra R B] [Algebra A Aq]
    [IsScalarTower R A Aq]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (S : Submonoid A) [IsLocalization S Aq]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ F ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (i : ℤ) (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
      (F.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj
          ((restrict R Aq).obj ((extend A Aq).obj Q)))))) :
    ∃ (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        (F.obj (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ _).obj ((restrict R A).obj Q))))) (s : S),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (F.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
            ((restrict R Aq).map
              ((algebraMap A Aq (s : A)) • 𝟙 ((extend A Aq).obj Q)))))) y =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (F.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient _ _).map uQ))) x := by sorry

end RingTensorCohomology
