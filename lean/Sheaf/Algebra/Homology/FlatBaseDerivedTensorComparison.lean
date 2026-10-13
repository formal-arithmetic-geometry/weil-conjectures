/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.RingTheory.Flat.Basic

/-! # Localized base-derived tensor comparison for K-flat complexes

Source: Stacks Project, Tags 06Y6 and 0A1D, condition (1) of Tag 0DJ8.
(blueprint: lem-pc-flat-base-derived-tensor-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ModuleCat

/-- K-flatness over the base and a flat final extension make the canonical localized
comparison invertible. Source: Stacks Project, Tags 06Y6 and 0A1D (Tag 0DJ8 (1)).
(blueprint: lem-pc-flat-base-derived-tensor-comparison).

Proof: Put P = Q restricted from A to R and E = A ⊗[R] B. Since tensoring P with
every acyclic R-complex is acyclic, P is K-flat, and the identity resolution computes
P ⊗ᴸ[R] B. The universal derived counit is thus invertible at P. In comparison_eq,
all other factors are isomorphisms; restriction of scalars reflects isomorphisms,
so comparison i is invertible. Since D is E-flat, scalar extension E → D is exact
and its canonical homology comparison is invertible. Tensor associativity identifies
the scalar extension of E ⊗[A] Q with D ⊗[A] Q. Its map on elementary tensors is
the one specified by ordinaryToLocalized_tmul. Thus localized_eq identifies
localizedComparison with the composite of the scalar extension of comparison and
this exact homology comparison, followed by tensor associativity. Every factor is
invertible. This argument works for unbounded K-flat Q as well, and for the zero
complex or zero coefficient ring; it requires no flatness of A or B over R. -/
theorem localizedComparison_isIso_of_kFlat_flat
    {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L
        (((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q)
        (MonoidalCategory.curriedTensor _)).Acyclic)
    (hD : Module.Flat (A ⊗[R] B) D)
    (M : BaseDerivedTensorCohomologyModel R A B Q D) :
    ∀ i : ℤ, IsIso (M.localizedComparison i) := by sorry

end ModuleCat
