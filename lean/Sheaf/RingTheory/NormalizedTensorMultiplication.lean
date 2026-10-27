module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Multiplication into a normalized reduced tensor product

Source: Stacks Project, More on Algebra, Tags 09EM and 09II
(blueprint: def-sfb-normalized-tensor-multiplication).

The reduced generic tensor algebra `(L ⊗[K] P)_red`, the integral closure `C_P`
of `B` in it, the canonical multiplication `B ⊗[A] R_P → C_P` and its restriction
`R_P → C_P`, `r ↦ [1 ⊗ r]`, are defined here from Mathlib constructions only.
This module deliberately does not import the downstream Epp theorem module
(lem-sfb-epp-essentially-finite-type-traits), whose proof uses
lem-sfb-dvr-normalized-finite-stage-descent: its `eppReducedTensor`,
`eppUpperClosure` and `eppNormalizationMap` are the same constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- The reduced generic tensor algebra `(L ⊗[K] P)_red`, the quotient by the
ideal of all nilpotent elements.
Source: Stacks Project, More on Algebra, Tag 09EM
(blueprint: def-sfb-normalized-tensor-multiplication). -/
abbrev normalizedReducedTensor (K : Type w) (L : Type x) (P : Type y)
    [Field K] [Field L] [Field P] [Algebra K L] [Algebra K P] :=
  (L ⊗[K] P) ⧸ nilradical (L ⊗[K] P)

/-- The integral closure `C_P` of `B` in the reduced generic tensor algebra
`(L ⊗[K] P)_red`.
Source: Stacks Project, More on Algebra, Tags 09EM and 09II
(blueprint: def-sfb-normalized-tensor-multiplication). -/
abbrev normalizedUpperClosure (B : Type v) (K : Type w) (L : Type x) (P : Type y)
    [CommRing B] [Field K] [Field L] [Field P]
    [Algebra B L] [Algebra K L] [Algebra K P] :=
  integralClosure B (normalizedReducedTensor K L P)

/-- The canonical multiplication map from `B ⊗[A] R_P` into `C_P`.
Here `R_P = integralClosure A P` and `C_P = normalizedUpperClosure B K L P`.
It sends `b ⊗ r` to the product of the images of `b` and `r` in the reduced
algebra `L ⊗[K] P`. The tensor comparison into the integral closure of
`B ⊗[A] P`, followed by restriction of the canonical map to the reduced generic
algebra, constructs its data without any postponed proof.
Source: Stacks Project, More on Algebra, Tags 09EM and 09II, normalized tensor
construction and final finite-stage descent
(blueprint: def-sfb-normalized-tensor-multiplication). -/
noncomputable def normalizedTensorMultiplication
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (P : Type y)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field P]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K P] [Algebra A P] [IsScalarTower A K P] :
    B ⊗[A] integralClosure A P →+* normalizedUpperClosure B K L P :=
  ((Algebra.TensorProduct.lift (Algebra.ofId B (normalizedReducedTensor K L P))
    (((Ideal.Quotient.mkₐ K (nilradical (L ⊗[K] P))).comp
      Algebra.TensorProduct.includeRight).restrictScalars A)
    (fun _ _ ↦ Commute.all _ _)).mapIntegralClosure.comp
      (TensorProduct.toIntegralClosure A B P)).toRingHom

/-- The canonical normalization map `R_P → C_P`, `r ↦ [1 ⊗ r]`: the restriction
of the canonical multiplication to `1 ⊗ R_P`.
Source: Stacks Project, More on Algebra, Tag 09EM
(blueprint: def-sfb-normalized-tensor-multiplication). -/
noncomputable def normalizedLowerMap
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (P : Type y)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field P]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K P] [Algebra A P] [IsScalarTower A K P] :
    integralClosure A P →+* normalizedUpperClosure B K L P :=
  (normalizedTensorMultiplication A B K L P).comp
    (Algebra.TensorProduct.includeRight :
      integralClosure A P →ₐ[A] B ⊗[A] integralClosure A P).toRingHom

end IsDiscreteValuationRing
