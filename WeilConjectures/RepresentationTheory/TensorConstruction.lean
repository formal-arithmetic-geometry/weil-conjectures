/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation

/-!
# Tensor constructions on a representation

A *tensor construction* on a representation `ρ` of a group `W` on `V` is a representation obtained
from `ρ` and its contragredient `ρ^∨` by finitely many tensor products, direct sums, exterior
powers and subquotients by `W`-stable subspaces. Such representations are taken up to
equivalence.

In the purity argument `W` is the Weil group `W(U₀)` and `ρ` a Weil representation; a central
element of the arithmetic monodromy group acts on every tensor construction, and on its simple
subquotients by scalars.

## Main declarations

* `Representation.IsTensorConstruction`: `σ` is a tensor construction on `ρ`.
* `Representation.IsTensorConstruction.subrepresentation`: a subrepresentation of a tensor
  construction is a tensor construction.

## Blueprint

`Representation.IsTensorConstruction` implements `definition-tensor-construction` and its clause
`definition-tensor-construction--1`.
-/

@[expose] public section

universe u

namespace Representation

variable {k : Type u} [Field k] {W : Type*} [Group W] {V : Type u} [AddCommGroup V] [Module k V]

/-- A *tensor construction* on a representation `ρ` of `W` on `V`: a representation obtained from
`ρ` and its contragredient `ρ^∨` by finitely many tensor products, (binary) direct sums, exterior
powers and subquotients `S ⧸ U` by `W`-stable subspaces `U ≤ S`, up to equivalence of
representations.
(blueprint: `definition-tensor-construction`, `definition-tensor-construction--1`) -/
inductive IsTensorConstruction (ρ : Representation k W V) :
    {U : Type u} → [AddCommGroup U] → [Module k U] → Representation k W U → Prop
  /-- `ρ` itself is a tensor construction on `ρ`. -/
  | self : IsTensorConstruction ρ ρ
  /-- The contragredient `ρ^∨` is a tensor construction on `ρ`. -/
  | dual : IsTensorConstruction ρ ρ.dual
  /-- The tensor product of two tensor constructions is a tensor construction. -/
  | tprod {U₁ U₂ : Type u} [AddCommGroup U₁] [Module k U₁] [AddCommGroup U₂] [Module k U₂]
      {σ₁ : Representation k W U₁} {σ₂ : Representation k W U₂} :
      IsTensorConstruction ρ σ₁ → IsTensorConstruction ρ σ₂ →
        IsTensorConstruction ρ (σ₁.tprod σ₂)
  /-- The direct sum of two tensor constructions is a tensor construction. -/
  | prod {U₁ U₂ : Type u} [AddCommGroup U₁] [Module k U₁] [AddCommGroup U₂] [Module k U₂]
      {σ₁ : Representation k W U₁} {σ₂ : Representation k W U₂} :
      IsTensorConstruction ρ σ₁ → IsTensorConstruction ρ σ₂ →
        IsTensorConstruction ρ (σ₁.prod σ₂)
  /-- An exterior power of a tensor construction is a tensor construction. -/
  | exteriorPower {U : Type u} [AddCommGroup U] [Module k U] {σ : Representation k W U} :
      IsTensorConstruction ρ σ → ∀ r : ℕ, IsTensorConstruction ρ (σ.exteriorPower r)
  /-- A subquotient `S ⧸ U` of a tensor construction by `W`-stable subspaces `U ≤ S` is a tensor
  construction. -/
  | subquotient {U : Type u} [AddCommGroup U] [Module k U] {σ : Representation k W U} :
      IsTensorConstruction ρ σ → ∀ S T : Subrepresentation σ, T ≤ S →
        IsTensorConstruction ρ (S.subquotient T)
  /-- A representation equivalent to a tensor construction is a tensor construction. -/
  | of_equiv {U₁ U₂ : Type u} [AddCommGroup U₁] [Module k U₁] [AddCommGroup U₂] [Module k U₂]
      {σ₁ : Representation k W U₁} {σ₂ : Representation k W U₂} :
      IsTensorConstruction ρ σ₁ → σ₁.Equiv σ₂ → IsTensorConstruction ρ σ₂

namespace IsTensorConstruction

variable {ρ : Representation k W V} {U : Type u} [AddCommGroup U] [Module k U]
  {σ : Representation k W U}

/-- A subrepresentation of a tensor construction is a tensor construction: it is the subquotient
`S ⧸ 0`. -/
theorem subrepresentation (h : IsTensorConstruction ρ σ) (S : Subrepresentation σ) :
    IsTensorConstruction ρ S.toRepresentation :=
  (h.subquotient S ⊥ bot_le).of_equiv S.subquotientBotEquiv

end IsTensorConstruction

end Representation
