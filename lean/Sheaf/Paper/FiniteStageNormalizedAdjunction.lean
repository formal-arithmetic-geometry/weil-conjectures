/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.FiniteCoefficientAdjointData

/-! # Normalized adjunction at one finite coefficient stage

Source: current blueprint reduction-exceptional, Locality and Charts, with the
ordinary closed-chart preservation argument in the parent node, proof steps 1--4.
(blueprint: lem-pur-finite-stage-normalized-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

/-- A single compactification and coefficient stage have a unique adjunction with the
specified transported geometric counit.

Source: current blueprint reduction-exceptional, Locality and Charts; parent
lem-pur-finite-coefficient-adjoint-comparisons, proof steps 1--4.
(blueprint: lem-pur-finite-stage-normalized-adjunction).

Proof: the positive base-uniformizer quotient is a finite local primary ring by
local_field_coefficient_stages. Identify its ideal with an upper-uniformizer power
using stage_ramification. Finite-type schemes over k are Noetherian. On the etale
site finiteTor_directImage_coefficients and the exact open extension, whose stalks
are the original stalks or zero, show that Rg_* j_! preserves bounded constructible
finite-Tor objects. The finite affine factorization and gluing theorem supplies a
finite closed affine-space chart cover. On each chart the closed-chart exceptional
preservation theorem bounds the etale right adjoint. Gluing the finite intervals
gives global preservation. Transfer along the finite-Tor site equivalence and the
specified compact-support comparison. The comparison unit identifies Rnu_* of an
etale-origin object with its bounded etale antecedent, giving etaleBound. The Hom
bijection is the compact-support comparison followed by the site adjunction and
etale adjunction; its inverse has exactly the displayed counit normalization.
Restrict to the full finite-Tor subcategories. For uniqueness all preservation and
bound fields are proofs. The normalization fixes every counit component, and an
adjunction on the fixed functors is determined by its counit, hence the whole
AdjointDatum is unique. This works for the zero complex and empty schemes, and
uses neither smoothness nor perfection of k. -/
theorem finite_stage_normalized_adjunction
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (s : Stage l E) (c : Compactification f) :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    letI := (finiteTypeMorphismProperties k f).1
    letI := (finiteTypeMorphismProperties k f).2.1
    letI := (finiteTypeMorphismProperties k f).2.2
    ∃! d : AdjointDatum s.ring c, True := by sorry

end AlgebraicGeometry.FiniteCoefficientAdjoints
