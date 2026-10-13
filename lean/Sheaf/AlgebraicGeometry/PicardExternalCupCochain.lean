/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.PicardKunnethResolutionModel
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

import Sheaf.Algebra.Homology.TensorKunnethNat

/-! # Cochain realization of the external cup product

Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV; Varieties, Tag 0BED.
(blueprint: lem-sc-picard-external-cup-cochain).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The tensor total complex of the two actual scalar sections models.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-cochain). -/
noncomputable abbrev picardExternalTotal
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) : CochainComplex (ModuleCat.{w} k) ℤ :=
  HomologicalComplex.mapBifunctor (picardScalarModel f F) (picardScalarModel g G)
    (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)

/-- Normalization of a specified cochain map on tensor cycles. This imposes only the
external cup formula, not injectivity or surjectivity on homology.
Source: Stacks, Tags 01FD, 07MB and 0FKV; equation 33.29.1.1 of Tag 0BED
(blueprint: lem-sc-picard-external-cup-cochain). -/
def IsPicardExternalCupCochain
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)) : Prop :=
  ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : (picardScalarModel f F).cycles (i.val.1 : ℤ))
    (b : (picardScalarModel g G).cycles (i.val.2 : ℤ))
    (z : (picardExternalTotal f g F G).cycles (n : ℤ)),
    (picardExternalTotal f g F G).iCycles (n : ℤ) z =
      HomologicalComplex.ιMapBifunctor (picardScalarModel f F) (picardScalarModel g G)
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
        (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ) (by
          change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
          exact_mod_cast i.property)
        (((picardScalarModel f F).iCycles (i.val.1 : ℤ) a) ⊗ₜ[k]
          ((picardScalarModel g G).iCycles (i.val.2 : ℤ) b)) →
    picardScalarModelEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n
        (HomologicalComplex.homologyMap c (n : ℤ)
          ((picardExternalTotal f g F G).homologyπ (n : ℤ) z)) =
      cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) d)) i.property)
        (externalCup f g F G i.val.1 i.val.2
          (picardScalarModelEquiv f F i.val.1
            ((picardScalarModel f F).homologyπ (i.val.1 : ℤ) a))
          (picardScalarModelEquiv g G i.val.2
            ((picardScalarModel g G).homologyπ (i.val.2 : ℤ) b)))

/-- External cup admits a cochain realization between the explicitly constructed models.
This asserts no geometric Kunneth isomorphism and needs no compactness or affine diagonal.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV;
Varieties, Tag 0BED, construction before equation 33.29.1.1
(blueprint: lem-sc-picard-external-cup-cochain).

Proof: Resolve the coefficient sheaves, compute the projection pullbacks on resolution
representatives, and use the signed tensor pairing of Tag 0FKV followed by the
coefficient map from derived tensor to ordinary tensor. Tags 01FD and 07MB identify
this pairing on cocycle tensors with pullback followed by cup. The scalar Ext
comparison identifies it with the recorded externalCup operation, k-bilinearly.
To obtain a map on the fixed sections models rather than on a Godement model,
use the following explicit vector-space lifting argument. In each degree choose a
complement of boundaries in cycles and a complement of cycles in the term. The
latter complement maps isomorphically onto the next boundaries. Thus each complex
is the direct sum of its homology representatives with zero differential and pairs
mapped isomorphically by the differential. Projection to the homology representatives
and inclusion of them are cochain maps inducing the identity on homology. The field
linear tensor Kunneth map identifies homology of the tensor total with the sum of
factor homology tensors. Define a map on that homology by the bilinear external cup
on each summand, using picardScalarModelEquiv on all three models; include it into
the homology representatives of the product model. Composing with projection of
the tensor total gives the required cochain map c. Its homology map has exactly the
specified value on every tensor cycle by the tensor Kunneth cycle formula.
If two total cycles have the specified inclusion, monicity of iCycles identifies
them, so the formula holds for the arbitrary z in the statement. All negative
terms are zero, and the construction includes zero sheaves and empty schemes. -/
theorem picardExternalCupCochain_exists
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ∃ c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G),
      IsPicardExternalCupCochain f g F G c := by sorry

end AlgebraicGeometry.Scheme.Modules
