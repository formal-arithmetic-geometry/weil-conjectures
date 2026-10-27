/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveRepresentationLinearization
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.GroupSchemeLinearization
public import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis

/-! # Coordinates for projective rational representations

Source: MFK, Geometric Invariant Theory, Chapter 1, §1 and Chapter 2, §1;
Morrison, arXiv:0810.2340, §2.1--2.2, pp.5--7
(blueprint: def-sfb-projective-representation-coordinates).

A basis identifies V with its coordinate vector space. The pulled-back line, its coordinate
sections, the induced linearization of an equivariant embedding and vector lifts are those of
def-sfb-projective-representation-linearization (`line`, `coordinate`, `LinearizedEmbedding`,
`IsVectorLift`); this module adds only the coordinate SL(E), the space of lines in V and the
restricted one-parameter coaction with its negative-weight predicate.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.ProjectiveRepresentation

variable {k : Type u} [Field k]

/-- Coordinate model of SL(E), after choosing coordinates on E. Every finite-dimensional
E has this model, and changing coordinates conjugates all homomorphisms in the criterion.
Source: MFK, Chapter 2, §1 (blueprint: def-sfb-projective-representation-coordinates). -/
abbrev specialLinear (E : Type v) [AddCommGroup E] [Module k E] :
    Grp (Over (Spec (.of k))) :=
  ⟨LinearGroupSchemes.specialLinear k (Module.finrank k E)⟩

/-- Projective space of lines in V, in coordinates: its homogeneous coordinates are
linear forms on V, so its O(1) is the dual tautological line, not the tautological line.
This is the target of `LinearizedEmbedding` and `IsVectorLift` of
def-sfb-projective-representation-linearization, for the index type of a basis of V.
Source: Morrison §2.1 (blueprint: def-sfb-projective-representation-coordinates). -/
abbrev lines (V : Type w) [AddCommGroup V] [Module k V] : Over (Spec (.of k)) :=
  (ℙ(LinearGroupSchemes.Index (Module.finrank k V); Spec (.of k))).asOver (Spec (.of k))

variable {V : Type w} [AddCommGroup V] [Module k V]
variable {E : Type v} [AddCommGroup E] [Module k E]

/-- The restricted coaction obtained by evaluating rho o lambda at the universal Laurent
point t. Its columns are the images of the basis vectors; this is an actual linear map.
Source: Milne, Theorem 12.12; MFK, Chapter 2, §1
(blueprint: def-sfb-projective-representation-coordinates). -/
def restrictedCoaction
    (b : Module.Basis (LinearGroupSchemes.Index (Module.finrank k V)) k V)
    (ρ : (specialLinear (k := k) E).X ⟶
      GeneralLinearGroup (LinearGroupSchemes.Index (Module.finrank k V)) k)
    (lam : StandardGroupSchemes.multiplicative k ⟶ (specialLinear (k := k) E).X) :
    V →ₗ[k] V ⊗[k] LaurentPolynomial k :=
  b.constr k fun q ↦
    ∑ i : LinearGroupSchemes.Index (Module.finrank k V),
      b i ⊗ₜ[k] (GeneralLinearGroup.homMulEquiv
        (LinearGroupSchemes.Index (Module.finrank k V)) k (LaurentPolynomial k) (lam ≫ ρ) i q)

/-- The minimum occurring weight is negative exactly when a negative component in the
finite weight decomposition is nonzero. Internal directness makes this decomposition
unique. It uses the recorded weight spaces, with the lines/minimum sign convention.
Source: MFK, Theorem 2.1; Morrison §2.2
(blueprint: def-sfb-projective-representation-coordinates). -/
def HasNegativeWeight (c : V →ₗ[k] V ⊗[k] LaurentPolynomial k) (v : V) : Prop :=
  ∃ z : ℤ →₀ V,
    (∀ a : ℤ, z a ∈ GmRepresentation.weightSpace c a) ∧
      z.sum (fun _ x ↦ x) = v ∧ ∃ a : ℤ, a < 0 ∧ z a ≠ 0

end AlgebraicGeometry.ProjectiveRepresentation
