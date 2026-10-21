/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.EtaleWeilRealization

/-! # Tensor compatibility of the actual etale Weil realization

Source: Weil II (1.1.1), (1.1.12), steps 9 and 10 of the equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable (l : ℕ) [Fact l.Prime] (Q : Type (u + 1)) [Field Q]
  [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  {Y : Scheme.{u}} [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (h : Y ≅ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ Y) {G : Type v} [Group G]
  (d : Monodromy.DegreeDatum G) (D : EtaleWeilDegreeData h t G d)

/-- The specified realization has strong monoidal constraints for the actual tensors.
Source: Weil II (1.1.1), (1.1.12); steps 9 and 10 of
prop-wf-weil-sheaf-representation-equivalence.
(blueprint: new-p6-etale-weil-tensor)

Proof: use the monoidal structures and tensor and unit identifications of the
algebraic clause of cor-galois-lisse-representations for the underlying lisse
category, retaining lisseAlgebraicTensor and lisseAlgebraicUnit as its objects.
Reindexing by h commutes with the sectionwise finite tensor presheaf and its
sheafification; take this comparison levelwise on integral systems, then extend
it through rationalization and common coefficient extension. These comparisons
are fixed on sections and pure tensors, so their associativity and unit diagrams
commute. They make h^* strong monoidal. Its invertible algebras inherit tensor
with descent phi_F tensor phi_H, and the forgetful functor is strong monoidal.
At finite coefficients a path respects products by naturality with both projections.
Naturality with the map (x,y) to x tensor y then shows it sends a pure tensor to
the tensor of its images. Naturality with constant sections fixes the unit.
Limit projections and both coefficient extensions give these same statements
for etaleAlgebraicPathIso. Thus the degree-one operator on a Weil tensor is
T_F tensor T_H, and the unit has trivial operator. The geometric actions already
respect the tensor by the underlying dictionary. Since every Weil element is
a geometric element times a power of s, the tensor comparison intertwines all
of G. The l-adic full subcategory is closed under tensor and contains the unit,
by tensoring the finite coefficient models over a common finite extension.
It therefore inherits the representation tensor, with strong monoidal inclusion.
The normalized fibre tensor and unit comparisons give the strong monoidal
realization. Naturality and all coherence identities can be checked after the
faithful underlying vector-space functor, where they are the same pure-tensor
identities as at finite levels. This includes zero tensors and the unit without
any nonzero-rank assumptions. -/
theorem etaleWeilTensor [ConnectedSpace Y]
    (e : EtaleLisseWeilSheaf l Q h ≌ etaleLisseWeilRepresentations l Q h t d D)
    (he : e.functor = etaleWeilRealization l Q h t d D) :
    etaleWeilTensorCompatibility l Q h t d D e := by sorry

end AlgebraicGeometry.Scheme
