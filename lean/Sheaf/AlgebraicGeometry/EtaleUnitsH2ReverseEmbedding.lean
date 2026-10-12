/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.FieldTheory.GaloisUnitsCohomology
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.AlgebraicGeometry.EtaleFieldSectionsInvariants
import Sheaf.AlgebraicGeometry.EtaleUnitsStalkRepresentation
import Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison
import Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation
import Mathlib.FieldTheory.Galois.Profinite

/-! Directional degree-two comparison over a field. -/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Etale unit H2 embeds into Galois unit H2.

Source: Stacks Project, Tags 04JQ, 03QU, Example 03QV (2), and Section 0DVG.
(blueprint: lem-sc-etale-units-h2-reverse-embedding).

Proof: Choose an algebraic closure of the separable closure as geometric residue field.
The abelian geometric stalk equivalence identifies the stalk of the units sheaf with
separable-closure units, with their natural Galois action: every germ is represented over
some finite separable extension, and the action on germs is induced by the automorphism
of that extension. Under this equivalence global sections are invariants. Transport
an injective resolution across the exact equivalence; injectives remain injective.
Continuous cochains compute derived invariants: lifting the finite image of a continuous
cochain on compact powers gives exactness, and embedding into locally constant coinduced
functions effaces positive degrees by the insertion homotopy. More explicitly, embed
m by the orbit function x ↦ x • m and act on functions by right translation. Such
functions have open stabilizers: compactness makes their locally constant partitions
finite and allows a common open subgroup. On cochains with these coefficients use
h_n(F)(g1,...,g(n-1))(x) = F(x,g1,...,g(n-1))(1). The alternating differential terms
cancel in d h + h d = 1 for positive degrees. Continuity into the discrete function
module follows from the same finite-partition and common-open-subgroup argument.
Hence the embedding kills positive cohomology.
The cochain delta-functor is therefore universal. Its degree-zero identification
with invariants extends uniquely to mutually inverse morphisms of delta-functors,
so it computes derived invariants in every degree. For the homogeneous model used in
GaloisUnitsH2, the compact-open exponential law on compact Hausdorff finite powers
identifies iterated continuous maps with jointly continuous maps. Evaluate a homogeneous
n-cochain at (1, g1, g1*g2, ..., g1*...*gn); the inverse sends c to
(g0, ..., gn) ↦ g0 • c(g0⁻¹*g1, ..., g(n-1)⁻¹*gn). Equivariance makes these inverse,
and alternating omission becomes the inhomogeneous differential. Thus these maps induce
inverse maps on degree-two cohomology. Canonical lift/down is additive and equivariant
and removes the coefficient universe lift. Composing gives inverse maps on classes.
Use the reverse comparison on degree-two classes. If two images agree, apply the
inverse map on classes to this equality. Its composite with the reverse map is the
identity, so the original classes were equal. This proves only injectivity in this direction. -/
theorem nonempty_embedding_cohomologicalBrauerGroup_galoisUnitsH2 (K : Type u) [Field K] :
    Nonempty ((Spec (.of K)).CohomologicalBrauerGroup ↪ Field.GaloisUnitsH2 K) := by
  classical
  let Ω := AlgebraicClosure K
  obtain ⟨E, _, i, _, _, haction, _⟩ :=
    abelianSheaves_equiv_discreteGModules.{u, 0} K (SeparableClosure K) Ω
  obtain ⟨η⟩ := nonempty_iso_etaleFieldSections_invariants
    K (SeparableClosure K) Ω E i haction
  obtain ⟨e, he⟩ := exists_etaleUnits_stalk_linearEquiv K Ω E i haction
  let S := Spec (.of K)
  let Γ := (CategoryTheory.sheafToPresheaf S.smallEtaleTopology
    AddCommGrpCat.{u + 1}).comp
      ((CategoryTheory.evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Opposite.op (Scheme.Etale.mk (CategoryTheory.CategoryStruct.id S))))
  obtain ⟨a⟩ := CategoryTheory.Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    S.smallEtaleTopology (Scheme.Etale.mk (CategoryTheory.CategoryStruct.id S))
    (CategoryTheory.MorphismProperty.Over.mkIdTerminal _ S) S.gmSheaf 1
  have : DiscreteTopology (Field.galoisUnitsTopRep K).V := ⟨rfl⟩
  obtain ⟨b⟩ := Rep.nonempty_equiv_rightDerived_continuousCohomology.{u, u + 2, u + 1, u + 1, u}
    (Gal(SeparableClosure K/K)) _ E Γ η S.gmSheaf (Field.galoisUnitsTopRep K) e he 2
  exact ⟨(a.toEquiv.trans b).toEmbedding⟩

end AlgebraicGeometry.Scheme
