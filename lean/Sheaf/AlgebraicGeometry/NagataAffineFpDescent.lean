/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.Order.DirectedFiniteUpperBound
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Finite-stage model of a finitely presented affine algebra

Source: the Weil conjectures blueprint, `sec-nagata-compactification`,
`sk-prop-nagata-sketch-approximation`, node order 351
(blueprint: def-nagata-affine-fp-descent).

The record retains the individual coefficient lifts and the selected-upper-bound data.
Its equations fix the transported relations and the comparison on polynomial generators.
The tensor factors are written in the order `A ⊗ B_stage`, canonically equivalent to the
source's `B_stage ⊗ A`, so that the colimit algebra structure is Mathlib's left structure.
The scheme diagram and cone use the existing base-change construction, including its maps.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

open Classical in
/-- Chosen finite-stage descent data for a presented affine algebra (blueprint,
`sec-nagata-compactification`, node order 351).

The coefficient set is exactly the union of the nonzero coefficients of the relations.
Each coefficient has its own representative stage and lift. The common stage is precisely
`directedFiniteUpperBound` of their stages together with `lambda0`, using the base point,
binary bounds and auxiliary order of `def-nagata-directed-finite-upper-bound`.
The coefficient equations specify the transported polynomials, including zero coefficients.
Both algebra presentations are retained; the tensor presentation preserves each variable,
and `beta` is its composite with the inverse of the given presentation of the colimit algebra.
Thus the comparison is the identity on presentations, not an arbitrary algebra homomorphism.
No independence of the choices is asserted. Existence of coefficient lifts is supplied by
`lemma-nagata-filtered-colimit-finite-data`; the stage inequalities follow from
`lemma-nagata-directed-finite-upper-bound`.
(blueprint: def-nagata-affine-fp-descent). -/
structure NagataAffineFpDescent {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (F : I ⥤ CommRingCat.{u}) (lambda0 : I)
    (n m : ℕ) (relations : Fin m → MvPolynomial (Fin n) (↑(colimit F))) where
  /-- The auxiliary choices defining the selected upper-bound function. -/
  boundBase : I
  boundPair : I → I → I
  boundPair_le : ∀ i j, i ≤ boundPair i j ∧ j ≤ boundPair i j
  boundOrder : LinearOrder I
  /-- Exactly the finite set of coefficients occurring in the relations. -/
  coefficients : Finset (↑(colimit F))
  coefficients_eq : coefficients =
    Finset.univ.biUnion (fun j ↦ (relations j).support.image (relations j).coeff)
  /-- Individual representative stages and values, one for each coefficient. -/
  liftStage : coefficients → I
  liftValue : ∀ k : coefficients, F.obj (liftStage k)
  liftValue_colimit : ∀ k, colimit.ι F (liftStage k) (liftValue k) = k.val
  /-- The selected common upper bound, including the fixed base stage. -/
  stage : I
  stage_eq : stage = directedFiniteUpperBound boundBase boundPair boundOrder
    (insert lambda0 (coefficients.attach.image liftStage))
  stage_ge : lambda0 ≤ stage
  liftStage_le : ∀ k, liftStage k ≤ stage
  /-- Polynomial coefficients are the transported chosen lifts, and zero off the support. -/
  relationMap : Fin m → MvPolynomial (Fin n) (F.obj stage)
  relationMap_coeff : ∀ j a, a ∈ (relations j).support →
    ∃ k : coefficients, k.val = (relations j).coeff a ∧
      (relationMap j).coeff a = F.map (homOfLE (liftStage_le k)) (liftValue k)
  relationMap_coeff_zero : ∀ j a, a ∉ (relations j).support → (relationMap j).coeff a = 0
  relationMap_colimit : ∀ j,
    MvPolynomial.map (colimit.ι F stage).hom (relationMap j) = relations j
  /-- The finite-stage algebra with its transported quotient presentation. -/
  stageAlgebra : Type u
  [stageAlgebraCommRing : CommRing stageAlgebra]
  [stageAlgebraAlgebra : Algebra (F.obj stage) stageAlgebra]
  stagePresentation : stageAlgebra ≃ₐ[F.obj stage]
    (MvPolynomial (Fin n) (F.obj stage) ⧸ Ideal.span (Set.range relationMap))
  /-- The given colimit algebra and its chosen finite presentation. -/
  algebra : Type u
  [algebraCommRing : CommRing algebra]
  [algebraStructure : Algebra (↑(colimit F)) algebra]
  presentation : algebra ≃ₐ[↑(colimit F)]
    (MvPolynomial (Fin n) (↑(colimit F)) ⧸ Ideal.span (Set.range relations))
  /-- The stage-to-colimit scalar structure is exactly the colimit structure map. -/
  [colimitAlgebra : Algebra (F.obj stage) (↑(colimit F))]
  colimitAlgebra_map : algebraMap (F.obj stage) (↑(colimit F)) = (colimit.ι F stage).hom
  /-- The usual tensor quotient identification, fixed on every variable. -/
  tensorPresentation :
    (↑(colimit F) ⊗[F.obj stage] stageAlgebra) ≃ₐ[↑(colimit F)]
      (MvPolynomial (Fin n) (↑(colimit F)) ⧸ Ideal.span (Set.range relations))
  tensorPresentation_variable : ∀ i : Fin n,
    tensorPresentation (1 ⊗ₜ[F.obj stage] stagePresentation.symm
      (Ideal.Quotient.mk (Ideal.span (Set.range relationMap)) (MvPolynomial.X i))) =
      Ideal.Quotient.mk (Ideal.span (Set.range relations)) (MvPolynomial.X i)
  /-- The induced comparison, the identity under the two quotient presentations. -/
  beta : (↑(colimit F) ⊗[F.obj stage] stageAlgebra) →ₐ[↑(colimit F)] algebra
  beta_eq : beta = presentation.symm.toAlgHom.comp tensorPresentation.toAlgHom

attribute [instance] NagataAffineFpDescent.stageAlgebraCommRing
  NagataAffineFpDescent.stageAlgebraAlgebra NagataAffineFpDescent.algebraCommRing
  NagataAffineFpDescent.algebraStructure NagataAffineFpDescent.colimitAlgebra

namespace NagataAffineFpDescent

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {F : I ⥤ CommRingCat.{u}} {lambda0 : I} {n m : ℕ}
  {relations : Fin m → MvPolynomial (Fin n) (↑(colimit F))}

/-- The finite-stage spectrum over its selected base stage. Source: blueprint,
`sec-nagata-compactification`, node order 351 (blueprint: def-nagata-affine-fp-descent). -/
noncomputable def stageMorphism (E : NagataAffineFpDescent F lambda0 n m relations) :
    Spec (.of E.stageAlgebra) ⟶ Spec (F.obj E.stage) :=
  Spec.map (CommRingCat.ofHom (algebraMap (F.obj E.stage) E.stageAlgebra))

/-- The same spectrum over the originally fixed base stage. Source: blueprint,
`sec-nagata-compactification`, node order 351 (blueprint: def-nagata-affine-fp-descent). -/
noncomputable def baseMorphism (E : NagataAffineFpDescent F lambda0 n m relations) :
    Spec (.of E.stageAlgebra) ⟶ Spec (F.obj lambda0) :=
  E.stageMorphism ≫ Spec.map (F.map (homOfLE E.stage_ge))

/-- The base-changed inverse system starting at the selected coefficient stage, with all
transition maps, using `def-nagata-basechanged-system`. Its objects are fibre products of
`Spec B_stage` with `Spec A_j`, hence the spectra of their tensor products.
Source: blueprint, `sec-nagata-compactification`, node order 351
(blueprint: def-nagata-affine-fp-descent). -/
noncomputable def baseChanged (E : NagataAffineFpDescent F lambda0 n m relations) :
    Over (Opposite.op E.stage) ⥤ Scheme.{u} :=
  baseChangeDiagram (F.op ⋙ Scheme.Spec) (i := Opposite.op E.stage) E.stageMorphism

/-- The base-changed cone, including its projections and its limit term
`Spec B_stage ×[Spec A_stage] Spec A`, the affine tensor-product spectrum in the source.
The assertion that this cone is limiting belongs to the base-change limit lemma.
Source: blueprint, `sec-nagata-compactification`, node order 351
(blueprint: def-nagata-affine-fp-descent). -/
noncomputable def baseChangedCone (E : NagataAffineFpDescent F lambda0 n m relations) :
    Cone E.baseChanged :=
  baseChangeCone (F.op ⋙ Scheme.Spec) (i := Opposite.op E.stage)
    (Scheme.Spec.mapCone (colimit.cocone F).op) E.stageMorphism

/-- The base-changed limit term. Source: blueprint, `sec-nagata-compactification`,
node order 351 (blueprint: def-nagata-affine-fp-descent). -/
noncomputable def baseChangedLimit (E : NagataAffineFpDescent F lambda0 n m relations) :
    Scheme.{u} :=
  E.baseChangedCone.pt

end NagataAffineFpDescent
end AlgebraicGeometry
