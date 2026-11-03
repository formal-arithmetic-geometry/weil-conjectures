/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointEvaluation.PointEvaluationTensorData
public import WeilConjectures.AlgebraicGeometry.PointEvaluation.PointEvaluationScalarTensor

/-! # Tensor square for balanced point scalar data

Source: Stacks Project, sites-cohomology.tex, Tag 07A4
(lemma-pullback-tensor-product), and sites-modules.tex, Tag 03EL
(lemma-tensor-product-pullback); normalized point specialization of the relative
Kunneth proof (blueprint: def-sf-point-evaluation-scalar-coherence).

`ScalarCoherent` requires the square of the specified chain maps to commute and
both canonical scalar extensions to preserve flat-term K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] SheafOfModules.monoidalCategory

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback

namespace AlgebraicGeometry.ProEtale.PointEvaluation

variable {k : Type u} [Field k]
  {B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}

/-- Coherence of normalized point evaluation with arbitrary change of coefficients.
The upper route evaluates the canonical sheaf scalar tensor comparison, applies
`T'.b`, and then applies `S.κ` to both factors. The lower route applies `S.κ`,
scalar-extends `T.b`, and applies the balanced ordinary comparison `S.ε`.
Both scalar extensions must preserve exactly the recorded flat-term K-flat class;
no flatness assumption on the coefficient map is made.
Source: Stacks 03EL and 07A4, normalized point specialization in the Kunneth proof
(blueprint: def-sf-point-evaluation-scalar-coherence). -/
structure ScalarCoherent
    {B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}
    (a : B ⟶ B') (T : TensorModel B) (T' : TensorModel B')
    (S : ScalarModel a T T') : Prop where
  /-- Equality of the two specified composites as chain maps, for every pair. -/
  tensor_square : ∀ P Q : Complexes B,
    (complexSections k B').map (epsilon.{u + 1, u + 1, u} a P Q).hom ≫
        (T'.b ((extend.{u + 1, u + 1, u} a).obj P)
          ((extend.{u + 1, u + 1, u} a).obj Q)).hom ≫
        (S.κ.hom.app P ⊗ₘ S.κ.hom.app Q) =
      S.κ.hom.app (totalObj B P Q) ≫
        (moduleExtend B a).map (T.b P Q).hom ≫
        (S.ε ((complexSections k B).obj P) ((complexSections k B).obj Q)).hom
  /-- Canonical sheaf scalar extension preserves the specified resolving class. -/
  sheaf_preserves_resolving : ∀ P : Complexes B, resolving B P →
    resolving B' ((extend.{u + 1, u + 1, u} a).obj P)
  /-- Ordinary scalar extension preserves the specified resolving class. -/
  module_preserves_resolving :
    ∀ P : CochainComplex (ModuleCat.{u + 1} (sectionRing k B)) ℤ,
      moduleResolving B P → moduleResolving B' ((moduleExtend B a).obj P)

end AlgebraicGeometry.ProEtale.PointEvaluation
