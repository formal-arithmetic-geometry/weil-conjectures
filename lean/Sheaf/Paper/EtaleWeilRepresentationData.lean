/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Categories and tensor compatibility for etale Weil realization

The existing representation subcategory and compatibility predicate are kept here
so the independent Hom, reconstruction and tensor arguments can share their statements.
Source: Weil II (1.1.1), (1.1.6), (1.1.10)-(1.1.12).
(blueprint: new-p6-etale-weil-representation-data)
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

/-- Continuous finite-dimensional Weil representations, with the actual profinite
geometric group and the finite coefficient-field convention of Weil II (1.1.6).
Source: prop-wf-weil-sheaf-representation-equivalence
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
@[reducible] def etaleLisseWeilRepresentations (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (d : Monodromy.DegreeDatum G) (D : EtaleWeilDegreeData h t G d) :=
  ObjectProperty.FullSubcategory (fun V : Rep.{u + 1} Q G ↦
    Representation.IsLAdic l Q (ProfiniteGrp.of (Aut (fiber t))) V.V
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv Q V.V).toMonoidHom.comp
        (Representation.asGroupHom
          (V.ρ.comp (d.deg.ker.subtype.comp D.geom.toMonoidHom)))))

/-- Tensor compatibility refers to the recorded levelwise etale tensor and unit.
The two forgetful functors are monoidal, so the Weil and representation tensor
structures use those actual underlying operations.
Source: Weil II (1.1.1), (1.1.10)
(blueprint: prop-wf-weil-sheaf-representation-equivalence). -/
def etaleWeilTensorCompatibility
    (e : EtaleLisseWeilSheaf l Q h ≌ etaleLisseWeilRepresentations l Q h t d D) : Prop :=
  ∃ m₀ : MonoidalCategory (LisseAlgebraicSheaf l Y Q),
    m₀.toMonoidalCategoryStruct.tensorObj = lisseAlgebraicTensor l Y Q ∧
    m₀.toMonoidalCategoryStruct.tensorUnit = lisseAlgebraicUnit l Y Q ∧
    ∃ (mW : MonoidalCategory (EtaleLisseWeilSheaf l Q h))
      (mR : MonoidalCategory (etaleLisseWeilRepresentations l Q h t d D)),
      Nonempty (@Functor.Monoidal (EtaleLisseWeilSheaf l Q h) _ mW
        (LisseAlgebraicSheaf l Y Q) _ m₀
        (Endofunctor.IsoAlgebra.forget (lisseAlgebraicAutomorphismPullback h l Q))) ∧
      Nonempty (@Functor.Monoidal (etaleLisseWeilRepresentations l Q h t d D) _ mR
        (Rep.{u + 1} Q G) _ _ (ObjectProperty.ι _)) ∧
      Nonempty (@Functor.Monoidal (EtaleLisseWeilSheaf l Q h) _ mW
        (etaleLisseWeilRepresentations l Q h t d D) _ mR e.functor)

end AlgebraicGeometry.Scheme
