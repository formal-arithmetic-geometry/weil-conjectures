/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModelExistence
import WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteQuotientCalculusExistence
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SFDualizableBiduality

/-! # Core normalized coefficient reduction witness

Source: Stacks 06YS, 06YY, 07A4, 07A6 and 0941
(blueprint: lem-coef-normalized-reduction-models-core).
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Coefficient duality restricts to an anti-equivalence on dualizable complexes over
Λ_X = p_X^* Λ, with its actual internal-Hom functor and its canonical Koszul biduality.
This supplies the locally free coefficient-duality step, not general Verdier duality
for all constructible complexes or ordinary module reflexivity over a valuation ring.

Source: latest blueprint det-prop-sf-biduality-general.proof.md, locally free case
and perfect integral coefficient paragraph; sk-prop-sf-dualizable-biduality
(blueprint: lem-coef-normalized-reduction-models-core).

Proof: the actual derived coefficient dual preserves dualizable objects by
sk-prop-sf-dualizable-biduality. The same result makes the canonical double-dual
map invertible. Restrict internal Hom into the coefficient unit to this full
subcategory. Naturality of the evaluation transpose gives its square naturally
isomorphic to the identity, so the restricted dual and its right opposite are
quasi-inverse. The full inclusions recover the prescribed ambient functor exactly.
The canonical dual-tensor comparison remains invertible for every ambient target.
The zero object and zero coefficient ring use exactly the same construction. -/
theorem coefficientNormalizedReductionCore
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    let C := DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    letI := DerivedCategory.braidedCategory'
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    let P : ObjectProperty C := IsDualizable
    let D := (derivedHom Λ X).flip.obj (𝟙_ C)
    (∃ e : P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory,
      e.functor ⋙ P.ι = P.ι.op ⋙ D ∧ e.inverse = e.functor.rightOp) ∧
      ∀ K : C, P K → IsIso (MonoidalClosed.toIhomIhomUnit K) ∧
        ∀ M : C, IsIso (MonoidalClosed.ihomUnitTensorToIhom K M) := by
  dsimp only
  let C := DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X))
  let := DerivedCategory.braidedCategory'
    (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  let P : ObjectProperty C := IsDualizable
  let D := (derivedHom Λ X).flip.obj (𝟙_ C)
  have hD (K : C) (hK : P K) : P (D.obj (op K)) :=
    (dualizable_biduality Λ X K hK).1
  have hδ (K : C) (hK : P K) :
      IsIso ((MonoidalClosed.toIhomIhomNatTrans (𝟙_ C)).app K) :=
    (dualizable_biduality Λ X K hK).2.1
  refine ⟨?_, ?_⟩
  · exact ⟨P.liftDualEquivalence D hD
      (MonoidalClosed.toIhomIhomNatTrans (𝟙_ C)) hδ, rfl, rfl⟩
  · intro K hK
    exact (dualizable_biduality Λ X K hK).2

end WeilConjectures
