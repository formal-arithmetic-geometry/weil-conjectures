/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import Sheaf.Paper.GaloisLisseRepresentations
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
public import Sheaf.Paper.LisseAdicFiberFunctors
public import Sheaf.Paper.LisseModuleSheaves
public import Sheaf.Paper.LisseTensorScalarExtension
public import Sheaf.RepresentationTheory.LAdic
public import Mathlib.RepresentationTheory.Rep.Basic
import WeilConjectures.RepresentationTheory.FiniteDimensionalRealization
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
import WeilConjectures.WeilSheaf.Tensor

/-!
# The exact tensor equivalence for actual etale adic Weil sheaves

Source: Weil II (1.1.1), (1.1.6), (1.1.10); blueprint main-20261015,
prop-wf-weil-sheaf-representation-equivalence
(blueprint: prop-wf-weil-sheaf-representation-equivalence).

The source is the actual etale adic coefficient-pair category with descent, and the
realization is its geometric etale fibre with the normalized fundamental representation.
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

/-- The stalk realization is an exact tensor equivalence, including its actual
fundamental action. The supplied abelian structures and finite-limit and finite-colimit preservation
express exactness;
the inverse gives the correspondence of subobjects, quotients and subquotients.
Source: blueprint prop-wf-weil-sheaf-representation-equivalence
(blueprint: prop-wf-weil-sheaf-representation-equivalence).
Proof: cor-galois-lisse-representations identifies underlying etale lisse sheaves
with continuous geometric representations. Its finite evaluation action is the germ
rule used in etaleFinitePathIso. Apply inverse limits, rationalization and the
coefficient localization for the same identity at adic coefficients. A Weil descent
isomorphism gives the specified degree-one operator, and the finite path conjugation
identity is precisely its extension relation. Conversely that relation reconstructs
descent by full faithfulness of the underlying etale dictionary. Morphisms are exactly
intertwiners for the geometric group and the degree-one operator, hence for the whole
Weil group. This proves full faithfulness and essential surjectivity. Finite limits
and colimits are preserved by an equivalence, giving exactness and both directions
of the subquotient correspondence. The recorded tensor and unit on the etale side
are sent to the diagonal tensor and trivial representation: check on finite stalks,
then limits and the two coefficient extensions. Naturality of these prescribed
maps gives the monoidal constraints and their associativity and unit identities. -/
theorem etaleWeilSheafRepresentationEquivalence [ConnectedSpace Y] :
    ∃ e : EtaleLisseWeilSheaf l Q h ≌ etaleLisseWeilRepresentations l Q h t d D,
      (∃ f : ∀ F : EtaleLisseWeilSheaf l Q h,
          (e.functor.obj F).obj.V ≃ₗ[Q] lisseAlgebraicFiber l Y Q t F.carrier,
        (∀ (F : EtaleLisseWeilSheaf l Q h) (g : G) (x : (e.functor.obj F).obj.V),
          f F ((e.functor.obj F).obj.ρ g x) =
            etaleFundamentalRep l Q h t d D F g (f F x)) ∧
        ∀ (F H : EtaleLisseWeilSheaf l Q h) (a : F ⟶ H) (x : (e.functor.obj F).obj.V),
          f H ((e.functor.map a).hom.hom x) =
            etaleAlgebraicFiberMap l Q t
              ((Endofunctor.IsoAlgebra.forget
                (lisseAlgebraicAutomorphismPullback h l Q)).map a) (f F x)) ∧
      Nonempty (Abelian (EtaleLisseWeilSheaf l Q h)) ∧
      Nonempty (Abelian (etaleLisseWeilRepresentations l Q h t d D)) ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse ∧
      etaleWeilTensorCompatibility l Q h t d D e := by
  sorry

end AlgebraicGeometry.Scheme
