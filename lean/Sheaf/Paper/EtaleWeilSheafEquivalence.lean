/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.EtaleWeilRepresentationData
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
import Sheaf.Paper.EtaleWeilReconstruction
import Sheaf.Paper.EtaleWeilAbelian
import Sheaf.Paper.EtaleWeilTensor
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Preadditive.Transfer

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
  let R := etaleWeilRealization l Q h t d D
  let ff : R.FullyFaithful := etaleWeilRealization_fullyFaithful l Q h t d D
  let : R.Full := ff.full
  let : R.Faithful := ff.faithful
  let : R.EssSurj := ⟨etaleWeilReconstruction l Q h t d D⟩
  let : R.IsEquivalence := {}
  let e := R.asEquivalence
  obtain ⟨aW⟩ := etaleWeilAbelian l Q h t
  let : Abelian (EtaleLisseWeilSheaf l Q h) := aW
  let : Preadditive (etaleLisseWeilRepresentations l Q h t d D) :=
    Preadditive.ofFullyFaithful e.fullyFaithfulInverse
  let : HasFiniteLimits (etaleLisseWeilRepresentations l Q h t d D) :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  let aR : Abelian (etaleLisseWeilRepresentations l Q h t d D) :=
    abelianOfEquivalence e.inverse
  refine ⟨e, ⟨fun F ↦ LinearEquiv.refl Q _, ?_, ?_⟩, ⟨aW⟩, ⟨aR⟩,
    inferInstance, inferInstance, inferInstance, inferInstance,
    etaleWeilTensor l Q h t d D e rfl⟩
  · intro F g x
    rfl
  · intro F H a x
    exact LinearMap.congr_fun (etaleWeilRealization_map l Q h t d D a) x

end AlgebraicGeometry.Scheme
