/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefProjectionEvaluationData
import WeilConjectures.SixFunctors.CoefProjectionTensorModelsExistence
import WeilConjectures.SixFunctors.CoefProjectionAdjunctionModelsExistence
import WeilConjectures.SixFunctors.CoefProjectionSectionsModelsExistence
import WeilConjectures.SixFunctors.CoefProjectionReductionModelsExistence

/-! # Projection and evaluation on coefficient systems

The system projection word is specialized using the normalized scalar Hom theorem.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2.
(blueprint: lem-coef-system-projection-evaluation).
-/

@[expose] public noncomputable section
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u a b v w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Projection-evaluation on the whole ringed coefficient system, and its scalar
specialization for every ambient completed-coefficient K and arbitrary quotient N.
All tensor, adjunction, representative and composition witnesses are conclusions.
The maps are Model.v, Model.Pi, Model.q, Model.balance, Model.beta and
ScalarSpecialization.transported, with exactly their displayed composite definitions.
No finite-Tor, boundedness, constructibility, or projection-isomorphism hypothesis occurs.

Source: blueprint latest, prop-coef-integral-dualizing.proof.md paragraph 2;
Stacks 07A4, 07A6, 08J9, 0D6D, 0B56
(blueprint: lem-coef-system-projection-evaluation).

Proof: derive the ordinary module adjunctions for quotient-system point sections,
proper direct image and scalar restriction simultaneously on the sequence sites.
Exact scalar restriction has its mapDerivedCategory comparison; the other direct
images have their universal right-derived units. The adjunction transpose of the
ordinary unit tensored with itself, followed by the local pure-tensor map, is the
strong pullback comparison. Signed totalization and the left-derived universal
property give TensorAdjunction.representative and its localized comparison.
Compute the ordinary sections/direct-image comparison at (n,X): it is restriction
along the inverse terminal-object pullback isomorphism. Its derived unit equation
fixes SectionsComposition, and conjugation gives sectionsPullback. Resolve both
system tensor factors K-flatly and the Hom target K-injectively. The recorded
Hom model makes evaluation actual sheafified evaluation, and its graded symmetry
contributes (-1)^(rs). The recorded normalized open model supplies gamma, including
the quotient transitions. Compose the proper mate, gamma and pullback composition
to obtain Pi; compose the point-sections mate and evaluation to obtain q. Exact
restriction applied to the scalar counit gives balance, and the signed symmetry
gives beta. All arrows already live on the localized derived sequence category;
changing a representative conjugates adjacent maps by inverse comparison pairs,
which cancel. None of this inverts a projection mate. Finally apply the normalized
scalar internal-Hom comparison of coefHomTowerScalarModel. Derived scalar extension
of const K has the strict reduction model P tensor A_(n+1), with id tensor quotient
transitions and finite scalar-extension comparisons. Tensor its Hom comparison
with the identity of the native compact-support point tower and compose with beta;
this is exactly ScalarSpecialization.transported, for arbitrary K and N. -/
theorem projectionEvaluation
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (_hl : IsUnit (l : k)) (c : Compactification a) :
    ∃ m : Model l E c, Nonempty (ScalarSpecialization l E m) := by
  obtain ⟨point, pointSymmetry, x, y, z, ⟨openTensor⟩⟩ :=
    coefficientProjectionTensorModels_exists l E X Y c.Z c.i
  obtain ⟨xLax, yLax, pLax, rLax, gx, gy, p, r,
    ⟨gxTensor⟩, ⟨gyTensor⟩, ⟨pTensor⟩, ⟨rTensor⟩⟩ :=
    coefficientProjectionAdjunctionModels_exists l E X Y c.Z c.g point x y z
  obtain ⟨⟨composition⟩, ⟨sections⟩⟩ := coefficientProjectionSectionsModels_exists l E a
  let m : Model l E c := {
    point, pointSymmetry, x, y, z, xLax, yLax, pLax, rLax, gx, gy, p, r,
    gxTensor, gyTensor, pTensor, rTensor, composition, openTensor }
  let : ∀ R : Sheaf (coefficientSequenceTopology (ProEt.topology X))
      CommRingCat.{u + 1}, HasDerivedCategory.{u + 2}
        (scalarModules (coefficientSequenceTopology (ProEt.topology X)) R) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 2} (scalarModules (ProEt.topology X) R) :=
    fun _ ↦ HasDerivedCategory.standard _
  obtain ⟨S, μ, ⟨A⟩⟩ := scalarInternalHomAdjunction_exists.{u + 1, u, u, u + 2}
    (J := coefficientSequenceTopology (ProEt.topology X))
  obtain ⟨F, ν, ⟨B⟩⟩ := scalarInternalHomAdjunction_exists.{u + 1, u, u, u + 2}
    (J := ProEt.topology X)
  obtain ⟨α, hα, _⟩ := coefHomTowerScalarModel.{u, u} l E X S μ A F ν B
  obtain ⟨ρ, hρ⟩ := coefficientProjectionReductionModels_exists l E X S
  exact ⟨m, ⟨{
    supportSections := sections
    scalar := S
    tensor := μ
    homAdjunction := A
    comparison := α
    normalization := hα
    reductionEvaluation := ρ
    reductionModel := hρ }⟩⟩

end WeilConjectures.CoefProjectionEvaluation
