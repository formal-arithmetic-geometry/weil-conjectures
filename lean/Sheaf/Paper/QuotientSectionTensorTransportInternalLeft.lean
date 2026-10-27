/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorTransportInternalData
import Sheaf.Paper.IntegralResidueDerivedMonoidal

/-! # Derived-side scalar tensor evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- Evaluate the derived tensor side on internal resolving complexes.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A4,
lemma-pullback-tensor-product and the K-flat tensor localization construction.
(blueprint: lem-sfb-quotient-section-tensor-transport-internal-left).

Proof: transfer the independent K-flat test and flat terms through the exact
section equivalence to P and Q. Precompose the tensor-section conjugation square
hbarB by the section localization isomorphisms. Naturality of barB moves these
isomorphisms into its output. Replace each scalar localization counit using hc.2.
Normalize the output qTensor on the two extended internal complexes by its
TensorRepresentativeNormalization equation; naturality moves the ordinary
scalar section comparisons to the final total map. All section tensor and
scalar comparison isomorphisms cancel in pairs. What remains is the section
image of b followed by the two internal scalar counits and the internal tensor
localization. TensorNormalized hb replaces precisely this internal path by
D.map of the internal tensor localization, compute on P tensor Q, and the
localization of totalScalar. These are the first three factors of
scalarTensorSectionPath; the remaining factors are the localized total section
comparison and the two ordinary scalar comparisons. This proves the displayed
evaluation. No assertion about the section ordinary tensor map e occurs here.
The zero pair gives zero maps on both sides; no coefficient flatness is used. -/
theorem section_tensor_transport_internal_left (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (hbarB : TensorSectionCondition a T c b barB) :
    ∀ P Q : CochainComplex (Modules Λ T) ℤ,
      let EP := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P
      let EQ := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) EP →
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) EQ →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (EP.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (EQ.X i)) →
      scalarTensorSectionInput a T c P Q ≫
        barB.hom.app (DerivedCategory.Q.obj EP, DerivedCategory.Q.obj EQ) ≫
          (tensor Λ' T).map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ)) ≫
          (qTensor Λ' T).app
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj EP,
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj EQ) =
        scalarTensorSectionPath a T c P Q := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
