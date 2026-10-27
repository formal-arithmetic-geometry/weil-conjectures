/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorTransportInternalData
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Sheaf.Paper.IntegralResidueDerivedMonoidal

/-! # Ordinary-side scalar tensor evaluation -/

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

/-- Evaluate the ordinary scalar-total side on all internal complexes.
Source: Stacks Project, sites-modules.tex, Tag 03EL, extension of scalars and pure
sections; sites-cohomology.tex, Tags 06YY and 07A4, signed total constituents.
(blueprint: lem-sfb-quotient-section-tensor-transport-internal-right).

Proof: hc.1 identifies c.ordinary on the images of scalar-unit generators.
The formula he then says that e is the transport of the internal scalar
tensorator, after the ordinary section tensor comparisons. Scalar-linearity
extends the equality to general scalar generators, tensor balancing extends it
to ordinary tensor sections, and the universal property of sheafification
extends it to sheaf morphisms. Totalize this ordinary square. Check each
bidegree inclusion: mapBifunctorComparison has the specified component map,
and the same Koszul sign occurs on both routes, so coproduct extensionality
gives the complex square. Substitute TensorRepresentativeNormalization for the
input qTensor and hc.2 on P tensor Q. Naturality of the model counit moves the
section total comparison across it. The ordinary complex square then replaces
the transported e total by totalScalar followed by the output total section
comparison and the two c.ordinary comparisons. Naturality of the section
localization factor yields scalarTensorSectionPath. This uses no K-flat or
flat-term assumption, and does not involve b or barB. For zero complexes the
same inclusion check is vacuous, and nonflat scalar maps remain allowed. -/
theorem section_tensor_transport_internal_right (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    [PreservesColimitsOfSize.{0, 0} c.model.E]
    (e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
        (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
          (curriedTensor (modules Λ' T)))
    (he : ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
      (n : N.val.obj W) (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
          (sectionScalarElement a T c (M ⊗ N) W
            (sectionPureTensor Λ T M N W m n) s) =
        sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
          (sectionScalarElement a T c M W m 1)
          (sectionScalarElement a T c N W n s)) :
    ∀ P Q : CochainComplex (Modules Λ T) ℤ,
      let EP := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P
      let EQ := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q
      scalarTensorSectionInput a T c P Q ≫
        c.model.T.map ((qTensor Λ T).app (EP, EQ)) ≫
          c.model.ε.app ((totalTensor Λ T).obj (EP, EQ)) ≫
          DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorComparison e (.up ℤ) EP EQ) =
        scalarTensorSectionPath a T c P Q := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
