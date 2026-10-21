/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.CompletedIntegralScalarData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.CategoryTheory.AdicBasisLimit
import Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Finite free sections and tensor comparison at the geometric point

Source: Bhatt--Scholze, Lemma 4.2.12 (p. 30), Lemma 6.8.2(1) (pp. 58--59),
and the explicit finite-basis calculation in the DAG; Stacks, Tag 03EK
(blueprint: lem-weil-point-finite-free-sections-tensor).

The data structure spells out all clauses of the assertion. Finite products represent
finite direct sums. Tensor factors are written in the order used by change of rings,
namely scalar tensor section. All coefficient maps and sheafified tensors are the
published constructions. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures

/-- The final object s to s of the small pro-etale site, with the presheaf variance.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeFinal (k : Type t) [Field k] :=
  op (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of k))))

variable (k : Type t) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation at the final object, transported by the displayed constant-value ring
identification. No sectionwise tensor assertion is part of this definition.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeEvaluation
    (e : Padic.coefficientExtensionIntegers l E ≃+*
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj
        (pointFiniteFreeFinal k)) :=
  SheafOfModules.evaluation.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))
      (pointFiniteFreeFinal k) ⋙ ModuleCat.restrictScalars e.toRingHom

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ordinary module scalar extension, using the recorded inclusion of valuation rings.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeModuleTensor :=
  ModuleCat.extendScalars.{u, u, max u (t + 1)} (integralScalarIntegerInclusion l E L ι)

/-- Additivity from the existing extension-restriction adjunction.
Source: Stacks 03EK (blueprint: lem-weil-point-finite-free-sections-tensor). -/
instance pointFiniteFreeModuleTensor_additive :
    (pointFiniteFreeModuleTensor.{t, u} l E L ι).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{max u (t + 1), u, u}
    (integralScalarIntegerInclusion l E L ι)).left_adjoint_additive

/-- Forget commutativity in the actual completed coefficient inclusion.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeRingMap :
    completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)) ⟶
      completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k)) :=
  (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat RingCat)).map
      (completedCoefficientMap l E L ι (Spec (.of k)))

/-- Restriction of scalars along the canonical completed coefficient inclusion.
Source: DAG statement (blueprint: lem-weil-point-finite-free-sections-tensor). -/
abbrev pointFiniteFreeRestriction :=
  SheafOfModules.restrictScalars.{max u (t + 1)} (pointFiniteFreeRingMap k l E L ι)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The complete assertion: normalized coefficient identifications, a common global
basis, local tensor coordinates, the unique linear natural comparison, exactness,
and its unbounded termwise complex comparison. Each field is a clause of the node.
The inverse formulas fix every coordinate isomorphism, rather than postulating an
unrelated abstract isomorphism. The choice of basis is confined to these coordinates.
Source: Bhatt--Scholze 4.2.12 and 6.8.2(1), Stacks 03EK; DAG statement
(blueprint: lem-weil-point-finite-free-sections-tensor). -/
structure PointFiniteFreeSectionsTensorData where
  coefficientE : Padic.coefficientExtensionIntegers l E ≃+*
    (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj
      (pointFiniteFreeFinal k)
  coefficientL : Padic.coefficientExtensionIntegers l L ≃+*
    (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k))).obj.obj
      (pointFiniteFreeFinal k)
  constantE : ∀ a, coefficientE a =
    integralScalarConstant l E (Spec (.of k)) (pointFiniteFreeFinal k) a
  constantL : ∀ a, coefficientL a =
    integralScalarConstant l L (Spec (.of k)) (pointFiniteFreeFinal k) a
  quotientE : ∀ n a,
    (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n).hom.app
      (pointFiniteFreeFinal k) (coefficientE a) =
        integralScalarFiniteConstant l E (Spec (.of k)) n (pointFiniteFreeFinal k) a
  quotientL : ∀ n a,
    (completedIntegralCommRingProjectionUnrestricted l L (Spec (.of k)) n).hom.app
      (pointFiniteFreeFinal k) (coefficientL a) =
        integralScalarFiniteConstant l L (Spec (.of k)) n (pointFiniteFreeFinal k) a
  coefficient_compatibility : ∀ a,
    (completedCoefficientMap l E L ι (Spec (.of k))).hom.app (pointFiniteFreeFinal k)
      (coefficientE a) = coefficientL (integralScalarIntegerInclusion l E L ι a)
  basis : Fin (completedScalarRelativeDegree l E L ι) → Padic.coefficientExtensionIntegers l L
  integral_basis : Function.Bijective
    (fun a : Fin (completedScalarRelativeDegree l E L ι) →
        Padic.coefficientExtensionIntegers l E ↦
      ∑ i, integralScalarIntegerInclusion l E L ι (a i) * basis i)
  sheafBasis :
    (pointFiniteFreeRestriction k l E L ι).obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l L (Spec (.of k)))) ≅
      ∏ᶜ (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
        SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))))
  sheafBasis_inverse : ∀ U x,
    sheafBasis.inv.val.app U x = ∑ i,
      (pointFiniteFreeRingMap k l E L ι).hom.app U
        ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
          SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))) i).val.app U x) *
        integralScalarConstant l L (Spec (.of k)) U (basis i)
  coordinates : ∀ F : integralTowerModules l E (Spec (.of k)),
    (pointFiniteFreeRestriction k l E L ι).obj
        ((completedOrdinaryScalarExtension l E L ι (Spec (.of k))).obj F) ≅
      ∏ᶜ (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F)
  coordinates_tensor : ∀ (F : integralTowerModules l E (Spec (.of k))) U a n i,
    (Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app U
      ((coordinates F).hom.val.app U
        (completedScalarTensorSection l E L ι (Spec (.of k)) F U a n)) =
      ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦
        SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k)))) i).val.app U
            (sheafBasis.hom.val.app U a)) • n
  coordinates_inverse : ∀ (F : integralTowerModules l E (Spec (.of k))) U x,
    (coordinates F).inv.val.app U x = ∑ i,
      completedScalarTensorSection l E L ι (Spec (.of k)) F U
        (integralScalarConstant l L (Spec (.of k)) U (basis i))
        ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app U x)
  comparison :
    pointFiniteFreeEvaluation k l E coefficientE ⋙ pointFiniteFreeModuleTensor.{t, u} l E L ι ≅
      completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
        pointFiniteFreeEvaluation k l L coefficientL
  comparison_tensor : ∀ (F : integralTowerModules l E (Spec (.of k))) a n,
    comparison.hom.app F
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E, integralScalarIntegerInclusion l E L ι] n) =
      completedScalarTensorSection l E L ι (Spec (.of k)) F (pointFiniteFreeFinal k)
        (coefficientL a) n
  comparison_coordinates : ∀ (F : integralTowerModules l E (Spec (.of k)))
    (n : Fin (completedScalarRelativeDegree l E L ι) →
      (pointFiniteFreeEvaluation k l E coefficientE).obj F) i,
    (Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app
        (pointFiniteFreeFinal k)
      ((coordinates F).hom.val.app (pointFiniteFreeFinal k)
        (comparison.hom.app F (∑ j,
          basis j ⊗ₜ[Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion l E L ι] n j))) = n i
  comparison_inverse : ∀ (F : integralTowerModules l E (Spec (.of k))) x,
    comparison.inv.app F x = ∑ i,
      basis i ⊗ₜ[Padic.coefficientExtensionIntegers l E,
        integralScalarIntegerInclusion l E L ι]
        (@id ((pointFiniteFreeEvaluation k l E coefficientE).obj F)
          ((Pi.π (fun _ : Fin (completedScalarRelativeDegree l E L ι) ↦ F) i).val.app
            (pointFiniteFreeFinal k)
              ((coordinates F).hom.val.app (pointFiniteFreeFinal k) x)))
  comparison_unique : ∀ (F : integralTowerModules l E (Spec (.of k)))
    (f : ((pointFiniteFreeEvaluation k l E coefficientE ⋙
      pointFiniteFreeModuleTensor.{t, u} l E L ι).obj F) ⟶
      ((completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
        pointFiniteFreeEvaluation k l L coefficientL).obj F)),
    (∀ a n, f (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
      integralScalarIntegerInclusion l E L ι] n) =
        completedScalarTensorSection l E L ι (Spec (.of k)) F (pointFiniteFreeFinal k)
          (coefficientL a) n) → f = comparison.hom.app F
  sheaf_additive : (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).Additive
  sheaf_limits : PreservesFiniteLimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
  sheaf_colimits : PreservesFiniteColimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))
  module_additive : (pointFiniteFreeModuleTensor.{t, u} l E L ι).Additive
  module_limits : PreservesFiniteLimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)
  module_colimits : PreservesFiniteColimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)
  restriction_detects_exactness : ∀ S : ShortComplex (integralTowerModules l L (Spec (.of k))),
    S.Exact ↔ (S.map (pointFiniteFreeRestriction k l E L ι)).Exact
  complexes :
    (pointFiniteFreeEvaluation k l E coefficientE ⋙
      pointFiniteFreeModuleTensor.{t, u} l E L ι).mapHomologicalComplex (ComplexShape.up ℤ) ≅
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙
      pointFiniteFreeEvaluation k l L coefficientL).mapHomologicalComplex (ComplexShape.up ℤ)
  complexes_hom : ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) j,
    (complexes.hom.app K).f j = comparison.hom.app (K.X j)
  complexes_inv : ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) j,
    (complexes.inv.app K).f j = comparison.inv.app (K.X j)

/-- The finite-free comparison, including every coordinate and chain-level clause.
Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2(1); Stacks Tag 03EK
(blueprint: lem-weil-point-finite-free-sections-tensor).

Proof:
1. By lem-pur-proetale-finite-constant-sections, constants identify sections of each
finite quotient at s with that quotient. By def-pur-sheaf-inverse-limit the completion's
sections are their inverse limit. Compatible integral lifts form a Cauchy sequence by
the uniformizer-power bounds. lem-weil-l-adic-extension-complete supplies its limit;
lem-weil-l-adic-extension-integers-dvr identifies the balls with the quotient ideals.
The resulting integral scalar is unique, yielding the normalized ring equivalences
and their quotient equations.
2. Choose an integral basis by lem-sfb-local-field-integral-basis. Uniqueness of
extending absolute values (lem-weil-l-adic-extension-absolute-value) makes the two
integer actions agree. DVR factorization gives uniformizer_E = unit * uniformizer_L^e
with e positive. lem-pur-adic-basis-limit supplies the sheaf basis with these columns,
and its residue normalization proves compatibility with the coefficient inclusion.
3. On U send a tensor n tensor a to the tuple q_i(a)n, and a tuple to the sum of
n_i tensor b_i. The basis identities make these inverse and restriction-compatible.
The tuple presheaf is a sheaf. def-weil-presheaf-modules-sheafification therefore
identifies its sheafification with itself, giving the displayed sheaf coordinates.
4. The balanced pure-tensor formula gives an O_L-linear comparison. The same basis
calculation for ordinary modules identifies both sides with tuples of sections,
with identity comparison and the stated inverse. Pure tensors generate the module
tensor, proving uniqueness and independence of the basis. The formula commutes with
every sheaf map, giving naturality.
5. Tensor functors add maps. Their restrictions to the original coefficient ring are
finite powers. Kernels and cokernels are coordinatewise for finite powers; forgetting
the extended ring action detects exactness, since kernels and sheafified cokernels
retain their underlying abelian sheaves (def-weil-sheaf-of-modules-category).
This proves both exactness assertions.
6. Apply the natural comparison to every differential of any cochain complex.
Naturality is exactly the chain-map identity. The inverses also commute with the
differentials. This gives the asserted natural complex isomorphism without bounds.
-/
theorem point_finite_free_sections_tensor
    (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E L : IntermediateField ℚ_[l] Ω)
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (h : E ≤ L) :
    Nonempty (PointFiniteFreeSectionsTensorData D.k l E L (IntermediateField.inclusion h)) := by
  sorry

end WeilConjectures
