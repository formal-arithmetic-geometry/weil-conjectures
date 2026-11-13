/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import WeilConjectures.AlgebraicGeometry.ConstructibleLocalTorEtaleOrigin
import WeilConjectures.AlgebraicGeometry.FixedScalarEtaleOrigin
import WeilConjectures.AlgebraicGeometry.IntegralResidueCoefficientTransport

/-! # Residue origin under the canonical integral realization

## References

* Stacks, Tags 09C1, 09C2 and 09AL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- Constructible finite-Tor residue complexes are precisely the bounded constructible
etale residue complexes in the fixed completed coefficient presentation. The given
completeness witness only supplies the first conjunct of the adic predicate. -/
theorem residue_transport (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X)))
    (hcomplete : Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K)) :
    residueCondition l E X ((restriction l E X).obj K) ↔
    Scheme.IsSfbAdicConstructible X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K) := by
  let A := IntegralConstantCompletion.integers l E
  let I := IntegralConstantCompletion.ideal l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal :=
    h.2.2.2.2.1
  have hI : I.IsMaximal := by
    have hm := hmax.map_bijective
      (ULift.ringEquiv.symm : Padic.coefficientExtensionIntegers l E ≃+* A)
      ULift.ringEquiv.symm.bijective
    rw [← hgen, Ideal.map_span, Set.image_singleton] at hm
    exact hm
  let k := A ⧸ I ^ (0 + 1)
  have hIp : (I ^ (0 + 1)).IsMaximal := by simpa using hI
  let := hIp
  let : Field k := Ideal.Quotient.field _
  let T := Scheme.sfbResidueComplex X I
    ((IntegralConstantModel.derived l E X).functor.obj K)
  let M := Scheme.fixedScalarDerivedModel X k T
  have hcoeff := integral_residue_coefficient_transport l E X
    (inferInstance : IsNoetherianRing k) K
  have horigin := constructible_localTor_iff_etaleOrigin.{u, u} X k M
  have hlocal := Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally.{u, u} X k M
  have hfixed := Scheme.fixedScalar_etaleOrigin X k T
  change residueCondition l E X ((restriction l E X).obj K) ↔
    Scheme.IsSfbAdicComplete X I ((IntegralConstantModel.derived l E X).functor.obj K) ∧ _
  constructor
  · intro hK
    obtain ⟨hc, ht⟩ := hcoeff.mp hK
    exact ⟨hcomplete, hfixed.mp (horigin.mp ⟨hc, hlocal.mp ht⟩)⟩
  · rintro ⟨_, hK⟩
    obtain ⟨hc, ht⟩ := horigin.mpr (hfixed.mpr hK)
    exact hcoeff.mpr ⟨hc, hlocal.mpr ht⟩

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
