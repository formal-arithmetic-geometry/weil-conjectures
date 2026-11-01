/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData
public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SmoothPurity.Supporting.Coefficient.RegularCoefficientCoherentReduction
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.Compactification.CommonRefinement
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The specified structural exceptional dualizing object

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, paragraph 1,
and thm-coef-qbar-verdier, identification of the dualizing object.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard AlgebraicGeometry.Scheme.residueField
universe u
open CategoryTheory AlgebraicGeometry Opposite
open WeilConjectures.AdicQbarRealization WeilConjectures.NativeExceptionalForgetful

namespace WeilConjectures.NativeBidualRealization

/-- The dualizing object of descended Verdier duality agrees with the exceptional
image of the actual point unit for any specified normalized structural system.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, paragraph 1;
thm-coef-qbar-verdier, dualizing-object clause and coefficient transports.
(blueprint: lem-sf-structural-dualizing-identification).

Proof: represent B.omega over the least finite coefficient field using
B.omegaComparison. The rational dualizing identification identifies this finite
object with exceptional pullback of the completed regular module, localized.
Compare the exceptional adjunction with the specified system S: its normalized
compact-support functor agrees with the same proper/open construction, and
uniqueness of right adjoints supplies the comparison on the right. A common
compactification refinement compares the canonical compactification with c.
The common-stage coefficient comparison transports this isomorphism to closed
coefficients. The completed regular module and the reduction-limit tensor unit
are identified by their normalized reduction adjunction; after localization and
inclusion this identifies the input with geometricPointOmega. Compose these
isomorphisms with B.omegaComparison. All comparisons concern actual objects and
have inverses; zero objects and the empty scheme satisfy the same construction.
No biduality map, internal-Hom equivalence, or native adjunction is assumed. -/
theorem structural_dualizing_identification
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (R : Family l D) (X : Space D)
    (B : CoefQbarVerdier.Duality D l (Fact.out : l ≠ D.p) (PadicAlgCl l)
      (geometric D X).base.left)
    (hB : CoefQbarVerdier.Dualizing D l (Fact.out : l ≠ D.p) (PadicAlgCl l)
      (geometric D X).base.left B)
    (S : StructuralSystem D l X)
    (c : Compactification (geometric D X).base.hom) :
    Nonempty (B.omega ≅ (S.ring.operation c .closed).G.obj (geometricPointOmega D l R)) := by
  classical
  let Y := (geometric D X).base.left
  let E := Padic.finiteCoefficientBase l (PadicAlgCl l)
  let F := CoefQbarVerdier.fieldStage l (PadicAlgCl l) E
  let c₀ := integralDualizingCompactification D Y
  obtain ⟨A, _, hA⟩ := hB
  obtain ⟨e⟩ := hA E
  let t : (A.system.ring.operation c₀ (.rational F)).F ≅
      (S.ring.operation c₀ (.rational F)).F :=
    A.system.ring.rationalLeft c₀ F ≪≫ (S.ring.rationalLeft c₀ F).symm
  let r := ((A.system.ring.operation c₀ (.rational F)).adjunction.ofNatIsoLeft t).rightAdjointUniq
    (S.ring.operation c₀ (.rational F)).adjunction
  obtain ⟨d, ⟨rd⟩, ⟨rc⟩⟩ := Compactification.exists_common_refinement c₀ c
  let z : (S.ring.operation c₀ .closed).G ≅ (S.ring.operation c .closed).G :=
    (S.refinements.refinement rd .closed).right ≪≫
      (S.refinements.refinement rc .closed).right.symm
  have unit : Nonempty
      (CoefQbarVerdier.coefficientUnit D l (Fact.out : l ≠ D.p) (PadicAlgCl l)
        (Spec (CommRingCat.of D.k)) ≅ geometricPointOmega D l R) := by
    let P := Spec (CommRingCat.of D.k)
    let := (R.data (geometricPoint D)).units
    let K := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let Q := integralSystemReduction l K P
    let := (integralSystemReduction_fullyFaithful l K P).1
    let := (integralSystemReduction_fullyFaithful l K P).2
    obtain ⟨a⟩ := regularCoefficient_coherentReduction l K P
    let aa : Q.obj
        ⟨integralConstantCoefficientObject l K P,
          (integralConstantCoefficient_constructible l K P D (Fact.out : l ≠ D.p)).2.1⟩ ≅
        Q.obj (pullbackTensorIntegralUnit l K P) :=
      a ≪≫ (pullbackTensorIntegralUnitReduction l K P).symm
    let b := Q.preimageIso aa
    let b' := (sfRationalConstructibleLocalization l K P).mapIso b
    exact ⟨(GeneralAlgebraicallyClosedCoefficients.inclusion E).mapIso b'⟩
  obtain ⟨w⟩ := unit
  exact ⟨(B.omegaComparison E).symm ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion E).mapIso e ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion E).mapIso
      (r.app (RationalOperations.coefficientUnit l F.carrier
        (Spec (CommRingCat.of D.k)) D (Fact.out : l ≠ D.p))) ≪≫
    (S.common.commonComparison c₀ E).b.app _ ≪≫
    (z.app _) ≪≫ (S.ring.operation c .closed).G.mapIso w⟩

end WeilConjectures.NativeBidualRealization
