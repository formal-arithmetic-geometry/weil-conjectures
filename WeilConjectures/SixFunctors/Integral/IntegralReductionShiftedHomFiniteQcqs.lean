/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
import all WeilConjectures.SixFunctors.Compact.CompactSupportTermHomFinite
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Finiteness needed for the constructible integral mapping limit

Source: the constructible mapping-limit argument of
lem-coef-integral-finite-extension, using existing qcqs finite-coefficient Hom finiteness.
(blueprint: lem-sf-integral-reduction-shifted-hom-finite-qcqs).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The shifted Hom groups controlling the Milnor obstruction are finite on every
finite-type space over the algebraic closure of the recorded finite field. A separated
structure morphism is not required.

Source: lem-coef-integral-finite-extension, mapping-limit paragraphs;
CompactSupportTermHomFinite.intrinsic_hom_finite, with no separatedness hypothesis.
(blueprint: lem-sf-integral-reduction-shifted-hom-finite-qcqs).

Proof: shift K inside the constructible integral subcategory. Integral residue Tor gives
finite Tor intervals for both finite reductions. Apply the proved intrinsic_hom_finite
from CompactSupportTermHomFinite, whose statement requires only finite type and
quasicompactness, not separatedness of the structure map. The finite scalar
extension/restriction adjunction identifies its finite Hom set with the displayed one.
The same argument includes empty schemes and zero inputs. -/
theorem integralReduction_shiftedHom_finite_qcqs
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : SixFunctorSpace D)
    (K M : sfIntegralConstructibleCategory l E X.obj.left) (m : ℕ) :
    Finite (K.obj⟦(1 : ℤ)⟧ ⟶
      (sfDerivedReductionRestricted l E X.obj.left m).obj M.obj)  := by
  classical
  let : X.obj.left.Over (Spec (.of D.k)) := ⟨X.obj.hom⟩
  let : LocallyOfFiniteType (X.obj.left ↘ Spec (.of D.k)) := X.property.1
  let : QuasiCompact (X.obj.left ↘ Spec (.of D.k)) := X.property.2
  let : ∀ x : X.obj.left, Invertible (l : X.obj.left.residueField x) := fun x ↦
    (by simpa using ((PurCompactSupport.coefficientPrimeUnit l D hl).map
      (X.obj.hom.residueFieldAlgebraMap x)) :
      IsUnit (l : X.obj.left.residueField x)).invertible
  let K' : sfIntegralConstructibleCategory l E X.obj.left :=
    ⟨K.obj⟦(1 : ℤ)⟧, (sfIntegralConstructible l E X.obj.left).le_shift (1 : ℤ) _ K.property⟩
  obtain ⟨a, b, hab, hK⟩ := K'.property.2
  obtain ⟨c, d, hcd, hM⟩ := M.property.2
  have htK := (integral_residue_tor D l hl E X.obj.left).1
    K'.obj K'.property a b hab (hK 0).2 m
  have htM := (integral_residue_tor D l hl E X.obj.left).1
    M.obj M.property c d hcd (hM 0).2 m
  let : Finite ((scalarReductionDerivedExtension l E X.obj.left m).obj K'.obj ⟶
      (scalarReductionDerivedExtension l E X.obj.left m).obj M.obj) :=
    intrinsic_hom_finite D l hl E (m + 1) (by omega) X.obj.left _ _
      (hK m).1 (hM m).1 a b c d htK htM
  exact Finite.of_equiv _
    ((derivedScalarExtensionRestrictionAdjunction l E X.obj.left m).choose.homEquiv _ _)

end WeilConjectures
