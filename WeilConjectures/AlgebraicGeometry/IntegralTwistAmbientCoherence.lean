/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTwistDerivedScalarCanonical
public import WeilConjectures.AlgebraicGeometry.CompletedLineTensorCoherence

/-! # Ambient tower and unit laws for the published twist comparison

Source: blueprint `prop-weil-twist-preserves`, final integral/common-stage sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (S : Scheme.{u}) [∀ x : S, Invertible (l : S.residueField x)]
  (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
  (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
  (ι : E →ₐ[Padic l] F) (κ : F →ₐ[Padic l] G)

/-- The published completed beta obeys the ambient tower and multiplication-unit
laws, before restriction to the named integral scalar associator and unitor.
Source: blueprint `prop-weil-twist-preserves`, final common-stage sentence;
Steps 2--4 of the current proof of `lem-weil-integral-twist-scalar-coherence`.
(blueprint: lem-weil-integral-twist-ambient-coherence).

Proof: put L_H = purTwistIntegralModule S l H. These are locally free lines by
pur_twist_sheaf_locally_free. The normalized line extension is twistLineScalarIso
at exponent one. Its tower equation follows from integral_twist_base_change:
on a local tensor the two maps give c*kappa(b)*theta_GE(y), by semilinearity
and twistScalarMaps_composition. Its identity is multiplication, by
 twistScalarMaps_identity. For every signed exponent, the powers of these
line maps are exactly the published twistLineScalarIso: positive powers have
the same recursive tensor formula; for negative powers the common evaluation
formula determines the dual map. Apply the ordinary signed-line comparison
and its tower and identity clauses. Their sheaf maps agree with the maps
specifying integralTwistOrdinaryBeta, by the local tensor formula. The
universal K-flat counit equations and essential surjectivity of good-complex
localization give equality on every integral object. The published
integralTwistCompletedBeta is fixed by conjugation with the specified chi,
so it equals CompletedLineTensor.beta for these lines and signed maps.
Consequently CompletedLineTensor.tower gives the first equation. For the
second, substitute the multiplication identity in the ordinary line unit
square, then conjugate by chi. Naturality moves the middle chi past the
ordinary beta, adjacent inverse pairs cancel, and the resulting map is
CompletedLineTensor.unit at the twisted object. All comparisons are inverted
only on complete objects: C and its twist are integral, and scalar extension
preserves completeness. The proof retains multiplication units when fields
repeat; it does not identify completed identity extension with the identity
functor by definitional equality. Zero or negative m, empty S and the zero
object satisfy the same formulas. -/
theorem integral_twist_ambient_coherence (m : ℤ)
    (C : sfIntegralConstructibleCategory l E S)
    (hC : sfIntegralConstructible l E S
      ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj)) :
    ((integralScalarExtensionOfUniverses l F G κ S).map
        ((integralTwistCompletedBeta l E F ι S m).hom.app C) ≫
      (integralTwistCompletedBeta l F G κ S m).hom.app
        ((sfConstructibleIntegralScalarExtension (l + 1) l (ne_of_lt (Nat.lt_succ_self l))
          E F ι S).obj C) ≫
      (integralSheafTwist l G S m).mapDerivedCategory.map
        (CompletedLineTensor.associator l E S F ι G κ C.obj
          (CompletedLineTensor.intrinsic_complete l E S C)).hom =
    (CompletedLineTensor.associator l E S F ι G κ
      ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj)
      (CompletedLineTensor.intrinsic_complete l E S
        ⟨(integralSheafTwist l E S m).mapDerivedCategory.obj C.obj, hC⟩)).hom ≫
      (integralTwistCompletedBeta l E G (κ.comp ι) S m).hom.app C) ∧
    ((integralTwistCompletedBeta l E E (AlgHom.id (Padic l) E) S m).hom.app C ≫
      (integralSheafTwist l E S m).mapDerivedCategory.map
        (CompletedLineTensor.unit l E S C.obj
          (CompletedLineTensor.intrinsic_complete l E S C)).hom =
    (CompletedLineTensor.unit l E S
      ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj)
      (CompletedLineTensor.intrinsic_complete l E S
        ⟨(integralSheafTwist l E S m).mapDerivedCategory.obj C.obj, hC⟩)).hom) := by sorry

end WeilConjectures
