/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.FiniteCoefficientSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.Semilinear.DerivedSystemMappingHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Actual coherent global Hom systems for continuous integral reductions

Source: Zheng, Construction 4.1; Stacks 0B6E.
(blueprint: def-sfb-coherent-integral-mapping-systems)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.CoherentReduction
attribute [local instance] proEtSmall sequenceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The scalar value is the genuine integral constant section followed by quotient reduction.
Source: blueprint coherent Hom system, step 5
(blueprint: def-sfb-coherent-integral-mapping-systems). -/
def scalarValue (X : Scheme.{u}) (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) : (coefficients l E X n).obj.obj U :=
  (coefficientMap l E X n).hom.app U
    ((constantSections X (Padic.coefficientExtensionIntegers l E)).hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (Padic.coefficientExtensionIntegers l E)))).app U a))

/-- The actual scalar algebra on the coefficient sequence is fixed by all its section values.
Source: Zheng 4.1 and Stacks 0B6E
(blueprint: def-sfb-coherent-integral-mapping-systems).

Proof: send a in O at (n,U) to its constant continuous section and then its
class modulo ell^(n+1). Naturality in U follows from the sheafification unit
and the ring-sheaf maps. Naturality in n is coefficientMap_compatible, iterated
along the actual adjacent quotient maps. Pointwise ring operations preserve
zero, one, addition and multiplication, so these compatible sections form a
ring homomorphism. Equality at every (n,U) is equality of global sections,
which proves uniqueness. The construction includes the empty scheme.
-/
theorem scalarAlgebra_existsUnique (X : Scheme.{u}) :
    ∃! α : SystemAlgebra.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X) (Padic.coefficientExtensionIntegers l E),
      ∀ (a : Padic.coefficientExtensionIntegers l E) (U : (ℕ × X.ProEt)ᵒᵖ),
        (α a).val U = scalarValue l E X U.unop.1 (op U.unop.2) a := by
  sorry

/-- The unique quotient-compatible action of the original integral scalar ring.
Source: Stacks 0B6E (blueprint: def-sfb-coherent-integral-mapping-systems). -/
def scalarAlgebra (X : Scheme.{u}) := (scalarAlgebra_existsUnique l E X).exists.choose

/-- The existing normalized calculus on the actual pro-etale quotient-ring system.
Source: Zheng 4.1, 4.10 (blueprint: def-sfb-coherent-integral-mapping-systems). -/
def calculus (X : Scheme.{u}) : Data.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients l E X) (transitions l E X) :=
  (Classical.choice (semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X))).systems

/-- The ordinary unbounded integral proper direct image over the same continuous ring.
Source: the recorded pro-etale coefficient pushforward
(blueprint: def-sfb-coherent-integral-mapping-systems). -/
def integralPush {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  (CondensedRing.lowerStar
    (abelianPoint (Padic.coefficientExtensionIntegers l E)) p).rightDerivedFunctor

end AlgebraicGeometry.ProEtale.CoherentReduction
