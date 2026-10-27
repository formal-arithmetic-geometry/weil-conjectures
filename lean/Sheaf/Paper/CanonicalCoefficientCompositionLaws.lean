/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CanonicalCoefficientReduction

/-! # Internal composition for normalized coefficient tensor presentations

Source: Stacks 0A98, 08JD and 0941.
(blueprint: lem-pur-canonical-coefficient-composition-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe a b v w t u
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures.CanonicalCoefficient

/-- The internal-composition clause, separate from naturality and transposition. -/
def CompositionLaw {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q V : A,
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map
          (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
            (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Normalized reduction and finite scalar extension preserve internal composition.

Source: Stacks 0A98 (lemma-internal-hom-composition), 08JD (lemma-dual), 07A4, 0941;
canonical integral calculus, proof step 3.
(blueprint: lem-pur-canonical-coefficient-composition-laws).

Proof: use the fixed normalized duality structures on the integral, sequence and
finite sites. Their associators descend reassociation of the same total tensors.
Their tensor-Hom adjunctions are ordinary uncurrying on K-flat/K-injective pairs.
The old pure-tensor reduction and finite scalar maps, conjugated by the adjoint
comparisons, still have those formulas: transpose the comparisons into the fixed
Hom resolution and use uniqueness on sheafified tensor generators. Uncurry the
two sides of the displayed composition equation. On a triple of homogeneous
sections both reassociate the same tensor and apply the two evaluations in the
order phi(psi(x)); the total differential has the same Koszul signs on both sides.
The strict-system calculation is made before evaluation at a finite level.
Generator uniqueness proves the chain equation. K-flat localization in each
variable, followed by naturality along resolution isomorphisms, proves the
identity for all derived inputs. Apply this once to reduction and once at each
finite level. No claim is made that an arbitrary adjoint comparison is monoidal;
the normalized associator formulas are essential. The proof includes zero
objects, the empty scheme, and unbounded complexes. -/
theorem compositionLaws (S : CoefficientDerivedSystemFibers l E W) :
    let R := reduction l E W S.toCoefficientDerivedSystemReduction
    CompositionLaw R.integralClosed R.systemClosed R.reduction R.reductionTensor ∧
      ∀ n : ℕ, CompositionLaw R.integralClosed (R.finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n) := by sorry

end WeilConjectures.CanonicalCoefficient
