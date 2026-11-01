/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomScalarMonoidal

/-! Private monoidal proof for the finite-Hom domain calculus. -/

@[expose] public noncomputable section
-- This module intentionally exports only a private proof to its single importer.
set_option linter.privateModule false
set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a₁ a₂ a₃ b₁ b₂ b₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

attribute [local implicit_reducible] CategoryTheory.uniformProd

attribute [local implicit_reducible] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory

attribute [local irreducible] _root_.DerivedCategory.monoidalClosed

/-- The existing coefficient ring, lifted to the ordinary small-etale coefficient universe.
Source: blueprint finite coefficient convention
(blueprint: lem-coef-finite-hom-domain-calculus). -/
private abbrev proofCoeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))

private theorem insertComparison {P Q R S : Prop} (h : P ∧ R ∧ S) (q : Q) :
    P ∧ Q ∧ R ∧ S := ⟨h.1, q, h.2⟩

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [hXover : X.Over (Spec (.of D.k))]
  [hXsep : IsSeparated (X ↘ Spec (.of D.k))]
  [hXft : LocallyOfFiniteType (X ↘ Spec (.of D.k))] [hXqc : QuasiCompact (X ↘ Spec (.of D.k))]


include D hl hXover hXsep hXft hXqc in
/-- The canonical tensor and constant-unit comparisons make ambient coefficient change
strong symmetric monoidal, for the actual signed tensor and Koszul braiding.
Source: blueprint opening proof paragraph; Stacks 07A4 and 0FPT
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: use scalarExtension_coreMonoidal for the actual quotient ring map. That
proved generic theorem transports the native derived monoidal structure along
uniqueness of left adjoints. Right-exact tensor normalization identifies its
tensorator with the published tensorIso, the left unit law identifies its unit,
and braidedness descends from the ordinary scalar adjunction. The normalization
of finiteHomEtaleData identifies its tensor comparison with finiteHomEtaleTensor;
the all-complex tensor and unit normalization clauses are their choose_spec laws. -/
private theorem domainMonoidalProof {n m : ℕ} (h : m ≤ n) :
    FiniteHomDomainMonoidal (finiteHomEtaleReduction l E X h)
      (fun U V ↦ (Etale.ExceptionalCoefficients.tensorIso
        (finiteHomQuotient l E h) X).app (U, V))
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E h) X)
      (finiteHomKoszulIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (proofCoeff l E n))))
      (finiteHomKoszulIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (proofCoeff l E m)))) ∧
    HEq (finiteHomEtaleTensor l E X h)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X) ∧
    Etale.ExceptionalCoefficients.UnitNormalization (finiteHomQuotient l E h) X
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E h) X) ∧
    Etale.ExceptionalCoefficients.TensorNormalization (finiteHomQuotient l E h) X
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X) := by
  exact insertComparison
    (finiteHomScalar_monoidal (proofCoeff l E n) (proofCoeff l E m)
      (finiteHomQuotient l E h) X)
    ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.tensor n m h)

end WeilConjectures
