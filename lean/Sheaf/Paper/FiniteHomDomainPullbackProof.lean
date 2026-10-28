/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.EtaleDomainPullbackCalculus

/-! Private pullback proof for the finite-Hom domain calculus. -/

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
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit Etale.upperStar
  Etale.scalarGeometricRepresentative

/-- The existing coefficient ring, lifted to the ordinary small-etale coefficient universe.
Source: blueprint finite coefficient convention
(blueprint: lem-coef-finite-hom-domain-calculus). -/
private abbrev proofCoeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))

/-- Positive coefficient levels are finite, by the recorded coefficient-ring theorem.
Source: blueprint finite coefficient convention
(blueprint: lem-coef-finite-hom-domain-calculus). -/
private instance proofCoeffFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (proofCoeff l E n) :=
  @Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))) Equiv.ulift.symm

private theorem insertComparison {P Q R S : Prop} (h : P ∧ R ∧ S) (q : Q) :
    P ∧ Q ∧ R ∧ S := ⟨h.1, q, h.2⟩

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [hXover : X.Over (Spec (.of D.k))]
  [hXsep : IsSeparated (X ↘ Spec (.of D.k))]
  [hXft : LocallyOfFiniteType (X ↘ Spec (.of D.k))] [hXqc : QuasiCompact (X ↘ Spec (.of D.k))]

attribute [local irreducible] ProEtale.pbcFixedScalarExtension
  Etale.scalarExtensionRepresentative Etale.scalarSheafPullbackComplexIso
attribute [local instance 2000] CommRing.toRing

include D hl hXover hXsep hXft hXqc in
/-- Exact inverse image preserves bounded constructibility and the given Tor interval;
the specified scalar/pullback isomorphism is a morphism of B-module derived categories.
Source: blueprint opening proof paragraph; Stacks 04JC, 05VD, 095G, 07A4 and 0G7E
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: prop-weil-pbc-inverse-image-modules-exact identifies pullback with exact inverse
image. Its homology is the inverse image of homology; prop-constructible-pullback
preserves constructibility. Pull the preceding bounded flat constructible model back
termwise. Flatness is preserved by lem-weil-pbc-ringed-topos-flat-module-pullback,
and the same support and lem-kun-kflat-criteria give the Tor interval. The comparison
is the canonical normalized scalarPullbackIso of def-pur-etale-scalar-pullback-iso;
lem-pur-etale-scalar-pullback-existence gives its existence. The exact/derived
identification is lem-pur-exact-pullback-signed-comparison. -/
private theorem domainPullbackProof (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : Y ⟶ X) [f.IsOver (Spec (.of D.k))] {n m : ℕ} (h : m ≤ n) :
    exactFunctor _ _ (Etale.upperStar (ModuleCat.{u + 1} (proofCoeff l E n)) f) ∧
    (∀ (a b : ℤ), a ≤ b → ∀ T : finiteHomEtale l E X n,
      Etale.DerivedCategory.isBoundedConstructible (proofCoeff l E n) X T →
      Etale.DerivedCategory.hasTorAmplitudeIn (proofCoeff l E n) X a b T →
      Etale.DerivedCategory.isBoundedConstructible (proofCoeff l E n) Y
        ((Etale.upperStar (ModuleCat.{u + 1} (proofCoeff l E n)) f).leftDerivedFunctor.obj
          T) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn (proofCoeff l E n) Y a b
        ((Etale.upperStar (ModuleCat.{u + 1} (proofCoeff l E n)) f).leftDerivedFunctor.obj
          T)) ∧
    (∀ P : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (proofCoeff l E n))) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (Etale.scalarPullbackIso (finiteHomQuotient l E h) f).hom.app
          (_root_.DerivedCategory.Q.obj P) ≫
        (finiteHomEtaleReduction l E Y h).map
          (Etale.scalarGeometricRepresentative (proofCoeff l E n) f P) ≫
        Etale.scalarExtensionRepresentative (finiteHomQuotient l E h) Y
          (((Etale.upperStar (ModuleCat.{u + 1} (proofCoeff l E n))
            f).mapHomologicalComplex
            (.up ℤ)).obj P) =
      (Etale.upperStar (ModuleCat.{u + 1} (proofCoeff l E m)) f).leftDerivedFunctor.map
        (Etale.scalarExtensionRepresentative
            (finiteHomQuotient l E h) X P) ≫
        Etale.scalarGeometricRepresentative (proofCoeff l E m) f
          (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        _root_.DerivedCategory.Q.map
          ((Etale.scalarSheafPullbackComplexIso (finiteHomQuotient l E h) f).hom.app P)) := by
  exact scalarDomain_pullback (proofCoeff l E n) (proofCoeff l E m)
    (finiteHomQuotient l E h) X Y f

end WeilConjectures
