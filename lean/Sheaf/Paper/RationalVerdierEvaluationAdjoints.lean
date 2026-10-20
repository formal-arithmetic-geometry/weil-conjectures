/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.Paper.CompletedTensorHomTranspose
public import Sheaf.Paper.SitePerfectComplex

/-! # Canonical rational evaluation comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] WeilConjectures.rationalDerivedTensor
  WeilConjectures.rationalDerivedInternalHom WeilConjectures.podRationalClosed
  WeilConjectures.pullbackTensorRationalBraiding

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The two adjoints of the specified Verdier evaluation are the Hom identification
and the evaluation-defined biduality followed by that identification.
Source: blueprint lem-coef-rational-retract-evaluation, proof paragraph 1;
thm-coef-rational-verdier, proof step 5
(blueprint: lem-coef-rational-verdier-evaluation-adjoints).

Proof: compare the normalized integral closed tensor-Hom presentation with the
one in A. On ordinary representatives both evaluations are the same counit;
precomposing with the fixed ordinary-to-completed tensor unit determines the
completed evaluation uniquely. The uniqueness clause of podIntegralClosed then
identifies their transposes. Scalar localization preserves these identifications
on pure tensors, hence on all maps. Uniqueness of right adjoints gives the
natural isomorphism e; contravariance fixes its direction. The identity-counit
transpose gives the first formula. Swapping the inputs a second time cancels
the two Koszul signs; by A.bidual_integral this transpose is the recorded delta,
not an arbitrary double-dual isomorphism. Composing it with e at A.dual(K)
gives the second formula. All domain witnesses are propositions, so the same
formulas hold for every h. -/
theorem rationalVerdier_evaluation_adjoints
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w) :
    ∃ e : A.dual ≅ RationalOperations.homDual l E X h
        ((sfRationalConstructibleLocalization l E X).obj w.omega),
      ∀ K : sfRationalConstructibleCategory l E X,
        ((@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).transpose
          (A.dual.obj (op K))
          ⟨(op K, (sfRationalConstructibleLocalization l E X).obj w.omega), h K _⟩
          ((@pullbackTensorRationalBraiding l _ E _ _ _ X
            (RationalVerdier.units D l hl X) (A.dual.obj (op K)) K).hom ≫
              A.evaluation K) = e.hom.app (op K)) ∧
        ((@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).transpose
          K ⟨(op (A.dual.obj (op K)),
            (sfRationalConstructibleLocalization l E X).obj w.omega), h _ _⟩
          (A.evaluation K) = A.bidual.hom.app K ≫ e.hom.app (op (A.dual.obj (op K)))) := by
  sorry

end WeilConjectures
