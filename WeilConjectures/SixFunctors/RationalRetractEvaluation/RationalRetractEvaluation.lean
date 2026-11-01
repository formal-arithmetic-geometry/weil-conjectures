/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.LegacySitePerfectComplex
public import WeilConjectures.SixFunctors.Rational.RationalVerdier
public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
public import WeilConjectures.SixFunctors.RationalOperations.RationalHomIdentifications
public import WeilConjectures.SixFunctors.RationalOperations.RationalExceptionalIdentifications
public import WeilConjectures.SixFunctors.RationalOperations.RationalDualizingIdentification
public import WeilConjectures.SixFunctors.Completed.CompletedTensorHomTranspose
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

import WeilConjectures.SixFunctors.Rational.RationalTensorSymmetry
import WeilConjectures.SixFunctors.Rational.RationalHomScalarTranspose
import WeilConjectures.SixFunctors.Rational.RationalVerdier
import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
import WeilConjectures.SixFunctors.RationalOperations.RationalHomIdentifications
import WeilConjectures.SixFunctors.RationalOperations.RationalExceptionalIdentifications
import WeilConjectures.SixFunctors.RationalOperations.RationalDualizingIdentification
import WeilConjectures.SixFunctors.Completed.CompletedTensorHomTranspose
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
import WeilConjectures.SmoothPurity.Supporting.LegacySitePerfectComplex

/-! # Rational evaluation on retracts and finite scalar extension

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-rational-retract-evaluation, statement and proof paragraphs 1--3
(blueprint: lem-coef-rational-retract-evaluation).

The predicates spell out the clauses using the actual raw rational category,
normalized completed tensor-Hom transpose, and signed symmetry. The Hom-domain
witness in the conclusion is infrastructure supplied by rational operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalRetractEvaluation

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (h : ∀ K M : sfRationalConstructibleCategory l E X,
    constructibleRationalHomPairs l E X (op K, M))

/-- The Hom-first transpose, on the recorded permitted pair.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-rational-retract-evaluation). -/
def adjoint {K L W : sfRationalConstructibleCategory l E X}
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W) :
    K ⟶ (RationalOperations.homDual l E X h W).obj (op L) :=
  (@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).transpose K
    ⟨(op L, W), h L W⟩ b

/-- Perfection means that both actual adjoints are isomorphisms; the second uses
Koszul symmetry. Source: blueprint statement, second sentence
(blueprint: lem-coef-rational-retract-evaluation). -/
def IsPerfect {K L W : sfRationalConstructibleCategory l E X}
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W) : Prop :=
  IsIso (adjoint D l hl X E h b) ∧
    IsIso (adjoint D l hl X E h
      ((@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) L K).hom ≫ b))

/-- The usual Hom-first evaluation to any target, including omega and the unit.
Source: blueprint proof paragraphs 1 and 3
(blueprint: lem-coef-rational-retract-evaluation). -/
def evaluation (K W : sfRationalConstructibleCategory l E X) :
    (RationalVerdier.tensor D l hl X E).obj
      ((RationalOperations.homDual l E X h W).obj (op K), K) ⟶ W :=
  (@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).evaluation
    ⟨(op K, W), h K W⟩

/-- Finite scalar extension uses the coefficient-passage tensor comparison,
with no unrelated pairing or map chosen. The target becomes the scalar-extended
original target. Source: blueprint statement and proof paragraph 2
(blueprint: lem-coef-rational-retract-evaluation). -/
def ScalarExtension (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (ι : E →ₐ[Padic l] F)
    (hF : ∀ K M : sfRationalConstructibleCategory l F X,
      constructibleRationalHomPairs l F X (op K, M)) : Prop :=
  ∀ (K L W : sfRationalConstructibleCategory l E X)
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W),
    IsPerfect D l hl X E h b →
    IsPerfect D l hl X F hF
      ((@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
        (RationalVerdier.units D l hl X)).inv.app (K, L) ≫
        (RationalVerdier.scalar l X E F ι).map b)

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
include D hl in
end WeilConjectures.RationalRetractEvaluation

namespace WeilConjectures

end WeilConjectures
