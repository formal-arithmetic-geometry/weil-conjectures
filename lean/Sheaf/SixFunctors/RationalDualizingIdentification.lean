/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.SixFunctors.RationalOperationsData

/-! # The rational dualizing object and the structure exceptional adjoint

Source: lem-coef-rational-operations, step 11
(blueprint: lem-sf-rational-dualizing-identification).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The dualizing object is the exceptional value of the actual coefficient unit.
Source: lem-coef-rational-operations, DAG proof step 11
(blueprint: lem-sf-rational-dualizing-identification).

Proof: the integral exceptional adjunction at the structure morphism identifies its
value on the completed regular module with the coherent integral dualizing object.
Compare this adjunction with the integral part of S using their common compact-support
functor and the specified normalized realization. The right-adjoint uniqueness comparison
is obtained by transposing the other counit; composing the two such comparisons gives the
identity by the triangle identities. Thus the integral dualizing identification concerns
the actual adjunction, not just matching finite reductions. Localize the comparison.
S.fields.rationalizationComparison identifies the localized integral right adjoint with
S's rational right adjoint. The coefficient object is the completed regular module,
localized, which is coefficientUnit by definition. Evaluating the composite isomorphism
at this object gives the asserted isomorphism. The coherent datum w is compared by its
normalized finite counit maps before taking the total derived limit. -/
theorem rationalDualizing_identification
    (S : structureSystem l X D hl Ω) (F : FieldStage.{u} l)
    (w : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier) :
    DualizingIdentification l X D hl Ω S F w := by sorry

end WeilConjectures.RationalOperations
