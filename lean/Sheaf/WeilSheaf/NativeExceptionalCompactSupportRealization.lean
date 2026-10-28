/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

/-! # Coefficient realization of ordinary native compact support

Source: the scalar-realization step of
cor-coef-verdier-weil-equivariance.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.LocallyFiniteAdicRealization

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]

/-- The specified common-stage compact-support operation is realized by the ordinary
native open/proper functor. This involves no Weil category or forgetful model.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence and coefficient-comparisons paragraph;
Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-exceptional-compact-support-realization).

Proof: at every finite coefficient subfield use S.ring.rationalLeft to identify
the specified left operation with the prescribed rational compact-support functor.
For an integral representative, apply the inverse target integral realization,
the inverse integral compact-support realization and the proper/open scalar mate,
then compact support of the inverse source integral realization. The scalar mate
is invertible on constructible inputs by bounded-below proper scalar comparison
and exact open extension. The section equivalence reflects these isomorphisms.
Extend over inverse uniformizer powers to rational arrows. The normalized integral
scalar squares and the common_field equations of the specified source and target realizations make
these finite-stage maps compatible with every finite field inclusion. Compose
with S.common.commonComparison, and descend the maps and their inverses on common
finite-stage representatives. Every arrow is represented over a common field;
the compatibility square makes the construction independent of enlargement and
proves naturality. This yields the displayed natural isomorphism for the specified source, target
and S, without choosing alternative realizations. Empty schemes and identity
coefficient extensions use the same unit-normalized maps. -/
theorem system_compact_support_realization (f : X ⟶ Y)
    [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (source : Realization l X) (target : Realization l Y)
    (S : ConstructibleExceptionalCoefficients.System.{u, 0} l (PadicAlgCl l) D hl (f := f))
    (c : Compactification f) :
    Nonempty ((S.ring.operation c .closed).F ⋙ target.J ≅ source.J ⋙ actual l c) := by sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
