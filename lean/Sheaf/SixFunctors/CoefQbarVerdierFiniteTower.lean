/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData

/-! Tower component of normalized finite Verdier coherence.

Source: thm-coef-qbar-verdier, composition clause.
(blueprint: lem-coef-qbar-verdier-finite-tower-equation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage transition associator)
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The tower component equation for a finite Verdier datum.
Source: thm-coef-qbar-verdier, final coefficient-transport paragraph;
(blueprint: lem-coef-qbar-verdier-finite-tower-equation).

Proof: identify the three coefficient inclusions and their composite using the
coefficient-inclusion composition law. Apply RationalVerdier.extension_composition
to the normalized extensions and use its integral normalization clause. The canonical
scalar associator has the same normalized integral component, by its uniqueness
specification. Transport the resulting equality through the stage associator and
retain the dependent endpoint equality as HEq. Repeated fields, zero objects, and the
empty scheme are included automatically. -/
theorem finite_tower_equation (F : Finite D l hl Ω X) :
    ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) (K : Stage l Ω X E),
      HEq
        ((transition l Ω X L M k).map ((F.beta E L h).hom.app (op K)) ≫
          (F.beta L M k).hom.app (op ((transition l Ω X E L h).obj K)))
        ((associator l Ω X E L M h k).hom.app
            ((F.datum E).dual.obj (op K)) ≫
          (F.beta E M (h.trans k)).hom.app (op K) ≫
            (F.datum M).dual.map
              ((associator l Ω X E L M h k).hom.app K).op) := by
  sorry

end WeilConjectures.CoefQbarVerdier
