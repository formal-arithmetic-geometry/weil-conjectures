/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Restrict

/-! # The candidate syntomic open of fixed relative dimension

Source: Stacks Project, morphisms.tex, Tags 01UF, 02V3, 02NM, 02K1 and
Definition definition-syntomic-relative-dimension
(blueprint: def-sfb-syntomic-fixed-dimension-open).

The geometric-fibre lci predicate is the existing declaration recorded by
`def-sfb-local-complete-intersection-over-field`. No affine criterion theorem is used
in these definitions. The candidate open is a supremum, without an existence choice.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Syntomic of relative dimension `d`, in the geometric-fibre formulation: flat,
locally finitely presented, with local-complete-intersection geometric fibres pure of
dimension `d`. The existing pure-dimension predicate includes empty fibres.
Source: Stacks Project, morphisms.tex, Tags 01UF, 02K1 and 02NK
(blueprint: def-sfb-syntomic-fixed-dimension-open). -/
def Scheme.Hom.IsSyntomicOfRelativeDimension {P T : Scheme.{u}} (g : P ⟶ T)
    (d : ℕ) : Prop :=
  Flat g ∧ LocallyOfFinitePresentation g ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      IsLocalCompleteIntersectionOver Ω (pullback g t) (pullback.snd g t) ∧
        (pullback g t).IsPureDimension d

/-- The union of source opens on which the morphism is syntomic of relative dimension
`d`. This is an explicit open, without selecting a witness to an existence theorem.
Source: Stacks Project, morphisms.tex, Tags 02V3, 02NM and 02K1
(blueprint: def-sfb-syntomic-fixed-dimension-open). -/
noncomputable def Scheme.Hom.syntomicFixedDimensionOpen {P T : Scheme.{u}} (g : P ⟶ T)
    (d : ℕ) : P.Opens :=
  sSup {U : P.Opens | (U.ι ≫ g).IsSyntomicOfRelativeDimension d}

end AlgebraicGeometry
