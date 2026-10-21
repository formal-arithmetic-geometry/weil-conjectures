/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.QcqsCompactSupportRealization

/-! # Exactness of a normalized common-stage compact-support action

Source: Bhatt--Scholze, Definition 6.7.6 and Proposition 6.8.14;
the common-stage descent construction of the Weil conjectures blueprint
(blueprint: lem-zl-field-shriek-lower-bound-common-stage-exactness).

This is the exactness component of the field compact-support theorem.  It is
split from the lower-bound assertion because the action record exposes the
finite functors and their normalized coefficient maps, while the descent of
their shift and triangle structures is a separate categorical result.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

/-- A normalized common-stage compact-support action is exact and commutes with
integer shifts.  Proof in words: realize the finite integral functors by exact open extension
followed by proper derived image using the projection-normalized realization.
Give each the shift structure transported through its fully faithful ambient
inclusion.  The finite scalar comparison is the tensor-unit mate: its source
and target adjunction units commute with cochain shift, so the mate square
commutes with shift as well.  The normalized integral beta is the same map,
as is checked on the coherent quotient tower with its actual Roos projections;
this uses the full tower comparison, rather than faithfulness of a single
reduction.  Rationalize these maps and shift comparisons on pure tensors.
The rationalBeta equations identify them with the beta maps of S.  Integral
linearity and scalar localization give exactness at each rational stage.
The beta shift squares and S.system.coh now give a coherent exact morphism
of stage systems.  Descend its shifts componentwise.  Their naturality is the
beta square on finite representatives; zero and addition follow at that same
stage.  Every distinguished common-stage triangle is isomorphic to an image
of a distinguished finite-stage triangle.  The descended shift comparison
identifies its connecting arrow with the image under the exact stage functor,
so its image is distinguished.  The descended functor is S.system.functor:
its object formula and beta-conjugated representative formula coincide.
This proves the asserted exactness for every normalized S, including the zero
input, identity morphism, repeated coefficient stages and empty schemes.
Source: Bhatt--Scholze, Definition 6.7.6 and Proposition 6.8.14;
the common-stage descent construction of the Weil conjectures blueprint.
(blueprint: lem-zl-field-shriek-lower-bound-common-stage-exactness). -/
theorem sfCommonStageCompactSupport_exactness
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : Compactification f)
    (S : SfCompactSupportCoefficientAction l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) Ω d) :
    ∃ comm : S.system.functor.CommShift ℤ,
      (fun [commInst : S.system.functor.CommShift ℤ] ↦
        S.system.functor.IsTriangulated) (commInst := comm) := by
  sorry

end WeilConjectures
