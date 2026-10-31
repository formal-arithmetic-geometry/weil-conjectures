/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedPurityCoefficientChange
public import WeilConjectures.AlgebraicGeometry.RationalLocalizedHom
public import WeilConjectures.AlgebraicGeometry.TransportIntegralCounitRealization
public import WeilConjectures.AlgebraicGeometry.CondensedRationalAdjunction
public import WeilConjectures.AlgebraicGeometry.CondensedQbarPurityAdjunction
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Native condensed purity and trace under coefficient change

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
  sk-thm-purity-transport/sk-thm-purity-transport-coefficient-change.md,
  det-sp-purity-coefficient-change, clauses (1)--(3)
  (blueprint: prop-pur-condensed-purity-coefficient-change).

The statement uses the three specified adjunction interfaces: the realized integral
adjunction, the native rational adjunction, and the finite-field/algebraic-closure
adjunction.  It defines the purity map by `rightAdjointUniq` and the trace by the
specified counit.  The compact-support comparisons in the finite-reduction and
localization clauses are the named `b_n` and `b_E` maps, identified with the native
scalar compact-support map by the corresponding dependency results.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCondensedPurityCoefficientChange

/-- The counit-compatible purity comparison from a specified adjunction to a specified
Brown right adjoint.  This is exactly the transpose supplied by
`CategoryTheory.Adjunction.rightAdjointUniq`.
Source: det-sp-unique-right-adjoint (blueprint: prop-pur-condensed-purity-coefficient-change).
-/
def specifiedGamma {ell : ℕ} [Fact ell.Prime]
    {D : WeilConjectures.FiniteFieldDatum.{u}} {c : Coefficient ell} {s : SmoothDatum D}
    (A : ExplicitAdjunction ell D c s)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification) :
    source ell c s.map s.dim A.source_closed ≅ R.upper :=
  A.adjunction.rightAdjointUniq R.restrictedAdjunction

/-- The smooth trace attached to the specified adjunction is its actual counit.
Source: the definition of `Tr` in det-sp-purity-coefficient-change
(blueprint: prop-pur-condensed-purity-coefficient-change).
-/
def specifiedTrace {ell : ℕ} [Fact ell.Prime]
    {D : WeilConjectures.FiniteFieldDatum.{u}} {c : Coefficient ell} {s : SmoothDatum D}
    (A : ExplicitAdjunction ell D c s) (K : c.ctf ell s.Y.left) :=
  (A.adjunction.counit.app K).hom

/-- Every rational constructible object has an integral model, in the exact native
encoding used by `det-sp-rational-localized-hom`.
Source: det-sp-rational-localized-hom (blueprint: prop-pur-condensed-purity-coefficient-change).
-/
def RationalModelClause (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)] : Prop :=
  ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [IsNoetherian T]
    (E : PadicAlgCl.FiniteIntermediateField ell),
    ∀ K : RationalLocalizedHom.rational T ell E,
      RationalLocalizedHom.rationalConstructible T ell E K →
        ∃ K₀ : RationalLocalizedHom.integral T ell E,
          RationalLocalizedHom.integralConstructible T ell E K₀ ∧
          Nonempty ((RationalLocalizedHom.extend T ell E).obj K₀ ≅ K)

/-- The four adjunctions named in the coefficient-change statement.  The equalities
identify the endpoint fields with the corresponding entries of the common family;
there is no existentially chosen unpinned adjunction in the statement.
Source: lem-pur-transport-integral-counit-realization, prop-pur-condensed-rational-
adjunction, and prop-pur-condensed-qbar-adjunction (blueprint: prop-pur-condensed-
purity-coefficient-change).
-/
structure SpecifiedAdjunctions (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) where
  finite : AdjunctionFamily ell D
  integral : ∀ (E : PadicAlgCl.FiniteIntermediateField ell) (s : SmoothDatum D),
    ExplicitAdjunction ell D (.integral E) s
  rational : ∀ (E : PadicAlgCl.FiniteIntermediateField ell) (s : SmoothDatum D),
    ExplicitAdjunction ell D (.rational E) s
  qbar : ∀ (s : SmoothDatum D), ExplicitAdjunction ell D (.closure) s
  integral_eq : ∀ E s, integral E s = finite (.integral E) s
  rational_eq : ∀ E s, rational E s = finite (.rational E) s
  qbar_eq : ∀ s, qbar s = finite .closure s

/-- The structural-map specialization: the dualizing source and its integration
counit are the finite maps transported by the integral limit, localization, and
finite-field scalar extension comparisons.
Source: the final assertion of det-sp-purity-coefficient-change
(blueprint: prop-pur-condensed-purity-coefficient-change).
-/
def StructuralIntegrationClause (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (A : AdjunctionFamily ell D) : Prop :=
  ∀ (c : Coefficient ell) (s : SmoothDatum D)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification),
    ∀ (hK : property ell c s.Y.left (unit ell c s.Y.left)),
      Nonempty ((source ell c s.map s.dim (A c s).source_closed).obj ⟨_, hK⟩ ≅
        (R.upper.obj ⟨_, hK⟩)) ∧
      (specifiedTrace (A c s) ⟨_, hK⟩ =
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification).map
          ((specifiedGamma (A c s) R).hom.app ⟨_, hK⟩).hom ≫ R.counit ⟨_, hK⟩)

/-- The direct coefficient-change equations on the native categories.  The arrows
`scalarCompactSupportMap` are the dependency-specified `b` maps; in the reduction and
localization cases the named `b_n` and `b_E` comparisons are identified with these
maps by `det-sp-integral-direct-image-tower` and `det-sp-rational-localized-hom`.
The exceptional map is the adjoint transpose of that same `b` and the counit.
Source: det-sp-purity-coefficient-change, opening paragraph and clauses (1)--(3)
(blueprint: prop-pur-condensed-purity-coefficient-change).
-/
def NativeCoefficientChangeLaws (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (A : SpecifiedAdjunctions ell D)
    (P : PurityCoefficientChange.Coordinates.{u} ell) : Prop :=
  ∀ (c c' : Coefficient ell)
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : ListedScalarChange ell a) (s : SmoothDatum D)
    (R : ScalarExceptionalAdjoint (c.bundled ell) s.compactification)
    (S : ScalarExceptionalAdjoint (c'.bundled ell) s.compactification),
    (∀ K : c.ctf ell s.Y.left,
      IsIso (PurityCoefficientChange.sourceMap ell D P a ha s K.obj) ∧
      (scalarSixChange a s.X.left).map
          ((specifiedGamma (A.finite c s) R).hom.app K).hom ≫
          ((PurityCoefficientChange.exceptionalMap ell D hEll a ha s R S).app K).hom =
        PurityCoefficientChange.sourceMap ell D P a ha s K.obj ≫
          ((specifiedGamma (A.finite c' s) S).hom.app
            ((PurityCoefficientChange.change ell D hEll a ha s.Y).obj K)).hom ∧
      (scalarSixChange a s.Y.left).map (R.counit K) =
        (scalarCompactSupportMap a s.compactification.i s.compactification.g).app
            (R.upper.obj K).obj ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map
            ((PurityCoefficientChange.exceptionalMap ell D hEll a ha s R S).app K).hom ≫
          S.counit ((PurityCoefficientChange.change ell D hEll a ha s.Y).obj K) ∧
      (scalarSixChange a s.Y.left).map
          (specifiedTrace (A.finite c s) K) =
        (scalarCompactSupportMap a s.compactification.i s.compactification.g).app
            ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map
            (PurityCoefficientChange.sourceMap ell D P a ha s K.obj) ≫
          specifiedTrace (A.finite c' s)
            ((PurityCoefficientChange.change ell D hEll a ha s.Y).obj K)) ∧
    ∀ (K L : c.ctf ell s.Y.left) (v : K ⟶ L),
      (scalarSixChange a s.X.left).map
          ((c.smoothSource ell s.map s.dim).map v.hom) ≫
          PurityCoefficientChange.sourceMap ell D P a ha s L.obj =
        PurityCoefficientChange.sourceMap ell D P a ha s K.obj ≫
          (c'.smoothSource ell s.map s.dim).map
            ((scalarSixChange a s.Y.left).map v.hom)

/-- The native coefficient-change statement.  The specified finite, integral,
rational, and algebraically closed adjunctions are supplied by the three recorded
adjunction declarations; `A` is their common explicit family on the coefficient
presentations.  `models` is the integral-model clause, `structural` is the final
structural-map clause, and `laws` gives the purity, counit, trace, naturality, and
identity/successive-change equations.
(blueprint: prop-pur-condensed-purity-coefficient-change).

Proof steps. 1. Use the realized integral counit and its tower comparison. 2. Use
`condensed_rational_adjunction` and its localization comparison. 3. Use
`condensed_qbar_purity_adjunction` and finite-subextension descent. 4. Define gamma
by `rightAdjointUniq` and Tr by the specified counit. 5. Identify the reduction and
localization compact-support maps `b_n` and `b_E` with the native scalar map. 6.
Transpose the counit to obtain the exceptional equation and then the trace equation.
7. Use the native scalar associators, Tate root frames, and the finite models to prove
identity, composition, uniformizer reduction, Frobenius, and the structural assertion.
-/
theorem native_condensed_purity_coefficient_change
    (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (A : SpecifiedAdjunctions ell D)
    (P : PurityCoefficientChange.Coordinates.{u} ell)
    : @RationalModelClause ell _ D.k inferInstance
      (PurityCoefficientChange.fieldPrime D)
      (PurityCoefficientChange.fieldDifferent ell D hEll) ∧
      StructuralIntegrationClause ell D A.finite ∧
      NativeCoefficientChangeLaws ell D hEll A P := by
  sorry

end AlgebraicGeometry.ProEtale.NativeCondensedPurityCoefficientChange
