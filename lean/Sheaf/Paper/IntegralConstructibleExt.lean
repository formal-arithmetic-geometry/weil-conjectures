/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.Paper.IntegralStratumExtBound
import Sheaf.SixFunctors.IntegralExtHomContinuity

/-!
# Continuity and boundedness of integral constructible Ext

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext/_section.md
and sk-lem-int-ext.proof.md (blueprint: sk-lem-int-ext).
The derived category is the ordinary unbounded category of module objects over the
pulled-back condensed valuation ring. No completeness or finite Tor condition is added
to its arbitrary second arguments in the continuity assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Continuity for each integer shift and a bound uniform in the second constructible sheaf.
Source: blueprint main-20261015, sk-lem-int-ext, assertions 1--2
(blueprint: sk-lem-int-ext).

Proof: Fix a bounded constructible C and an integer q. The statement of
`det-lem-int-ext-continuity` gives that the canonical map from the colimit of
Hom(C,K_i[q]) to Hom(C,(colim K_i)[q]) is an isomorphism for every filtered diagram
of complexes with a common termwise lower bound. This is the first conjunct.
For the second conjunct fix a constructible sheaf C. The final consequence of
`det-lem-int-ext-bound` gives an integer d_C, independent of N, above which all
Ext(C,N) vanish for constructible N. Its proof reduces C by a finite filtration
to extensions by zero of finite constant local models on strata. The closed-support
fibre sequence, finite Tor amplitude of the dual, and finite cohomological dimensions
bound the Ext groups of each reduction of N. Derived completeness and the Milnor
sequence add at most one to that bound. Taking a maximum over the finitely many pieces
gives d_C. Ext in integer degree q is the ambient Hom from C[0] to N[0][q]; its vanishing
is expressed by Subsingleton on that abelian Hom group. -/
theorem integralConstructibleExt
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (∀ C : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X C →
      ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
        (K : I ⥤ CochainComplex
          (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) ℤ),
        (∃ b : ℤ, ∀ (i : I) (r : ℤ), r < b → IsZero ((K.obj i).X r)) →
        ∀ q : ℤ, IsIso (colimit.desc _
          ((DerivedCategory.Q ⋙ shiftFunctor _ q ⋙ preadditiveCoyoneda.obj (op C)).mapCocone
            (colimit.cocone K)))) ∧
    (∀ C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X),
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X C →
      ∃ d : ℤ, ∀ N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X),
        IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X N →
        ∀ q : ℤ, d < q →
          Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C) ⟶
            ((DerivedCategory.singleFunctor _ 0).obj N)⟦q⟧)) := by
  sorry

end AlgebraicGeometry.ProEtale
