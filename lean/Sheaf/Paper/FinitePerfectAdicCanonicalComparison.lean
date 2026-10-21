/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.FinitePerfectAdicCoefficientLimit
public import Sheaf.Paper.FinitePerfectAdicQuotientDiagram

/-! # The canonical quotient diagram as an explicit coefficient complex

Source: Stacks Project, Tag 09C6, the finite-projective quotient comparison;
Modules on Sites, Tags 093J--093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The canonical algebraic quotient diagram is computed by the corresponding explicit
coefficient complex and its compatible finite-free summands.

Source: Stacks Project, Tag 09C6, the displayed finite-projective quotient calculation;
Modules on Sites, Tags 093J--093M; More on Algebra, Tag 09AW.
(blueprint: lem-weil-pbc-finite-perfect-adic-canonical-comparison).

Proof: use Module.Finite.exists_comp_eq_id_of_projective to split each term of P
from a finite power of A, with projection composed with inclusion equal to id. Form its
ordinary completed constant realization and, at each quotient level, the same
idempotent summand of the finite coefficient module. The scalar normalization
identifies the ordinary quotient maps with the coefficient projections. Naturality
for linear maps makes the differentials and all tower maps commute, giving a complex
tower T and its explicit cone c. The same inclusions and projections supply compatible
finite-free retracts of both diagrams and cones in each degree. Exact constant
sheafification preserves the bounded flat representative. Flatness of the completed
coefficient algebra and the finite quotient comparisons identify this representative
with completed derived scalar extension of P, and its quotient levels with the
realization of derived A/I^(n+1) tensor P. Uniqueness of left adjoints identifies each
supplied L_n with derived scalar extension, preserving its unit. Their canonical
transitions are transposes of these units, so the comparisons form an isomorphism
of entire diagrams. The cone point comparison is the ordinary-to-derived comparison
on the bounded flat complex. No inverse limit or Roos assertion is used here. Zero
terms, rank zero, and the zero coefficient ring give zero summands throughout. -/
theorem finitePerfectAdicCanonical_comparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction d.ideal n)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) :
    ∃ (T : ℕᵒᵖ ⥤ CochainComplex (CompletedAdicModules X d) ℤ) (c : Cone T),
      (∀ j : ℤ, Nonempty (FinitePerfectAdicCoefficientRetract X d
        (T ⋙ HomologicalComplex.eval (CompletedAdicModules X d) (.up ℤ) j)
        ((HomologicalComplex.eval (CompletedAdicModules X d) (.up ℤ) j).mapCone c))) ∧
      Nonempty (T ⋙ DerivedCategory.Q ≅
        finitePerfectAdicQuotientDiagram d.ideal L adj (DerivedCategory.Q.obj P) ⋙
          finitePerfectAdicDerivedConstant X A ⋙
            completedAdicDerivedChange X (completedAdicScalar X d)) ∧
      Nonempty (DerivedCategory.Q.obj c.pt ≅
        (completedAdicDerivedChange X (completedAdicScalar X d)).obj
          ((finitePerfectAdicDerivedConstant X A).obj (DerivedCategory.Q.obj P))) := by
  sorry

end AlgebraicGeometry.Scheme
