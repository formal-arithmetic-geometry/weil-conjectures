/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.Compactification.BoundaryRefinement

/-!
# The projective line, rational coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/
  sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/
  sk-prop-p1-adjunction-rational/_section.md, Proposition sk-prop-p1-adjunction-rational,
  and sk-prop-p1-adjunction-rational.proof.md in the same folder.
(blueprint: sk-prop-p1-adjunction-rational)

Proof route recorded by the blueprint: (1) define the unit and counit from the geometric
projective-line formulas and the diagonal tensor identification; (2) use projection formula,
proper base change, and direct-image composition to reduce the two triangle composites to the
first and second diagonal integrals; (3) use the diagonal-tower trace identities to make both
integrals identities; (4) obtain the adjunction on the localizing categories; and (5) identify
those categories with the finite-Tor constructible localizing closures and transport the Brown
right adjoint along the canonical inclusion comparisons.  Uniqueness of right adjoints then
identifies the transported exceptional functor with `q^!`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RationalP1

/-- The rational projective-line adjunction, stated on the literal `Loc(Dctf)` closures.
The first three clauses provide the restrictions of derived direct image and of pullback with
Tate twist and shift two, together with their adjunction.  The final clause identifies every
compactification right adjoint supplied by exceptional-adjoint existence with that restricted
Tate-twisted pullback.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/
sk-prop-p1-adjunction-rational/_section.md, Proposition sk-prop-p1-adjunction-rational
(blueprint: sk-prop-p1-adjunction-rational).

Proof (node steps):
1. The unit and counit on the localizing categories are the explicit transformations of
   det-prop-p1-adjunction-rational-unit-counit: the diagonal tensor identification
   `Δ_* M ≃ p₁^* M ⊗ Δ_* Λ`, the unit formula via proper base change, the counit formula via
   the projection formula, and their naturality and exactness.
2. det-prop-p1-adjunction-rational-triangle reduces both triangle composites to the diagonal
   integrations `Tr_{p_i} ∘ Rp_{i*} δ_Λ` and proves each is the identity (projection formula,
   proper base change, direct-image composition); this gives `Rq_* ⊣ q^*(1)[2]` on
   `Loc(Dbc)`. Since `Y` and `P¹_Y` are qcqs and `Λ ∈ {E, Q̄_ℓ}`,
   det-def-localizing-closure-ctf-equals-bc (2) identifies `Loc(Dctf) = Loc(Dbc)` as full
   subcategories, giving `F ⊣ G` on `localizingClosureProEtale`. For every compactification
   of `q`, a right adjoint of `localizingLowerShriek` (the `q^!` of sk-prop-sf-existence) is
   isomorphic to `G` by uniqueness of right adjoints.
-/
theorem sk_prop_p1_adjunction_rational
    (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] :
    ∃ (F : (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory ⥤
        (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory)
      (G : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ⥤
        (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory),
      Nonempty (F ⋙ (localizingClosureProEtale (coefficient l c).X Y).ι ≅
        (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).ι ⋙
          moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)) ∧
      Nonempty (G ⋙ (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).ι ≅
        (localizingClosureProEtale (coefficient l c).X Y).ι ⋙
          moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y) ⋙
            twist (coefficient l c).X (ProjectiveLine Y)
              (line l c (ProjectiveLine Y))) ∧
      Nonempty (F ⊣ G) ∧
      ∀ (compactification : Compactification.BoundaryCompactification (ProjectiveLine Y ↘ Y))
        (h : ∀ A, localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y) A →
          localizingClosureProEtale (coefficient l c).X Y
            ((rightDerivedLowerShriekOfCompactification (coefficient l c).X
              compactification.obj.obj).obj A))
        (G' : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ⥤
          (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory),
        (localizingLowerShriek (coefficient l c).X compactification.obj.obj h ⊣ G') →
          Nonempty (G' ≅ G) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
