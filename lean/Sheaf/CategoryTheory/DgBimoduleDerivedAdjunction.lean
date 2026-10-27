/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.CategoryTheory.DgBimoduleModels
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.LeftDerivedExactWhenDefined
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-!
# Unbounded derived tensor--Hom adjunction for a DG bimodule

Source: Stacks Project, `dga.tex`, Tags 09LT, 09LS, 09LI, 09LN, 09KY,
0FQN and 0FQR (blueprint: lem-sfb-dg-bimodule-derived-adjunction).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.DgAlgebra

/-- For arbitrary unital associative DG algebras and an arbitrary DG bimodule,
balanced tensor and DG Hom have universal total derived functors on the unbounded
localizations. They form the adjunction induced by chain currying. Hom is computed
on homotopically injective resolutions; no flatness or boundedness is assumed.
The degree-one shift squares pin the derived shift comparisons to the sign-free
ordinary comparisons; a `CommShift ℤ` structure is determined by its degree-one
component, so this fixes every degree. Squares in every degree would also tie the
comparisons to `DerivedStructure.shiftIso` in degrees other than one, which that class
does not make coherent with shift addition. `adj.CommShift` makes the unit and counit
commute with these comparisons.
`IsTriangulated` states preservation of distinguished mapping-cone triangles.

Source: Stacks Project, `dga.tex`, Tags 09LT, 09LS, 09LI, 09LN, 09KY,
0FQN and 0FQR (blueprint: lem-sfb-dg-bimodule-derived-adjunction).

Proof plan (the five steps of the node):
1. Resolve arbitrary M by a property-(P) module P (lem-sfb-dg-property-p-resolution).
The one-object specialization of lem-coef-dg-semi-free-homotopically-projective
makes P homotopically projective. Resolve Y into a homotopically injective I by
lem-sfb-dg-injective-resolution-localization. Localization on these sources and
targets is fully faithful by that lemma and
lem-sfb-dg-homotopically-projective-hom-derived. Quasi-isomorphisms between two
models of the same kind are therefore homotopy equivalences.
2. Lem-sfb-dg-tensor-hom-homotopy-calculus gives exact ordinary homotopy functors
and chain currying. They invert these homotopy equivalences; arbitrary
quasi-isomorphism preservation by ordinary tensor or Hom is not needed.
3. Apply lem-pur-resolving-class-essential-constancy and
lem-pur-left-derived-exact-when-defined to projective models, then to injective
models in opposite categories. Lem-sfb-dg-quasi-isomorphism-localization supplies
both fraction calculi, saturation and the opposite triangulations;
lem-sf-triangulated-functor-opposite supplies opposite exactness. This constructs
the universal T and U, their comparisons, and their exact shifts.
4. Compare Hom(T M,Y) with Hom(P tensor N,I), apply chain currying, and compare
with Hom(M,U Y). The first comparison uses only injectivity of I and the last
only projectivity of P. No projectivity of P tensor N or injectivity of Hom(N,I)
over A is used.
5. Naturality of currying and localization gives natural bijections independent
of choices. Lem-weil-pbc-adjunction-of-natural-bijection constructs the adjunction;
its unit and counit are transposes of identities. Apply the sign-free shift
identities of lem-sfb-dg-tensor-hom-homotopy-calculus to shifted models to obtain
the displayed shift squares and shift-compatible unit and counit. Exactness
already gives preservation of distinguished triangles. -/
theorem bimodule_derived_tensor_hom_adjunction
    (A B : Algebra.{u}) [DerivedStructure A] [DerivedStructure B] (N : Bimod A B) :
    ∃ (F : RightModule A ⥤ RightModule B) (G : RightModule B ⥤ RightModule A)
      (t : BalancedTensorModel N F) (h : BimoduleHomModel N G) (a : F ⊣ G),
      IsBimoduleCurrying N t h a ∧
      ∃ (T : Derived A ⥤ Derived B) (U : Derived B ⥤ Derived A)
        (α : Q A ⋙ T ⟶ F ⋙ Q B) (β : G ⋙ Q A ⟶ Q B ⋙ U)
        (_sT : T.CommShift ℤ) (_sU : U.CommShift ℤ) (adj : T ⊣ U),
        T.IsRightKanExtension α ∧ U.IsLeftKanExtension β ∧
        T.IsTriangulated ∧ U.IsTriangulated ∧ adj.CommShift ℤ ∧
        (∀ (Y : RightModule B), ∃ (I : RightModule B) (i : Y ⟶ I),
          quasiIsomorphisms B i ∧ IsHomotopicallyInjective B I) ∧
        (∀ (I : RightModule B), IsHomotopicallyInjective B I → IsIso (β.app I)) ∧
        (∀ (M : RightModule A) (Y : RightModule B) (g : F.obj M ⟶ Y),
          adj.homEquiv ((Q A).obj M) ((Q B).obj Y) (α.app M ≫ (Q B).map g) =
            (Q A).map (a.homEquiv M Y g) ≫ β.app Y) ∧
        (∀ (M S : RightModule A) (e : ShiftComparison A 1 M S),
          ∃ eF : ShiftComparison B 1 (F.obj M) (F.obj S),
            IsTensorShift N t 1 M S e eF ∧
            T.map (DerivedStructure.shiftIso 1 M S e).hom ≫
                (Functor.commShiftIso T (1 : ℤ)).hom.app ((Q A).obj M) ≫
                  (α.app M)⟦(1 : ℤ)⟧' =
              α.app S ≫ (DerivedStructure.shiftIso 1 (F.obj M) (F.obj S) eF).hom) ∧
        (∀ (Y S : RightModule B) (e : ShiftComparison B 1 Y S),
          ∃ eG : ShiftComparison A 1 (G.obj Y) (G.obj S),
            IsHomShift N h 1 Y S e eG ∧
            β.app S ≫ U.map (DerivedStructure.shiftIso 1 Y S e).hom ≫
                (Functor.commShiftIso U (1 : ℤ)).hom.app ((Q B).obj Y) =
              (DerivedStructure.shiftIso 1 (G.obj Y) (G.obj S) eG).hom ≫
                (β.app Y)⟦(1 : ℤ)⟧') := by
  sorry

end CategoryTheory.DgAlgebra
