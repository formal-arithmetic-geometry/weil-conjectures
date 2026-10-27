/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Sheaf.CategoryTheory.DgBimoduleModels
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import Sheaf.CategoryTheory.DgBimoduleDerivedAdjunction

/-!
# Restriction along a quasi-isomorphism of DG algebras

Source: Stacks Project, dga.tex, Tag 09S6, lemma-qis-equivalence,
and Example 0BYX, example-map-hom-tensor
(blueprint: lem-sfb-dg-qis-restriction-equivalence).

The coordinate models below fix restriction and the extension bimodule up to
unique isomorphism, rather than supplying unspecified functors or actions.
The derived tensor is specified by the universal left-derived comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.DgAlgebra

/-- The extension bimodule is B itself, with multiplication on the right and
left action a b = φ(a)b. Both actions are fixed as maps of actual complexes.
The isomorphism permits only transport of this specified object.
Source: Stacks, dga.tex, Tag 09S6 and Example 0BYX
(blueprint: lem-sfb-dg-qis-restriction-equivalence). -/
structure AlgebraMapBimoduleModel {A B : Algebra.{u}} (φ : A ⟶ B) (N : Bimod A B) where
  iso : N.X ≅ B.X
  left_action : N.actLeft ≫ iso.hom =
    (A.X ◁ iso.hom) ≫ (φ.hom ▷ B.X) ≫ MonObj.mul
  right_action : N.actRight ≫ iso.hom = (iso.hom ▷ B.X) ≫ MonObj.mul

/-- Restriction retains the underlying complex, naturally on all morphisms,
and its right action is exactly precomposition with the given algebra map.
This specifies the ordinary scalar restriction functor up to natural isomorphism.
Source: Stacks, dga.tex, Tag 09S6 and Example 0BYX
(blueprint: lem-sfb-dg-qis-restriction-equivalence). -/
structure ScalarRestrictionModel {A B : Algebra.{u}} (φ : A ⟶ B)
    (G : RightModule B ⥤ RightModule A) where
  underlyingIso : G ⋙ underlying A ≅ underlying B
  action (Y : RightModule B) :
    rightAction A (G.obj Y) ≫ underlyingIso.hom.app Y =
      (underlyingIso.hom.app Y ▷ A.X) ≫
        ((underlying B).obj Y ◁ φ.hom) ≫ rightAction B Y

/-- A quasi-isomorphism of unital associative DG algebras induces the exact
restriction equivalence, with inverse the total left derived balanced tensor.
The unit and counit are those of the specified adjunction, not arbitrary
objectwise isomorphisms. Degree-one comparison squares specify the usual
shift comparisons; `adj.CommShift` gives their compatibility in every degree.

Source: Stacks, dga.tex, Tag 09S6, lemma-qis-equivalence
(blueprint: lem-sfb-dg-qis-restriction-equivalence).

Proof plan:
1. Give B the left A-action through φ. Apply
lem-sfb-dg-bimodule-derived-adjunction. Evaluation f ↦ f(1), inverse x ↦ (b ↦ xb),
identifies DG Hom from B with restriction, including the differential and A-action.
Restriction preserves quasi-isomorphisms, shifts and cones on underlying complexes.
Transport the derived tensor--Hom adjunction along evaluation to get L ⊣ R and
its canonical shift comparisons and shift-compatible unit and counit.
2. Apply lem-sfb-dg-finite-cell-compact to the filtration 0 ⊂ B. Thus B is compact
as a right B-module.
3. By lem-sfb-dg-free-module-hom-cohomology, Hom(B,B[k]) is H^k(B), via left
multiplication by cycles. The action of a cycle a in A is multiplication by φ(a).
Consequently the left-action map on H^k(A) is an isomorphism by QuasiIso φ.hom.
Apply lem-sfb-dg-compact-bimodule-full-faithfulness to deduce full faithfulness of L.
4. Restriction leaves the complex unchanged. If R(Y) is zero, all cohomology of Y
vanishes; 0 → Y is a quasi-isomorphism, so Y is zero in the localization.
5. Apply lem-sfb-exact-adjoint-zero-kernel-equivalence to L ⊣ R. Its unit and
counit are isomorphisms, so both functors are equivalences. The exact structures
and compatible shifts from Step 1 give the asserted triangulated equivalence. -/
theorem quasiIso_restriction_equivalence
    (A B : Algebra.{u}) [DerivedStructure A] [DerivedStructure B]
    (φ : A ⟶ B) (hφ : QuasiIso φ.hom) :
    ∃ (N : Bimod A B) (_b : AlgebraMapBimoduleModel φ N)
      (F : RightModule A ⥤ RightModule B) (G : RightModule B ⥤ RightModule A)
      (t : BalancedTensorModel N F) (r : ScalarRestrictionModel φ G)
      (L : Derived A ⥤ Derived B) (R : Derived B ⥤ Derived A)
      (α : Q A ⋙ L ⟶ F ⋙ Q B) (ρ : Q B ⋙ R ≅ G ⋙ Q A)
      (_sL : L.CommShift ℤ) (_sR : R.CommShift ℤ) (adj : L ⊣ R),
      L.IsRightKanExtension α ∧ L.IsTriangulated ∧ R.IsTriangulated ∧
      adj.CommShift ℤ ∧ IsIso adj.unit ∧ IsIso adj.counit ∧
      L.IsEquivalence ∧ R.IsEquivalence ∧
      (∀ (M S : RightModule A) (e : ShiftComparison A 1 M S),
        ∃ eF : ShiftComparison B 1 (F.obj M) (F.obj S),
          IsTensorShift N t 1 M S e eF ∧
          L.map (DerivedStructure.shiftIso 1 M S e).hom ≫
              (Functor.commShiftIso L (1 : ℤ)).hom.app ((Q A).obj M) ≫
                (α.app M)⟦(1 : ℤ)⟧' =
            α.app S ≫ (DerivedStructure.shiftIso 1 (F.obj M) (F.obj S) eF).hom) ∧
      (∀ (Y S : RightModule B) (e : ShiftComparison B 1 Y S),
        ∃ eG : ShiftComparison A 1 (G.obj Y) (G.obj S),
          eG.iso.hom ≫ (r.underlyingIso.hom.app Y)⟦(1 : ℤ)⟧' =
            r.underlyingIso.hom.app S ≫ e.iso.hom ∧
          R.map (DerivedStructure.shiftIso 1 Y S e).hom ≫
              (Functor.commShiftIso R (1 : ℤ)).hom.app ((Q B).obj Y) ≫
                (ρ.hom.app Y)⟦(1 : ℤ)⟧' =
            ρ.hom.app S ≫ (DerivedStructure.shiftIso 1 (G.obj Y) (G.obj S) eG).hom) := by
  sorry

end CategoryTheory.DgAlgebra
