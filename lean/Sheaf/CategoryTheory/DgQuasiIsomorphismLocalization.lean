/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.DgAlgebraHomotopyStructure
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Sheaf.CategoryTheory.DgHomotopyAcyclicLocalization
import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Compatible localization of the homotopy category of right dg modules

Source: Stacks Project, dga.tex, Tags 09KJ, 09KW, 09KX; derived.tex,
Tags 05RG, 05R2, 05R6; Mathlib's unsigned opposite triangulation
(blueprint: lem-sfb-dg-quasi-isomorphism-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uE vE

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory.DgAlgebra

/-- The quasi-isomorphisms in the actual dg homotopy quotient: every induced
cohomology map is invertible. Cohomology is the factorization of the underlying
complex's kernel modulo image, as specified by `HomotopyStructure.cohomology_factors`.
Source: Stacks, dga.tex, Tag 09KW
(blueprint: lem-sfb-dg-quasi-isomorphism-localization). -/
def homotopyQuasiIsomorphisms (A : Algebra.{u}) [HomotopyStructure A] :
    MorphismProperty (HomotopyCategory A) :=
  fun _ _ f ↦ ∀ n : ℤ, IsIso ((HomotopyStructure.cohomology n).map f)

/-- Quasi-isomorphisms of arbitrary right dg modules form a saturated compatible
multiplicative system, in both the homotopy category and its unsigned opposite.
The derived category here is the existing actual localization `Derived A`.
All triangulation data and the induced homotopy localization functor are conclusions;
no triangulation, boundedness or commutativity assumption is made on the dg algebra.
The equation with `Q A` fixes the functor on the homotopy quotient canonically.
Distinguished triangles in the target are exactly the localized cone triangles.
Target universes in the strict universal properties are arbitrary.

Source: Stacks, dga.tex, Tags 09KJ, 09KW, 09KX; derived.tex, Tags 05RG,
05R2 and 05R6; Mathlib opposite triangulation and localization
(blueprint: lem-sfb-dg-quasi-isomorphism-localization).

Proof plan, following the nine steps of the node:
1. Apply lem-sfb-dg-homotopy-acyclic-localization. Degree-zero Hom cocycles are
chain maps and boundaries are dh+hd, so its quotient is H^0 of the dg Hom complex.
It gives the standard cone triangulation and identifies the acyclic cone class.
Homotopic maps induce identical cohomology maps because their difference on cycles
is a boundary; composition and identities descend.
2. Apply lem-trf-triangulated-subcategory-cone-system to the acyclic subcategory.
This gives MS1--MS3, both fraction calculi, shift invariance and MS6, without any
closure-under-retracts assumption.
3. For h,g,f with gh and fg quasi-isomorphisms, H(g) has right inverse
H(h)(H(g)H(h)) inverse and left inverse (H(f)H(g)) inverse H(f). A left and right
inverse coincide. This proves MS4; functoriality similarly proves two-out-of-three.
4. Use lem-weil-pbc-localization-universal-property and the homotopy quotient to
factor the existing Q canonically through K. The cylinder homotopy identifies
homotopic maps after Q. The quotient and localization universal properties show
that this induced functor is a strict localization, including natural transformations.
Apply lem-pur-localization-triangles-05r6 to transport the localized triangulation
to the fixed category Derived A. Its triangles are exactly images of cone triangles.
5. An acyclic object's arrow from zero is a quasi-isomorphism, so its image is zero.
Conversely each cohomology functor factors through localization. If the image of M
is zero, apply these factors to its isomorphism with the image of zero to obtain
vanishing of every H^n(M). This gives precisely the stated kernel.
6. Apply lem-sfb-opposite-triangulated-category to K and D. The opposite shift
is the original negative shift and opposite triangles have no additional sign.
Apply lem-sf-triangulated-functor-opposite to the localization functor.
7. Reversing arrows exchanges the left and right MS2 and MS3 diagrams and
preserves MS1 and MS4. Invariance under all integer shifts supplies opposite MS5.
8. For opposite MS6, unop a square on the first two objects to a square on the
last two original objects. Rotate the original triangles, apply MS6, then shift
back by minus one. The two rotation signs cancel. The resulting third map remains
a quasi-isomorphism by shift invariance, giving the unsigned opposite completion.
9. Reverse any functor out of K opposite to one from K into the opposite target.
Factor uniquely through D, then reverse back. Do the same with natural
transformations, reversing their direction twice. These mutually inverse operations
give the strict opposite universal property on functors and transformations. -/
theorem quasi_isomorphism_localization (A : Algebra.{u}) :
    ∃ (_s : HomotopyStructure A) (_t : IsTriangulated (HomotopyCategory A))
      (_pD : Preadditive (Derived A)) (_zD : HasZeroObject (Derived A))
      (_sD : HasShift (Derived A) ℤ)
      (_aD : ∀ n : ℤ, (shiftFunctor (Derived A) n).Additive)
      (_pT : Pretriangulated (Derived A)) (_tD : IsTriangulated (Derived A))
      (Qh : HomotopyCategory A ⥤ Derived A)
      (_aQ : Qh.Additive) (_sQ : Qh.CommShift ℤ),
      homotopyQuotient A ⋙ Qh = Q A ∧
      (homotopyQuasiIsomorphisms A).IsSaturatedTriangulatedMultiplicativeSystem ∧
      (homotopyQuasiIsomorphisms A).HasLeftCalculusOfFractions ∧
      (homotopyQuasiIsomorphisms A).HasRightCalculusOfFractions ∧
      (homotopyQuasiIsomorphisms A).HasTwoOutOfThreeProperty ∧
      Qh.IsStrictLocalizationAt.{u + 1, u, u + 1, u + 1, uE, vE}
        (homotopyQuasiIsomorphisms A) ∧
      Qh.IsTriangulated ∧
      (∀ T : Triangle (Derived A),
        T ∈ distTriang (Derived A) ↔ T ∈ Qh.essImageDistTriang) ∧
      (∀ M : HomotopyCategory A,
        IsZero (Qh.obj M) ↔
          ∀ n : ℤ, IsZero ((HomotopyStructure.cohomology n).obj M)) ∧
      IsTriangulated (HomotopyCategory A)ᵒᵖ ∧ IsTriangulated (Derived A)ᵒᵖ ∧
      (homotopyQuasiIsomorphisms A).op.IsSaturatedTriangulatedMultiplicativeSystem ∧
      Qh.op.IsStrictLocalizationAt.{u + 1, u, u + 1, u + 1, uE, vE}
        (homotopyQuasiIsomorphisms A).op ∧
      Qh.op.IsTriangulated := by
  sorry

end CategoryTheory.DgAlgebra
