/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.CategoryTheory.TruncationCouple
import Sheaf.CategoryTheory.TruncationTriangle

/-! # Naturality of the raw truncation maps

Source: Stacks Project, Remark 08J5 and Tags 015J, 05TC.
(blueprint: lem-pc-raw-truncation-couple-naturality).
-/

@[expose] public section

universe v uA uB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TruncationCouple

variable {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
  [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- The degree-n canonical truncation inclusion, after RF and the inverse bridge.
Source: Stacks Tag 05TC (2) (blueprint: lem-pc-raw-truncation-couple-naturality). -/
noncomputable def abutmentMap (K : CochainComplex.Plus A) (n : ℤ) :
    D F K 0 n ⟶ (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj
      (DerivedCategory.Q.obj K.obj) :=
  eqToHom (by unfold D; rw [zero_add]) ≫
    (bridgeIso F (truncation K n) n).inv ≫
    (DerivedCategory.homologyFunctor B n).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE n)))

/-- The first shift comparison, without comparison to ordinary right derived functors.
Source: Stacks Tags 015J, 05TC (blueprint: lem-pc-raw-truncation-couple-naturality). -/
noncomputable def singleIso (K : CochainComplex.Plus A) (p q : ℤ) :
    E F K p q ≅
      (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor B p).obj (K.obj.homology q) :=
  (bridgeIso F (cohomologyComplex K q) (p + q)).symm ≪≫
    (DerivedCategory.homologyFunctor B (p + q)).mapIso
      (F.rightDerivedFunctor.mapIso
        (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0
          (by omega)).app (K.obj.homology q)).symm) ≪≫
    (DerivedCategory.homologyFunctor B (p + q)).mapIso
      ((F.rightDerivedFunctor.commShiftIso (-q)).app
        ((DerivedCategory.singleFunctor A 0).obj (K.obj.homology q))) ≪≫
    ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) (p + q) p
      (by omega)).app
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj (K.obj.homology q)))

/-- Transport derived cohomology of a map to cohomology of its representing complexes.
Source: derived localization, Stacks Tag 05S7
(blueprint: lem-pc-raw-truncation-couple-naturality). -/
noncomputable def homologyMap {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (q : ℤ) :
    K.obj.homology q ⟶ N.obj.homology q :=
  ((DerivedCategory.homologyFunctorFactors A q).app K.obj).inv ≫
    (DerivedCategory.homologyFunctor A q).map c ≫
    ((DerivedCategory.homologyFunctorFactors A q).app N.obj).hom

/-- Naturality of the raw maps, the canonical abutment inclusion and the first
shift comparison. This concerns two fixed complexes and a single derived morphism;
no exactness, lower bound, choice of representatives, or invertibility of abutment
maps is asserted.

Source: Stacks Project, Remark 08J5, with Tags 015J and 05TC; step 4 of
lem-pc-natural-bounded-below-truncation-couples.
(blueprint: lem-pc-raw-truncation-couple-naturality).

Proof:
1. Descend the functors tau<=q and H^q(-)[-q] along Q. On the two complexes,
conjugate the descended maps by Localization.fac. Apply the triangulated RF,
homology in degree p+q, and the bridge isomorphisms to define tD and tE.
2. The three squares of truncation_triangle give the alpha, projection and
boundary squares. For the boundary square use naturality of the connecting
morphism in the homology sequence of the mapped triangle. Bridge factors
cancel; the equality transports preserve total degrees, giving the three raw
squares below.
3. Descending the natural transformation tau<=n -> identity gives its square
for every derived morphism. Apply RF and H^n and cancel the bridge factors;
this is the abutment equation.
4. The single-functor shift comparison, RF commutation with shifts, and homology
shift comparison are natural isomorphisms. Their composite singleIso is therefore
natural. The homologyFunctorFactors comparison identifies the descended H^q map
with homologyMap; cancellation of the bridge yields the final equation.
The zero map and zero objects satisfy the same equations. No representative map
of complexes is needed, so arbitrary roofs in D(A) are covered. -/
theorem raw_naturality (K N : CochainComplex.Plus A)
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) :
    ∃ (tD : ∀ p q : ℤ, D F K p q ⟶ D F N p q)
      (tE : ∀ p q : ℤ, E F K p q ⟶ E F N p q),
      (∀ p q : ℤ, tD p q ≫ alpha F N p q =
        alpha F K p q ≫ tD (p - 1) (q + 1)) ∧
      (∀ p q : ℤ, tE p q ≫ f F N p q = f F K p q ≫ tD (p + 2) (q - 1)) ∧
      (∀ p q : ℤ, tD p q ≫ g F N p q = g F K p q ≫ tE p q) ∧
      (∀ n : ℤ, tD 0 n ≫ abutmentMap F N n = abutmentMap F K n ≫
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map c) ∧
      (∀ p q : ℤ, tE p q ≫ (singleIso F N p q).hom = (singleIso F K p q).hom ≫
        (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B p).map (homologyMap c q)) := by sorry

end CategoryTheory.TruncationCouple
