/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.CategoryTheory.RelativeInvariantForgetting
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.CategoryTheory.ProductActionExactForgetting
import Sheaf.CategoryTheory.BoundedBelowDerivedMateModel
import Sheaf.CategoryTheory.RightDerivedSingleH0
import Sheaf.CategoryTheory.CondensedRestrictionMateNormalization
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Normalized relative restriction mates and residual-action forgetting

Source: latest blueprint, six-functors direct-image stability proof, paragraph (3),
agent-extracted relative cyclic calculation; Stacks Tags 09T5, 070J, 070Y and 05SU.
The combined external reference is WANTED in the DAG.
(blueprint: lem-sfb-relative-restriction-mate-forgetting).

The existing `RelativeCyclic.betaNormalization`, `betaDegreeZero`, and `betaShift`
state the computation-unit equation, degree-zero inclusion, and canonical shift law.
`forgetInvariants`, `forgetDerivedExist`, `forgetDerived`, and `forgetDerivedShift`
provide the invariant-inclusion-normalized forgetting isomorphisms and their shift law.
They are reused, not redeclared. The statements below identify beta with the mate,
identify the bounded-below adjunction, record the forgetting square as an equality of
natural transformations, and spell out the last-arrow squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate)

namespace CategoryTheory.RelativeCyclic

variable (A : CondensedBar.Ring.{u}) (G : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

/-- The canonical derived adjunction of normalized projection invariants.
Source: paragraph (3), proof step 1, Stacks 09T5
(blueprint: lem-sfb-relative-restriction-mate-forgetting). -/
abbrev projectionAdjunction :
    (inflate (R := A.toMon) (ContinuousMonoidHom.fst G J)).mapDerivedCategory ⊣
      derived A G J :=
  (invariants A G J).adjunction.mapDerivedCategoryRightDerivedAdjunction

variable {J} {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restriction of a trivial second-factor action, identity on the original modules.
Source: paragraph (3), proof step 2
(blueprint: lem-sfb-relative-restriction-mate-forgetting). -/
def projectionRestriction (v : J →ₜ* H) :
    inflate (R := A.toMon) (ContinuousMonoidHom.fst G J) ≅
      inflate (R := A.toMon) (ContinuousMonoidHom.fst G H) ⋙
        inflate (productMap (G := G) v) :=
  NatIso.ofComponents (fun M ↦
    { hom := ⟨𝟙 M.module, fun _ _ _ ↦ rfl⟩
      inv := ⟨𝟙 M.module, fun _ _ _ ↦ rfl⟩ })

/-- Exact localization of the identity-underlying projection-inflation square.
Source: paragraph (3), proof steps 2--3
(blueprint: lem-sfb-relative-restriction-mate-forgetting). -/
def projectionRestrictionDerived (v : J →ₜ* H) :
    (inflate (R := A.toMon) (ContinuousMonoidHom.fst G J)).mapDerivedCategory ≅
      (inflate (R := A.toMon) (ContinuousMonoidHom.fst G H)).mapDerivedCategory ⋙
        (inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (projectionRestriction A G v) ≪≫
    Functor.mapDerivedCategoryCompIso
      (inflate (R := A.toMon) (ContinuousMonoidHom.fst G H))
      (inflate (productMap (G := G) v))

variable [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The relative restriction arrow is the canonical mate of trivial-inflation restriction.
Source: paragraph (3), Stacks 09T5
(blueprint: lem-sfb-relative-restriction-mate-forgetting).
Proof: step 1 identifies bounded-below and K-injective derived adjunctions by the unique
comparison commuting with computation units, and identifies their counits. In step 2,
the normalized underived transpose is precisely the fixed-section inclusion. Apply
lem-trf-bounded-below-derived-mate-model (step 3); betaNormalization is its computation
unit equation, also when the restricted complex is not injective. The right-derived
universal property identifies beta with the displayed unit-counit mate. Applying H-zero
and lem-kun-right-derived-single-h0 gives the existing betaDegreeZero formula. -/
theorem beta_mate (v : Z.{u} →ₜ* H)
    (N : DerivedCategory.Plus (Equivariant A (G × H))) :
    (beta (A := A) (G := G) v).app N.obj =
      (projectionAdjunction A G Z).unit.app ((derived A G H).obj N.obj) ≫
        (derived A G Z).map ((projectionRestrictionDerived A G v).hom.app
          ((derived A G H).obj N.obj)) ≫
        (derived A G Z).map
          ((inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategory.map
            ((projectionAdjunction A G H).counit.app N.obj)) := by
  sorry

/-- The ambient derived adjunction agrees with the normalized bounded-below adjunction.
This formula is applicable to both H and the discrete integers.
Source: paragraph (3), proof step 1, Stacks 09T5 and 070J
(blueprint: lem-sfb-relative-restriction-mate-forgetting).
Proof: right-derived-plus-injective supplies the unique comparison commuting with units.
On bounded-below injectives both units are invertible; injective resolutions make the
comparison invertible everywhere on D-plus. The underived-counit normalization of
lem-sc-derived-adjunction-from-underived identifies the counits, and the adjunction
triangle identities then identify the units. -/
theorem projectionAdjunction_plus (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K]
    (X : DerivedCategory.Plus (Equivariant A G))
    (Y : DerivedCategory.Plus (Equivariant A (G × K))) :
    DerivedCategory.Plus.ι.map ((invariants A G K).adjunction.derivedPlus.unit.app X) ≫
      (invariants A G K).functor.rightDerivedFunctorPlusCompatibility.hom.app
        ((inflate (R := A.toMon) (ContinuousMonoidHom.fst G K)).mapDerivedCategoryPlus.obj X) ≫
      (derived A G K).map
        ((inflate (R := A.toMon)
          (ContinuousMonoidHom.fst G K)).mapDerivedCategoryPlusCompatibility.hom.app X) =
      (projectionAdjunction A G K).unit.app X.obj ∧
    (inflate (R := A.toMon)
      (ContinuousMonoidHom.fst G K)).mapDerivedCategoryPlusCompatibility.hom.app
        ((invariants A G K).functor.rightDerivedFunctorPlus.obj Y) ≫
      (inflate (R := A.toMon) (ContinuousMonoidHom.fst G K)).mapDerivedCategory.map
        ((invariants A G K).functor.rightDerivedFunctorPlusCompatibility.hom.app Y) ≫
      (projectionAdjunction A G K).counit.app Y.obj =
      DerivedCategory.Plus.ι.map ((invariants A G K).adjunction.derivedPlus.counit.app Y) := by
  sorry

/-- Forgetting the relative mate is scalar restriction as a natural transformation.
Source: paragraph (3), proof steps 4--5, Stacks 070Y
(blueprint: lem-sfb-relative-restriction-mate-forgetting).
Proof: the fixed-section comparisons have identical invariant inclusions. On a
bounded-below injective I precompose both paths with D(U-zero)(alpha at I).
The relative mate equation, forgetDerivedExist and scalar groupMapNormalization turn
both into the scalar computation unit after Q of the same invariant inclusion.
U preserves injectives by lem-sfb-product-action-exact-forgetting, so the source unit
is invertible. Cancel it and use naturality along injective resolutions. This is
forgetBeta componentwise; extensionality gives the stated natural-transformation equality.
No injectivity of the restricted I is assumed. -/
theorem beta_forget_natTrans (v : Z.{u} →ₜ* H) :
    Functor.whiskerRight (beta (A := A) (G := G) v)
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory ≫
      Functor.whiskerLeft
        (inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategory
        (forgetDerived A G (J := Z)).hom =
    (forgetDerived A G (J := H)).hom ≫
      Functor.whiskerLeft (forgetResidual A G H).mapDerivedCategory
        (CondensedDerivedRestriction.groupMap A v) ≫
      Functor.whiskerRight (forgetRestrictionDerived (A := A) (G := G) v).hom
        (CondensedDerivedRestriction.derived A Z) := by
  sorry

/-- The mate respects the triangle boundary with the fixed signed shift comparisons.
Source: paragraph (3), proof steps 6--7, Stacks 05SU
(blueprint: lem-sfb-relative-restriction-mate-forgetting).
Proof: substitute the canonical derived-unit and counit shift identities into the mate
formula to obtain betaShift. Naturality at T.mor-three followed by that shift equation
is exactly the displayed last-arrow square; naturality supplies the first two squares.
Both image triangles are distinguished because all functors are triangulated. -/
theorem beta_boundary (v : Z.{u} →ₜ* H)
    (T : Triangle (DerivedCategory.{u + 1} (Equivariant A (G × H))))
    (_hT : T ∈ distTriang (DerivedCategory.{u + 1} (Equivariant A (G × H)))) :
    (derived A G H).map T.mor₃ ≫
        ((derived A G H).commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫
        (shiftFunctor (DerivedCategory.{u + 1} (Equivariant A G)) (1 : ℤ)).map
          ((beta (A := A) (G := G) v).app T.obj₁) =
      (beta (A := A) (G := G) v).app T.obj₃ ≫
        ((inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategory ⋙
          derived A G Z).map T.mor₃ ≫
        (((inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategory ⋙
          derived A G Z).commShiftIso (1 : ℤ)).hom.app T.obj₁ := by
  sorry

/-- The normalized forgetting isomorphisms respect the triangle boundary.
Source: paragraph (3), proof steps 4, 6--7, Stacks 05SU
(blueprint: lem-sfb-relative-restriction-mate-forgetting).
Proof: on common injective models the comparison is the identity on fixed sections,
normalized by the two computation units (forgetDerivedExist). Substitute canonical
unit and counit shift identities to obtain forgetDerivedShift. Apply naturality at
the triangle boundary and then this shift identity. This proves the last-arrow square,
while ordinary naturality proves the other two squares. -/
theorem forgetDerived_boundary
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (T : Triangle (DerivedCategory.{u + 1} (Equivariant A (G × K))))
    (_hT : T ∈ distTriang (DerivedCategory.{u + 1} (Equivariant A (G × K)))) :
    (derived A G K ⋙
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory).map T.mor₃ ≫
      ((derived A G K ⋙
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory).commShiftIso
          (1 : ℤ)).hom.app T.obj₁ ≫
      (shiftFunctor (DerivedCategory.{u + 1} (Modules A)) (1 : ℤ)).map
        ((forgetDerived A G (J := K)).hom.app T.obj₁) =
    (forgetDerived A G (J := K)).hom.app T.obj₃ ≫
      ((forgetResidual A G K).mapDerivedCategory ⋙
        CondensedDerivedRestriction.derived A K).map T.mor₃ ≫
      (((forgetResidual A G K).mapDerivedCategory ⋙
        CondensedDerivedRestriction.derived A K).commShiftIso (1 : ℤ)).hom.app T.obj₁ := by
  sorry

end CategoryTheory.RelativeCyclic
