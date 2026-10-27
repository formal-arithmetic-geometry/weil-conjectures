/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedInvariants
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Normalization of the derived group-restriction mate

Source: main-20261015, direct-images proof, paragraph (3), dense-lattice input,
restriction-calculus steps 4 and 5
(blueprint: lem-sfb-condensed-restriction-mate-normalization).
The auxiliary statement is agent-formulated; its external reference is wanted.
The normalized invariant inclusions and every derived functor are the recorded constructions.

## Main statements

* `groupMap_mate`: the mate formula and its transpose.
* `groupMap_mate_plus_adjunction`: normalized restriction of the derived adjunction.
* `groupMap_mate_resolutions`: computation using two injective resolutions.
* `groupMap_mate_triangles`: compatibility including the connecting arrow.

The computation-unit and shift clauses are the existing `groupMapNormalization` and
`groupMapShift` of the imported dependency `Sheaf.CategoryTheory.CondensedDerivedInvariants`.
The degree-zero and identity clauses are stated word for word as `restrictionDegreeZero` and
`identityRestriction` in `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`, the
module of the node lem-sfb-condensed-derived-restriction-calculus, which lists this node as
a proof dependency. They are not redeclared here, and that module is not imported here, so
that it can import this one for its proofs without an import cycle. Their proofs are the
node's steps 7 and 8: (7) invariants are left exact by the fixed-section formula; the
degree-zero injective-resolution lemma identifies `H⁰(alpha)` with the augmentation; apply
`H⁰` to the computation-unit equation at `M[0]` and cancel. (8) For the identity map the
mate reduces to `eta; F(epsilon) = id`, the adjunction triangle identity.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Profinite.CondensedAction (inflate trivial)
open CategoryTheory.CondensedBar

namespace CategoryTheory.CondensedDerivedRestriction

variable (A : CondensedBar.Ring.{u})
variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The trivial-action comparison is identity on the original internal modules.
Source: paragraph (3), proof step 1
(blueprint: lem-sfb-condensed-restriction-mate-normalization). -/
def restrictionTrivial (v : H →ₜ* G) :
    trivial (R := A.toMon) (P := H) ≅ trivial (R := A.toMon) (P := G) ⋙ inflate v :=
  NatIso.ofComponents (fun M ↦
    { hom := ⟨𝟙 M, fun _ _ _ ↦ rfl⟩
      inv := ⟨𝟙 M, fun _ _ _ ↦ rfl⟩ })

/-- The exact-localization comparison between restricted trivial inflation and trivial
inflation. Source: paragraph (3), proof step 1
(blueprint: lem-sfb-condensed-restriction-mate-normalization). -/
def restrictionTrivialDerived (v : H →ₜ* G) :
    trivialDerived A H ≅ trivialDerived A G ⋙ groupDerived A v :=
  Functor.mapDerivedCategoryNatIso (restrictionTrivial A v) ≪≫
    Functor.mapDerivedCategoryCompIso (trivial (R := A.toMon) (P := G)) (inflate v)

/-- The canonical restriction map is the adjunction mate, and its inverse transpose is the
restricted counit, with the exact-localization comparison inserted.
Source: paragraph (3) (blueprint: lem-sfb-condensed-restriction-mate-normalization).
Proof: (1) both underived transposes are the same inclusion on every section.
(2) resolve a complex by a K-injective and apply resolving-adjunction normalization
[lem-sfb-resolving-derived-adjunction-normalization] to obtain
`L(alpha); epsilon = Q(e)`; cancel the localized resolution.
(3) transpose the computation-unit equation, use (1) and (2), then the total-derived
universal property [def-sfb-right-derived-functor]. This identifies the map with the mate.
No preservation of injectives by restriction is needed. -/
theorem groupMap_mate (v : H →ₜ* G)
    (N : DerivedCategory.{u + 1} (Equivariant A G)) :
    (groupMap A v).app N =
      (adjunction A H).unit.app ((derived A G).obj N) ≫
        (derived A H).map ((restrictionTrivialDerived A v).hom.app
          ((derived A G).obj N)) ≫
        (derived A H).map ((groupDerived A v).map ((adjunction A G).counit.app N)) ∧
    ((adjunction A H).homEquiv ((derived A G).obj N) ((groupDerived A v).obj N)).symm
        ((groupMap A v).app N) =
      (restrictionTrivialDerived A v).hom.app ((derived A G).obj N) ≫
        (groupDerived A v).map ((adjunction A G).counit.app N) := by
  sorry

/-- Preservation of bounded-below objects and the computation-unit normalization of the
canonical unbounded/bounded-below comparison, for either group.
Source: paragraph (3) (blueprint: lem-sfb-condensed-restriction-mate-normalization).
Proof: apply [lem-sfb-additive-derived-plus-unit-normalization] to the additive invariant
functor; the action category is Grothendieck abelian by the injective infrastructure.
The comparison is the unique isomorphism commuting with the two units (proof step 4). -/
theorem groupMap_mate_plus (K : DerivedCategory.Plus (Equivariant A G)) :
    (∃ n : ℤ, ((derived A G).obj K.obj).IsGE n) ∧
    (∀ P : HomotopyCategory.Plus (Equivariant A G),
      (invariants A G).functor.rightDerivedFunctorPlusιUnit.app P ≫
        (invariants A G).functor.rightDerivedFunctorPlusCompatibility.hom.app
          (DerivedCategory.Plus.Qh.obj P) =
      (invariants A G).functor.ιRightDerivedFunctorUnit.app P) := by
  sorry

/-- The restricted derived adjunction is the canonical bounded-below derived adjunction:
both the unit and counit agree under the exact and right-derived comparisons.
Source: paragraph (3) (blueprint: lem-sfb-condensed-restriction-mate-normalization).
Proof: bounded-below categories are full and both adjoints preserve them (step 4).
Restrict the ambient Hom bijection. Computation-unit normalization (step 2) gives the
bounded-below derived Hom bijection and hence its specified unit and counit. -/
theorem groupMap_mate_plus_adjunction
    (X : DerivedCategory.Plus (Modules A))
    (Y : DerivedCategory.Plus (Equivariant A G)) :
    DerivedCategory.Plus.ι.map ((invariants A G).adjunction.derivedPlus.unit.app X) ≫
      (invariants A G).functor.rightDerivedFunctorPlusCompatibility.hom.app
        ((trivial (R := A.toMon) (P := G)).mapDerivedCategoryPlus.obj X) ≫
      (derived A G).map
        ((trivial (R := A.toMon) (P := G)).mapDerivedCategoryPlusCompatibility.hom.app X) =
      (adjunction A G).unit.app X.obj ∧
    (trivial (R := A.toMon) (P := G)).mapDerivedCategoryPlusCompatibility.hom.app
        ((invariants A G).functor.rightDerivedFunctorPlus.obj Y) ≫
      (trivialDerived A G).map
        ((invariants A G).functor.rightDerivedFunctorPlusCompatibility.hom.app Y) ≫
      (adjunction A G).counit.app Y.obj =
      DerivedCategory.Plus.ι.map ((invariants A G).adjunction.derivedPlus.counit.app Y) := by
  sorry

/-- At bounded-below injective complexes the computation unit is invertible, and the
counit is the class of the termwise ordinary counit under that unit.
Source: paragraph (3) (blueprint: lem-sfb-condensed-restriction-mate-normalization).
Proof: bounded-below injectives are K-injective [lem-sfb-condensed-action-injective-
infrastructure]. Step 2 gives the counit equation; step 4 identifies it with the
bounded-below counit through the normalized comparison. -/
theorem groupMap_mate_injective_counit (I : CochainComplex (Equivariant A G) ℤ)
    (n : ℤ) [I.IsStrictlyGE n] [∀ i : ℤ, Injective (I.X i)] :
    IsIso ((invariants A G).functor.rightDerivedFunctorUnitQ I) ∧
    (trivialDerived A G).map ((invariants A G).functor.rightDerivedFunctorUnitQ I) ≫
      (adjunction A G).counit.app (DerivedCategory.Q.obj I) =
    (trivial (R := A.toMon) (P := G)).mapDerivedCategoryFactors.hom.app
        (((invariants A G).functor.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (invariants A G).adjunction.counit (.up ℤ)).app I)
      := by
  sorry

/-- Two bounded-below injective resolutions compute restriction by the actual fixed-section
inclusion followed by the map to the second resolution. The displayed square expresses
this representation using the specified computation units, without choosing another
comparison. Source: paragraph (3)
(blueprint: lem-sfb-condensed-restriction-mate-normalization).
Proof: apply step 3 to I, use naturality of the target computation unit along t and
naturality of b along s. Both units are invertible on bounded-below injectives; cancel
those units and the quasi-isomorphism s. This is proof step 5. -/
theorem groupMap_mate_resolutions (v : H →ₜ* G)
    (P I : CochainComplex (Equivariant A G) ℤ)
    (I' : CochainComplex (Equivariant A H) ℤ)
    (n m k : ℤ) [P.IsStrictlyGE n] [I.IsStrictlyGE m] [I'.IsStrictlyGE k]
    [∀ i : ℤ, Injective (I.X i)] [∀ i : ℤ, Injective (I'.X i)]
    (s : P ⟶ I) [QuasiIso s]
    (t : ((inflate v).mapHomologicalComplex (.up ℤ)).obj I ⟶ I') [QuasiIso t] :
    IsIso ((invariants A G).functor.rightDerivedFunctorUnitQ I) ∧
    IsIso ((invariants A H).functor.rightDerivedFunctorUnitQ I') ∧
    (invariants A G).functor.rightDerivedFunctorUnitQ I ≫
      inv ((derived A G).map (DerivedCategory.Q.map s)) ≫
      (groupMap A v).app (DerivedCategory.Q.obj P) ≫
      (derived A H).map
        ((groupDerived A v).map (DerivedCategory.Q.map s) ≫
          (inflate v).mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map t) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex
        (invariantRestriction (invariants A G) (invariants A H) v) (.up ℤ)).app I) ≫
      DerivedCategory.Q.map (((invariants A H).functor.mapHomologicalComplex (.up ℤ)).map t) ≫
      (invariants A H).functor.rightDerivedFunctorUnitQ I' := by
  sorry

/-- All three squares of the image triangles commute, including the connecting arrow
with the canonical shift comparisons.
Source: paragraph (3) (blueprint: lem-sfb-condensed-restriction-mate-normalization).
Proof: naturality gives the first two squares. Naturality at the last arrow followed
by the shift equation gives the last square, as in proof step 6. -/
theorem groupMap_mate_triangles (v : H →ₜ* G)
    (T : Triangle (DerivedCategory.{u + 1} (Equivariant A G)))
    (_hT : T ∈ distTriang (DerivedCategory.{u + 1} (Equivariant A G))) :
    (derived A G).map T.mor₁ ≫ (groupMap A v).app T.obj₂ =
      (groupMap A v).app T.obj₁ ≫ (groupDerived A v ⋙ derived A H).map T.mor₁ ∧
    (derived A G).map T.mor₂ ≫ (groupMap A v).app T.obj₃ =
      (groupMap A v).app T.obj₂ ≫ (groupDerived A v ⋙ derived A H).map T.mor₂ ∧
    (derived A G).map T.mor₃ ≫ ((derived A G).commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫
        (shiftFunctor (DerivedCategory.{u + 1} (Modules A)) (1 : ℤ)).map
          ((groupMap A v).app T.obj₁) =
      (groupMap A v).app T.obj₃ ≫ (groupDerived A v ⋙ derived A H).map T.mor₃ ≫
        ((groupDerived A v ⋙ derived A H).commShiftIso (1 : ℤ)).hom.app T.obj₁ := by
  sorry

end CategoryTheory.CondensedDerivedRestriction
