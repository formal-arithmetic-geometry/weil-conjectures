/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose

/-! # Canonical top cohomology of derived module pullback

Source: Stacks Project, derived.tex, Tag 05TC (dual upper-bound and truncation argument),
cohomology.tex, Tags 06YJ and 0D5S. Naturality and composition are the agent assembly
specified in the DAG (blueprint: lem-weil-pbc-derived-pullback-top-cohomology).

The comparison in degree n is the selected derived counit evaluated at the single
complex in degree n. The pinned counit shift theorem identifies it with c[-n].
The top projection is fixed by its identity action on cohomology, using the existing
bijection on maps from D^{≤n} to D^{≥n}; thus it is the standard truncation projection.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w uA uB vA vB wA wB
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback

/-- The canonical projection C → H^n(C)[-n], characterized by identity on H^n.
The inverse below is the existing bijection of Hom sets. This construction works in
any abelian category and uses its existing standard truncation interface.
Source: Stacks, derived.tex, Tags 08J5 and 05TC
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology). -/
def derivedTopTruncationProjection
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (n : ℤ) (C : DerivedCategory A) (hC : C.IsLE n) :
    C ⟶ (DerivedCategory.singleFunctor A n).obj ((DerivedCategory.homologyFunctor A n).obj C) :=
  letI := hC
  (Equiv.ofBijective _
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n)).symm
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso A n).inv.app
        ((DerivedCategory.homologyFunctor A n).obj C))

/-- Evaluate a specified derived counit on a single module and apply the canonical
termwise/single identification. This generic construction avoids expanding the concrete
sheafification data when checking each use of the same pinned comparison.
Source: Stacks, cohomology.tex, Tags 06YJ and 08HY
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology). -/
def derivedSingleComparisonOfCounit
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (n : ℤ) (M : A) :
    LF.obj ((DerivedCategory.singleFunctor A n).obj M) ⟶
      (DerivedCategory.singleFunctor B n).obj (F.obj M) :=
  ε.app ((HomotopyCategory.singleFunctor A n).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app M))

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The pinned derived-to-tensor-pullback comparison on a single module in degree n.
For n=0 this is the specified counit representative of
`IsDerivedModulePullbackComparison`, normalized by the ordinary pullback unit.
For general n it is the shifted comparison, by pinned counit shift compatibility.
Source: Stacks, cohomology.tex, Tags 06YJ, 08HY and 0D5S
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology). -/
def pinnedModulePullbackComparisonAt {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (M : S.Modules) :
    (derivedPullback g).obj ((DerivedCategory.singleFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj M) ⟶
    (DerivedCategory.singleFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj
        ((Scheme.Modules.tensorPullback g).obj M) :=
  letI : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive :=
    fun f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f
  derivedSingleComparisonOfCounit
    (A := SheafOfModules.{u} (moduleRings S.toRingedSpace))
    (B := SheafOfModules.{u} (moduleRings T.toRingedSpace))
    (Scheme.Modules.tensorPullback g) (derivedPullback g) (pinnedPullbackCounit.{u, w} g) n M

/-- The specified κ: apply derived pullback to the top projection, apply the pinned
comparison on H^n(C)[-n], take H^n, and use the canonical single-complex cohomology iso.
Source: Stacks, derived.tex, Tag 05TC, dual truncation argument; cohomology.tex, Tag 06YJ
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology). -/
def derivedPullbackTopCohomology {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE n) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj
        ((derivedPullback g).obj C) ⟶
    (Scheme.Modules.tensorPullback g).obj ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C) :=
  (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map
      ((derivedPullback g).map (derivedTopTruncationProjection n C hC)) ≫
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map
      (pinnedModulePullbackComparisonAt g n ((DerivedCategory.homologyFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C)) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).hom.app _

/-- Derived pullback preserves the upper bound; H^0 of its normalized module comparison
and the specified top comparison are isomorphisms. The top comparison is natural for
all derived morphisms between upper-bounded objects and respects composition.
The existential `hbound` records the first conclusion and supplies its proof to κ_h.
Source: Stacks, derived.tex, Tags 05TC and 08J5, dual upper-bound/truncation argument;
cohomology.tex, Tags 06YJ and 0D5S. Naturality and composition are the DAG assembly
(blueprint: lem-weil-pbc-derived-pullback-top-cohomology).

Proof:
1. Represent C by a complex K zero above n using the standard t-structure. Apply
lem-pc-kflat-bounded-flat-replacement at the same bound n. Its flat replacement P is
K-flat by lem-pc-bounded-above-flat-kflat, so def-pc-derived-pullback computes Lg*C by
termwise g*P, with the counit selected by derived pullback composition.
2. The ordinary tensor pullback is left adjoint to pushforward
(lem-pc-module-pullback-adjunction), hence preserves cokernels. Its comparison
coker(g*d^{n-1}) → g*coker(d^{n-1}) is the map induced by the quotient of g*P^n.
3. The pulled-back complex is zero above n; its top cohomology is that cokernel.
Thus Lg*C has the asserted upper bound, without a lower bound.
4. Resolve M[0] with the same upper bound zero. Naturality of the fixed derived
counit at the resolution map identifies H^0(c_g,M) with the invertible cokernel
comparison followed by g* of the resolution's H^0 isomorphism. This verifies the
particular comparison of def-pc-derived-module-base-change-map.
5. On P the top projection has degree-n component P^n → H^n(P). Counit naturality
at this map and lem-pc-pinned-pullback-counit-shifts identify κ with the cokernel
isomorphism of step 3. Transport along Q(P) ≅ C gives the stated κ.
6. Smart truncation is functorial and preserves quasi-isomorphisms; it descends to
all derived morphisms. Its projection and the selected counit are natural, giving
the displayed naturality equation. On a single module in degree n, κ is H^0(c).
7. Apply lem-pc-canonical-single-pullback-composition to h,g,M. The explicit pinned
construction of lem-pc-canonical-single-pullback-comparison and the transpose formula
lem-pc-canonical-single-adjunction-transpose identify its single comparisons with c.
Transport the ordinary comparisons back through the unique adjunction-preserving
tensor-to-ordinary identifications. This gives the same equation with tensor pullback
and tensorPullbackSectionComp.inv. Shift it using the two pinned shift lemmas.
8. Apply step 6 for h to v = Lg*(τ_C) followed by c_g,H^n(C)[-n]. Its H^n is κ_g,C.
The target is the single g*H^n(C) in degree n, so its κ_h is H^0(c_h). Postcompose
with ordinary tensor composition; substitute step 7 and use naturality of derived
composition at τ_C. This gives exactly the displayed composition equation.
No inverse of c in the derived category is used. -/
theorem derivedPullback_topCohomology {T S : Scheme.{u}} (g : T ⟶ S)
    (n : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE n) :
    ∃ hbound : ((derivedPullback g).obj C).IsLE n,
      (∀ M : S.Modules,
        IsIso ((DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map
            (pinnedModulePullbackComparisonAt g 0 M))) ∧
      IsIso (derivedPullbackTopCohomology g n C hC) ∧
      (∀ (D : schemeDerivedCategory S) (hD : D.IsLE n) (a : C ⟶ D),
        (DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).map ((derivedPullback g).map a) ≫
            derivedPullbackTopCohomology g n D hD =
          derivedPullbackTopCohomology g n C hC ≫
            (Scheme.Modules.tensorPullback g).map ((DerivedCategory.homologyFunctor.{w, u, u + 1}
              (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).map a)) ∧
      (∀ (T' : Scheme.{u}) (h : T' ⟶ T),
        (DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) n).map
            ((@pinnedPullbackComposition.{u, w} _
              (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f)
              _ _ _ h g).hom.app C) ≫
            derivedPullbackTopCohomology (h ≫ g) n C hC =
          derivedPullbackTopCohomology h n ((derivedPullback g).obj C) hbound ≫
            (Scheme.Modules.tensorPullback h).map (derivedPullbackTopCohomology g n C hC) ≫
            (Scheme.Modules.tensorPullbackSectionComp h g).inv.app
              ((DerivedCategory.homologyFunctor.{w, u, u + 1}
                (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj C)) := by
  sorry

end AlgebraicGeometry
