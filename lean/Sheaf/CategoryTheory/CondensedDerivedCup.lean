/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.CondensedActionTensor
public import Sheaf.CategoryTheory.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Canonical derived cup product of condensed internal invariants

Source: main-20261015 direct-images proof (sk-thm-sf-ctf-stability-direct-images.proof.md),
paragraph (3), agent-formulated formal restriction and cup-product infrastructure;
exact reference wanted; Stacks 07A4 for the localized unit
(blueprint: def-sfb-condensed-derived-cup).

## Main definitions

* `derivedTrivialTensor`: the strong derived tensor comparison of trivial inflation, fixed by
  the flat-term K-flat normalization of lem-derived-right-exact-tensor-comparison and the
  localized regular unit.
* `derivedLax`: the lax structure on derived invariants, the mate of the tensor of counits.
* `coefficient`, `cohomology`, `cup`, `cupUnit`: C_R(J) = RΓ(R[0]) with its cup algebra.
* `groupCupMap`, `tensorPower`, `tensorPowerMap`, `orderedProduct`: restriction on C_R(J) and
  ordered iterated products.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction (inflate trivial)
open CategoryTheory.CondensedBar
namespace CategoryTheory.CondensedDerivedRestriction
variable {A A' : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

section LocalizationUnit
variable {C : Type v} [Category.{w} C] [Abelian C]
  [HasDerivedCategory.{w} C] [IsGrothendieckAbelian.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]

/-- The localized regular unit, using the existing generic Qh-unit comparison.
Source: Stacks 07A4; DerivedCategory.isIso_ε_Qh
(blueprint: def-sfb-condensed-derived-cup). -/
def localizedUnit : 𝟙_ (DerivedCategory.{w} C) ≅
    (DerivedCategory.singleFunctor C 0).obj (𝟙_ C) :=
  @asIso _ _ _ _ (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := C)))
    (DerivedCategory.isIso_ε_Qh C)

end LocalizationUnit

/-- The regular module R in degree zero is the actual derived tensor unit.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def baseUnitIso (A : CondensedBar.Ring.{u}) :
    𝟙_ (DerivedCategory.{u + 1} (Modules A)) ≅
      (DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X) :=
  localizedUnit (C := Modules A)

/-- The trivial coefficient object, with the actual regular module in degree zero.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def coefficient (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : DerivedCategory.{u + 1} (Equivariant A G) :=
  (DerivedCategory.singleFunctor (Equivariant A G) 0).obj
    ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X))

/-- The canonical regular-unit identification, localized from the actual ordinary unit.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def canonicalActionUnit : 𝟙_ (DerivedCategory.{u + 1} (Equivariant A G)) ≅ coefficient A G :=
  localizedUnit (C := Equivariant A G) ≪≫
    (DerivedCategory.singleFunctor (Equivariant A G) 0).mapIso (trivialTensor A G).core.εIso

/-- Trivial action is a left adjoint with its specified invariant-submodule right adjoint.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
instance trivialLeftAdjoint : (trivial (R := A.toMon) (P := G)).IsLeftAdjoint :=
  (invariants A G).adjunction.isLeftAdjoint

/-- Trivial action carries flat modules to flat action modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup).
Proof: the underlying tensor with a trivial flat module is the flat ordinary module
tensor, and forgetting the action detects exactness. -/
@[instance] theorem trivialFlat : (trivial (R := A.toMon) (P := G)).PreservesFlat := by
  sorry


section ExactTensorNormalization
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]

/-- The existing K-flat model predicate for an exact strong tensor functor.
Source: Stacks 06YY and 07A4
(blueprint: def-sfb-condensed-derived-cup). -/
def exactTensorNormalization (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.IsLeftAdjoint]
    [F.OplaxMonoidal] (core : F.mapDerivedCategory.CoreMonoidal) : Prop :=
  Functor.rightExactTensorModelNormalization F F.mapDerivedCategory
    (fun P => F.mapDerivedCategoryFactors.hom.app P) (fun K L => core.μIso K L)

end ExactTensorNormalization

/-- The existing generic K-flat tensor normalization, specialized to exact trivial action.
Source: paragraph (3), Stacks 06YY and 07A4
(blueprint: def-sfb-condensed-derived-cup). -/
def TrivialTensorModel (core : (trivialDerived A G).CoreMonoidal) : Prop :=
  exactTensorNormalization (trivial (R := A.toMon) (P := G)) core

/-- The unit comparison is the localized ordinary regular-unit comparison.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def TrivialUnitModel (core : (trivialDerived A G).CoreMonoidal) : Prop :=
  core.εIso.hom ≫ (trivialDerived A G).map (baseUnitIso A).hom ≫
    ((trivial (R := A.toMon) (P := G)).mapDerivedCategorySingleFunctor 0).hom.app
      (Mod.regular A.X) = (canonicalActionUnit (A := A) (G := G)).hom

/-- The canonical strong derived tensor comparison, uniquely fixed by the localization
of the ordinary diagonal tensor and unit.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup).
Proof: trivial action is exact and carries flat modules to action-flat modules because
forgetting detects exactness of tensor with them. Apply it to K-flat representatives.
The localized tensor comparisons are isomorphisms and descend uniquely; associativity
and unit coherence descend from total complexes. Every derived object admits a K-flat
representative, so the displayed normalization determines all components uniquely. -/
theorem derivedTrivialTensorExist : ∃! core : (trivialDerived A G).CoreMonoidal,
    TrivialTensorModel (A := A) (G := G) core ∧ TrivialUnitModel (A := A) (G := G) core := by
  sorry

/-- The unique representative-normalized derived tensor comparison for trivial action.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def derivedTrivialTensor (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (trivialDerived A G).CoreMonoidal :=
  Classical.choose (derivedTrivialTensorExist (A := A) (G := G))

/-- Strong monoidality with its canonical ordinary-module normalization.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
instance derivedTrivialMonoidal : (trivialDerived A G).Monoidal :=
  (derivedTrivialTensor A G).toMonoidal

/-- The derived cup pairing is the monoidal adjoint mate of the actual tensor of counits.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
instance derivedLax : (derived A G).LaxMonoidal := (adjunction A G).rightAdjointLaxMonoidal

/-- The tensor unit identification for the actual trivial coefficient object.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def actionUnitIso (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : 𝟙_ (DerivedCategory.{u + 1} (Equivariant A G)) ≅ coefficient A G :=
  canonicalActionUnit (A := A) (G := G)

/-- Derived internal invariants of trivial coefficients, in the ordinary derived category.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def cohomology (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : DerivedCategory.{u + 1} (Modules A) :=
  (derived A G).obj (coefficient A G)


/-- Multiplication of trivial regular coefficients, through its tensor-unit comparison.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def coefficientMultiply : coefficient A G ⊗ coefficient A G ⟶ coefficient A G :=
  ((actionUnitIso A G).inv ⊗ₘ (actionUnitIso A G).inv) ≫
    (λ_ (𝟙_ (DerivedCategory.{u + 1} (Equivariant A G)))).hom ≫ (actionUnitIso A G).hom

/-- Cup multiplication is the adjoint lax pairing followed by regular-ring multiplication.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def cup : cohomology A G ⊗ cohomology A G ⟶ cohomology A G :=
  Functor.LaxMonoidal.μ (derived A G) (coefficient A G) (coefficient A G) ≫
    (derived A G).map (coefficientMultiply (A := A) (G := G))

/-- The cup unit is the adjoint unit applied to the regular-ring unit.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def cupUnit : 𝟙_ (DerivedCategory.{u + 1} (Modules A)) ⟶ cohomology A G :=
  Functor.LaxMonoidal.ε (derived A G) ≫ (derived A G).map (actionUnitIso A G).hom

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Exact restriction identifies the original trivial regular coefficient objects.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def coefficientRestriction (v : H →ₜ* G) :
    (groupDerived A v).obj (coefficient A G) ≅ coefficient A H :=
  ((inflate (R := A.toMon) v).mapDerivedCategorySingleFunctor 0).app (regularTrivial A G)

/-- The actual restriction arrow on derived trivial-coefficient invariants.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def groupCupMap (v : H →ₜ* G) : cohomology A G ⟶ cohomology A H :=
  (groupMap A v).app (coefficient A G) ≫
    (derived A H).map (coefficientRestriction (A := A) v).hom


section OrderedProducts
variable {C : Type v} [Category.{w} C] [MonoidalCategory C]

/-- Right-associated tensor powers, retaining order and the empty tensor unit.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def tensorPower (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => X ⊗ tensorPower X n

/-- Tensoring the same map in all positions, without permutations or sign changes.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def tensorPowerMap {X Y : C} (f : X ⟶ Y) : ∀ n : ℕ, tensorPower X n ⟶ tensorPower Y n
  | 0 => 𝟙 _
  | n + 1 => f ⊗ₘ tensorPowerMap f n

/-- The ordered iterated cup multiplication; length zero is the specified unit.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-cup). -/
def orderedProduct {X : C} (e : 𝟙_ C ⟶ X) (m : X ⊗ X ⟶ X) :
    ∀ n : ℕ, tensorPower X n ⟶ X
  | 0 => e
  | n + 1 => (𝟙 X ⊗ₘ orderedProduct e m n) ≫ m

end OrderedProducts


end CategoryTheory.CondensedDerivedRestriction
