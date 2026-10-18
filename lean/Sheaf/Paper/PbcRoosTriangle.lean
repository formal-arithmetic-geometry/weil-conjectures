/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.PbcDerivedProductRepresentation
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Functorial Roos triangles and evaluated Milnor sequences

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
`prop-weil-pbc-roos-triangle`; Stacks 07KX, 08TC, 07KW and 07KY
(blueprint: prop-weil-pbc-roos-triangle).

All towers are objects of D(Tow(Mod(A_T))). Natural transformations of presheaf-valued
functors express naturality both in the tower and in restriction of the test object.
On a weakly contractible object evaluation is exact. Thus sections of cohomology sheaves
are the hypercohomology groups H^i(U,-), including for unbounded complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) {A : Type u} [CommRing A]

/-- The specified test objects, with all morphisms between them retained.
Source: Stacks 0946 and the blueprint evaluation clause
(blueprint: prop-weil-pbc-roos-triangle). -/
def pbcMilnorTests : ObjectProperty T.ProEt := fun U ↦
  (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} U ∧ CompactSpace U.left

/-- The countable product functor of the canonical evaluated tower.
Source: Stacks 08TC (blueprint: prop-weil-pbc-roos-triangle). -/
abbrev pbcTowerProduct (d : Scheme.AdicCoefficientDatum A) :
    DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤
    DerivedCategory (Scheme.CompletedAdicModules T d) where
  obj M := ∏ᶜ fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).obj (op n)
  map f := Limits.Pi.map (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).map f).app (op n))
  map_id M := by
    apply Pi.hom_ext
    intro n
    simp
  map_comp f g := by
    apply Pi.hom_ext
    intro n
    simp

/-- The underlying abelian cohomology presheaf. On weakly contractible test objects its
sections compute hypercohomology, since their section functor is exact (Stacks 0946).
Source: Stacks 07KY (blueprint: prop-weil-pbc-roos-triangle). -/
def pbcCohomologyPresheaf (d : Scheme.AdicCoefficientDatum A) (i : ℤ) :
    DerivedCategory (Scheme.CompletedAdicModules T d) ⥤ ((pbcMilnorTests T).FullSubcategoryᵒᵖ ⥤
    AddCommGrpCat.{u + 1}) :=
  DerivedCategory.homologyFunctor (Scheme.CompletedAdicModules T d) i ⋙
    SheafOfModules.toSheaf (Scheme.completedAdicRing T d) ⋙
      sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft (pbcMilnorTests T).FullSubcategoryᵒᵖ T.ProEtᵒᵖ
          AddCommGrpCat.{u + 1}).obj (ObjectProperty.ι (pbcMilnorTests T)).op

/-- The cohomology towers as a presheaf in the test object.
Source: Stacks 07KY (blueprint: prop-weil-pbc-roos-triangle). -/
def pbcCohomologyTowers (d : Scheme.AdicCoefficientDatum A) (i : ℤ) :
    DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤ ((pbcMilnorTests T).FullSubcategoryᵒᵖ ⥤
    (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1})) :=
    pbcDerivedEvaluation T d ⋙
    (Functor.whiskeringRight ℕᵒᵖ (DerivedCategory (Scheme.CompletedAdicModules T d))
      ((pbcMilnorTests T).FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u + 1})).obj
      (pbcCohomologyPresheaf T d i) ⋙
    flipFunctor ℕᵒᵖ (pbcMilnorTests T).FullSubcategoryᵒᵖ AddCommGrpCat.{u + 1}

/-- The canonical comparison from cohomology of the product to the product of cohomology.
Its coordinates are induced by the actual derived-product projections.
Source: Stacks 07KC and 07KY (blueprint: prop-weil-pbc-roos-triangle). -/
def pbcProductCohomologyComparison (d : Scheme.AdicCoefficientDatum A) (i : ℤ)
    (M : DerivedCategory (Scheme.CompletedAdicTowers T d))
    (U : (pbcMilnorTests T).FullSubcategory) :
    ((pbcCohomologyPresheaf T d i).obj ((pbcTowerProduct T d).obj M)).obj (op U) ⟶
      ∏ᶜ fun n : ℕ ↦
        (((pbcCohomologyTowers T d i).obj M).obj (op U)).obj (op n) :=
  Pi.lift (fun n ↦ ((pbcCohomologyPresheaf T d i).map
    (Pi.π (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).obj (op n)) n)).app (op U))

/-- The evaluated connecting map determined by the last arrow of the Roos triangle.
Source: Stacks 07KY, the long exact sequence (blueprint: prop-weil-pbc-roos-triangle). -/
def pbcRoosConnecting (d : Scheme.AdicCoefficientDatum A) (i : ℤ)
    {P L : DerivedCategory (Scheme.CompletedAdicModules T d)} (δ : P ⟶ L⟦(1 : ℤ)⟧)
    (U : (pbcMilnorTests T).FullSubcategory) :
    ((pbcCohomologyPresheaf T d (i - 1)).obj P).obj (op U) ⟶
      ((pbcCohomologyPresheaf T d i).obj L).obj (op U) :=
  ((SheafOfModules.toSheaf (Scheme.completedAdicRing T d)).map
    ((DerivedCategory.homologyFunctor (Scheme.CompletedAdicModules T d) 0).shiftMap
      δ (i - 1) i (by omega))).hom.app (op U.obj)

/-- The actual first right derived functor of inverse limit on abelian-group towers.
The named structural theorems supply its instance parameters, without new assumptions.
Source: Stacks 07KW (blueprint: prop-weil-pbc-roos-triangle). -/
abbrev pbcFirstDerivedLimit :
    (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ AddCommGrpCat.{u + 1} :=
  letI := roosTowerEnoughInjectives.{u + 1}
  letI := roosLimitAdditive.{u + 1}
  (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ AddCommGrpCat.{u + 1}).rightDerived 1

/-- The left term R¹lim H^(i-1) of the Milnor sequence, retaining both naturalities.
Source: Stacks 07KY (blueprint: prop-weil-pbc-roos-triangle). -/
def pbcMilnorLeft (d : Scheme.AdicCoefficientDatum A) (i : ℤ) :
    DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤ ((pbcMilnorTests T).FullSubcategoryᵒᵖ ⥤
    AddCommGrpCat.{u + 1}) :=
  pbcCohomologyTowers T d (i - 1) ⋙
    (Functor.whiskeringRight (pbcMilnorTests T).FullSubcategoryᵒᵖ (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      AddCommGrpCat.{u + 1}).obj pbcFirstDerivedLimit

/-- The right term lim H^i of the Milnor sequence.
Source: Stacks 07KY (blueprint: prop-weil-pbc-roos-triangle). -/
def pbcMilnorRight (d : Scheme.AdicCoefficientDatum A) (i : ℤ) :
    DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤ ((pbcMilnorTests T).FullSubcategoryᵒᵖ ⥤
    AddCommGrpCat.{u + 1}) :=
  pbcCohomologyTowers T d i ⋙
    (Functor.whiskeringRight (pbcMilnorTests T).FullSubcategoryᵒᵖ (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      AddCommGrpCat.{u + 1}).obj lim

/-- The functorial Roos triangle and its natural evaluated Milnor short exact sequences.
The index n denotes the paper's positive level n+1. All cohomological degrees are integers.
Source: blueprint order 1246; Stacks 07KX, 08TC, 07KY and 07KW
(blueprint: prop-weil-pbc-roos-triangle).

Proof, following the seven node steps:
1. Represent the object by a complex C of strict towers. Exact sectionwise countable
products (lem-weil-proetale-countable-products-exact) and
lem-weil-derived-limit-products-core represent its product by the termwise product P.
The shift s has projections pr(n+1) followed by the transition; these commute with d.
2. Form Cone(1-s)[-1], with differential (y,x) ↦ (-dy-(1-s)x,dx). Projection to x and
inclusion of y give the inverse rotation of the mapping-cone triangle, hence a Roos
triangle in the sense of def-weil-derived-limit and def-weil-pbc-derived-inverse-limit.
3. A strict tower map induces the diagonal cone map (y,x) ↦ (vy,vx). These preserve
identity and composition. Products preserve quasi-isomorphisms by the products core;
lem-sf-triangle-morphism-iso then gives this also for the cone. Localization supplies
RF and the natural transformations p and δ, without a choice of triangulated cones.
4. For weakly contractible U, sections are exact by Stacks 0946 and the exact forgetful
functor lem-weil-pbc-module-sheaves-colimits-forgetful. Products are sectionwise.
5. Apply lem-sf-exact-functor-derived-triangulated and the long exact cohomology sequence
lem-sf-derived-homology-long-exact. Its outer maps are 1-s on the products of cohomology.
6. lem-pc-derived-limit-roos-abelian-groups identifies their kernel and cokernel with
lim and R¹lim. Factor the boundary through the cokernel and the projection through the
kernel. Exactness gives a mono, its image equal to the middle kernel, and an epi.
7. Naturality of the strict cone triangle and lem-weil-pbc-derived-cohomology-ladder
make both extracted arrows natural. Restrictions commute with differentials and
transitions; the same diagonal formula gives a morphism of evaluated triangles and
commutes with their connecting maps. Thus a and b are natural also in U.
The displayed cokernel comparison requires the left arrow to factor this very
connecting map, while the projection equations fix the right arrow. -/
theorem pbcRoosTriangle (d : Scheme.AdicCoefficientDatum A) :
    ∃ (RF : DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤
        DerivedCategory (Scheme.CompletedAdicModules T d))
      (p : RF ⟶ pbcTowerProduct T d)
      (δ : pbcTowerProduct T d ⟶ RF ⋙
        shiftFunctor (DerivedCategory (Scheme.CompletedAdicModules T d)) (1 : ℤ)),
      (∀ M : DerivedCategory (Scheme.CompletedAdicTowers T d),
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).map
            (homOfLE (Nat.le_succ n)).op)
          (RF.obj M) (p.app M) (δ.app M)) ∧
      ∀ i : ℤ, ∃
        (a : pbcMilnorLeft T d i ⟶ RF ⋙ pbcCohomologyPresheaf T d i)
        (b : RF ⋙ pbcCohomologyPresheaf T d i ⟶ pbcMilnorRight T d i),
        ∀ (M : DerivedCategory (Scheme.CompletedAdicTowers T d))
          (U : (pbcMilnorTests T).FullSubcategory),
          (∃ hz : (a.app M).app (op U) ≫ (b.app M).app (op U) = 0,
            (ShortComplex.mk ((a.app M).app (op U))
              ((b.app M).app (op U)) hz).ShortExact) ∧
          (∃ e : pbcFirstDerivedLimit.obj
              (((pbcCohomologyTowers T d (i - 1)).obj M).obj (op U)) ≅
                cokernel (roosMap
                  (((pbcCohomologyTowers T d (i - 1)).obj M).obj (op U))),
            pbcProductCohomologyComparison T d (i - 1) M U ≫
                cokernel.π (roosMap
                  (((pbcCohomologyTowers T d (i - 1)).obj M).obj (op U))) ≫
                e.inv ≫ (a.app M).app (op U) =
              pbcRoosConnecting T d i (δ.app M) U) ∧
          ∀ n : ℕ,
            (b.app M).app (op U) ≫
                limit.π (((pbcCohomologyTowers T d i).obj M).obj (op U)) (op n) =
              ((pbcCohomologyPresheaf T d i).map
                (p.app M ≫ Pi.π
                  (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).obj (op n)) n)).app
                    (op U) := by
  sorry

end AlgebraicGeometry.ProEtale
