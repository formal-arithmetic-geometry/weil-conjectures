/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.PbcDerivedProductRepresentation
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.CategoryTheory.Triangulated.RoosCohomologyProjection
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

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

private abbrev pbcTestsForget (d : Scheme.AdicCoefficientDatum A) :=
  SheafOfModules.toSheaf.{u + 1} (Scheme.completedAdicRing T d) ⋙
    sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft (pbcMilnorTests T).FullSubcategoryᵒᵖ T.ProEtᵒᵖ
        AddCommGrpCat.{u + 1}).obj (ObjectProperty.ι (pbcMilnorTests T)).op

private theorem pbcModulePresheaf_preservesHomology (d : Scheme.AdicCoefficientDatum A) :
    (SheafOfModules.toSheaf.{u + 1} (Scheme.completedAdicRing T d) ⋙
      sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft (pbcMilnorTests T).FullSubcategoryᵒᵖ T.ProEtᵒᵖ
          AddCommGrpCat.{u + 1}).obj
            (ObjectProperty.ι (pbcMilnorTests T)).op).PreservesHomology := by
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let G := SheafOfModules.toSheaf.{u + 1} (Scheme.completedAdicRing T d) ⋙
    sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft (pbcMilnorTests T).FullSubcategoryᵒᵖ T.ProEtᵒᵖ
        AddCommGrpCat.{u + 1}).obj (ObjectProperty.ι (pbcMilnorTests T)).op
  have : G.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    have hcomp (U : (pbcMilnorTests T).FullSubcategoryᵒᵖ) :
        Epi ((G.map f).app U) := by
      apply (AddCommGrpCat.epi_iff_surjective _).mpr
      let φ := (SheafOfModules.toSheaf.{u + 1} (Scheme.completedAdicRing T d)).map f
      have : Epi φ := inferInstance
      have : Sheaf.IsLocallySurjective φ :=
        (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} φ).mpr inferInstance
      let ψ := (sheafCompose (Scheme.ProEt.topology T)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).map φ
      exact U.unop.property.1 ψ inferInstance
    exact NatTrans.epi_of_epi_app _
  have : PreservesFiniteLimits G := by
    dsimp [G]
    infer_instance
  exact Functor.preservesHomology_of_preservesEpis_and_kernels G

private theorem pbcCohomology_preservesProducts (d : Scheme.AdicCoefficientDatum A)
    (i : ℤ) : PreservesLimitsOfShape (Discrete ℕ) (pbcCohomologyPresheaf T d i) := by
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  have : HasFiniteBiproducts (Scheme.CompletedAdicModules T d) :=
    Abelian.hasFiniteBiproducts
  have : CountableAB4Star (Scheme.CompletedAdicModules T d) := by
    have : (lim (J := Discrete ℕ)
        (C := Scheme.CompletedAdicModules T d)).PreservesEpimorphisms :=
      { preserves := by
          intro F G f hf
          have h := (Scheme.ProEt.countableProducts_exact.{u, u, 0} T
            (Scheme.completedAdicCommRing T d)).2.2
            ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
            (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
          have he : lim.map f = (Pi.isoLimit _).inv ≫
              Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
            apply limit.hom_ext
            intro ⟨n⟩
            simp
          rw [he]
          infer_instance }
    have := hasExactLimitsOfShape_of_preservesEpi
      (Scheme.CompletedAdicModules T d) (Discrete ℕ)
    exact CountableAB4Star.of_hasExactLimitsOfShape_nat _
  obtain ⟨hP, hprops⟩ := derivedCategory_countableProducts_core.{0, u + 2, u + 1, u + 2}
    (Scheme.CompletedAdicModules T d)
  have := hprops.2 ℕ i
  have : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.toSheaf.{u + 1} (Scheme.completedAdicRing T d) ⋙
        sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.forget (Scheme.completedAdicRing T d) ⋙
        PresheafOfModules.toPresheaf (Scheme.completedAdicRing T d).obj))
  have : PreservesLimitsOfShape (Discrete ℕ) (pbcTestsForget T d) := by
    exact comp_preservesLimitsOfShape
      (SheafOfModules.toSheaf.{u + 1} (Scheme.completedAdicRing T d) ⋙
        sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
      ((Functor.whiskeringLeft (pbcMilnorTests T).FullSubcategoryᵒᵖ T.ProEtᵒᵖ
        AddCommGrpCat.{u + 1}).obj (ObjectProperty.ι (pbcMilnorTests T)).op)
  exact comp_preservesLimitsOfShape
    (DerivedCategory.homologyFunctor (Scheme.CompletedAdicModules T d) i) (pbcTestsForget T d)

/-- Strict-complex construction of the functorial Roos triangle.
Source: blueprint Stacks 07KX and 08TC (blueprint: prop-weil-pbc-roos-triangle). -/
theorem pbcRoosTriangle_core (d : Scheme.AdicCoefficientDatum A) :
    ∃ (RF : DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤
        DerivedCategory (Scheme.CompletedAdicModules T d))
      (p : RF ⟶ pbcTowerProduct T d)
      (δ : pbcTowerProduct T d ⟶ RF ⋙
        shiftFunctor (DerivedCategory (Scheme.CompletedAdicModules T d)) (1 : ℤ)),
      ∀ M : DerivedCategory (Scheme.CompletedAdicTowers T d),
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).map
            (homOfLE (Nat.le_succ n)).op)
          (RF.obj M) (p.app M) (δ.app M) := by
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  obtain ⟨RF, η, hRF, hI, hres, hs, hp, E, ε, p, δ, ht, htri, hn, hδ, hrest⟩ :=
    ringedStrictTowerHomotopyLimitIndependentCoefficients.{u + 2, u + 1, u, u + 1}
      (C := T.ProEt) (Scheme.ProEt.topology T) (Scheme.completedAdicRing T d)
      (Scheme.completedAdicRing_mul_comm T d)
  let := hp
  let : Localization.Lifting (DerivedCategory.Q (C := Scheme.CompletedAdicTowers T d))
      (HomologicalComplex.quasiIso (Scheme.CompletedAdicTowers T d) (.up ℤ))
      (pbcComplexEvaluation T d) E := ⟨ε⟩
  let : Localization.Lifting (DerivedCategory.Q (C := Scheme.CompletedAdicTowers T d))
      (HomologicalComplex.quasiIso (Scheme.CompletedAdicTowers T d) (.up ℤ))
      (pbcComplexEvaluation T d) (pbcDerivedEvaluation T d) := ⟨pbcEvaluationFactors T d⟩
  let e : E ≅ pbcDerivedEvaluation T d :=
    Localization.liftNatIso (DerivedCategory.Q (C := Scheme.CompletedAdicTowers T d))
      (HomologicalComplex.quasiIso (Scheme.CompletedAdicTowers T d) (.up ℤ))
      (pbcComplexEvaluation T d) (pbcComplexEvaluation T d) E
      (pbcDerivedEvaluation T d) (Iso.refl _)
  let P : DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤
      DerivedCategory (Scheme.CompletedAdicModules T d) :=
    { obj := fun M ↦ ∏ᶜ fun n : ℕ ↦ (E.obj M).obj (op n)
      map := fun f ↦ Limits.Pi.map (fun n : ℕ ↦ (E.map f).app (op n))
      map_id := by intros; apply Pi.hom_ext; intro n; simp
      map_comp := by intros; apply Pi.hom_ext; intro n; simp }
  let eP : P ≅ pbcTowerProduct T d :=
    NatIso.ofComponents
      (fun M ↦ Pi.mapIso (fun n : ℕ ↦ (e.app M).app (op n))) (by
        intro M N f
        apply Pi.hom_ext
        intro n
        simp [P, Category.assoc])
  let p' : RF ⟶ pbcTowerProduct T d :=
    { app := fun M ↦ p M ≫ (eP.app M).hom
      naturality := by
        intro M N f
        change RF.map f ≫ p N ≫ eP.hom.app N =
          (p M ≫ eP.hom.app M) ≫ (pbcTowerProduct T d).map f
        rw [← Category.assoc, hn f, Category.assoc]
        simpa only [P, Category.assoc] using
          congrArg (fun k ↦ p M ≫ k) (eP.hom.naturality f) }
  let δ' : pbcTowerProduct T d ⟶ RF ⋙
      shiftFunctor (DerivedCategory (Scheme.CompletedAdicModules T d)) (1 : ℤ) :=
    { app := fun M ↦ (eP.app M).inv ≫ δ M
      naturality := by
        intro M N f
        change (pbcTowerProduct T d).map f ≫ eP.inv.app N ≫ δ N =
          (eP.inv.app M ≫ δ M) ≫ (RF.map f)⟦(1 : ℤ)⟧'
        rw [← Category.assoc, eP.inv.naturality f, Category.assoc]
        simpa only [P, Category.assoc] using
          congrArg (fun k ↦ eP.inv.app M ≫ k) (hδ f) }
  refine ⟨RF, p', δ', fun M ↦ ?_⟩
  let t := Pretriangulated.Triangle.mk (p M)
    (towerTransitionEndomorphism (fun n : ℕ ↦ (E.obj M).map
      (homOfLE (Nat.le_succ n)).op)) (δ M)
  let t' := Pretriangulated.Triangle.mk (p'.app M)
    (towerTransitionEndomorphism (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).map
      (homOfLE (Nat.le_succ n)).op)) (δ'.app M)
  have et : t ≅ t' := Pretriangulated.Triangle.isoMk t t' (Iso.refl _) (eP.app M) (eP.app M)
    (by simp [t, t', p'])
    (by
      change towerTransitionEndomorphism _ ≫ (eP.app M).hom =
        (eP.app M).hom ≫ towerTransitionEndomorphism _
      exact (towerTransitionEndomorphism_natural_backward _ _
        (fun n ↦ (e.hom.app M).app (op n))
        (fun n ↦ ((e.hom.app M).naturality (homOfLE (Nat.le_succ n)).op).symm)).symm)
    (by simp [t, t', δ'])
  exact (Pretriangulated.distinguished_iff_of_iso et).mp (htri M)

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
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  obtain ⟨RF, p, δ, hT⟩ := pbcRoosTriangle_core T d
  refine ⟨RF, p, δ, hT, fun i ↦ ?_⟩
  let G := pbcTestsForget T d
  have : G.PreservesHomology := pbcModulePresheaf_preservesHomology T d
  have hH (j : ℤ) : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor (Scheme.CompletedAdicModules T d) j ⋙ G) :=
    pbcCohomology_preservesProducts T d j
  obtain ⟨a, ha⟩ := roosCohomology_boundary (pbcDerivedEvaluation T d) G hH RF p δ hT i
  obtain ⟨b, hb⟩ := roosCohomology_projection (pbcDerivedEvaluation T d) G hH RF p δ hT i
  refine ⟨a, b, fun M U ↦ ?_⟩
  obtain ⟨hm, hz, he⟩ := ha M (op U)
  obtain ⟨hep, hπ⟩ := hb M (op U)
  let B := (((pbcCohomologyTowers T d i).obj M).obj (op U))
  let j : limit B ⟶ ∏ᶜ fun n : ℕ ↦ B.obj (op n) :=
    Pi.lift (fun n ↦ limit.π B (op n))
  have hj : Mono j := ⟨by
    intro Z f g h
    apply limit.hom_ext
    intro n
    obtain ⟨n⟩ := n
    have hn := congrArg (fun k ↦ k ≫ Pi.π (fun n : ℕ ↦ B.obj (op n)) n) h
    simpa only [j, Category.assoc, Pi.lift_π] using hn⟩
  have hbj : (b.app M).app (op U) ≫ j =
      ((pbcCohomologyPresheaf T d i).map (p.app M)).app (op U) ≫
        pbcProductCohomologyComparison T d i M U := by
    apply Pi.hom_ext
    intro n
    simpa [j, B, G, pbcTestsForget, pbcCohomologyTowers, roosCohomologyTowers,
      pbcCohomologyPresheaf, pbcProductCohomologyComparison, Functor.map_comp,
      SheafOfModules.comp_val, Category.assoc] using hπ n
  obtain ⟨hz, hex⟩ := hz
  have hz' : (a.app M).app (op U) ≫ (b.app M).app (op U) = 0 := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hbj, zero_comp]
    simpa [G, B, pbcTestsForget, pbcCohomologyTowers, roosCohomologyTowers,
      pbcCohomologyPresheaf, pbcProductCohomologyComparison, roosCohomologyComparison,
      Category.assoc] using hz
  refine ⟨⟨hz', ?_⟩, he, hπ⟩
  let φ : ShortComplex.mk ((a.app M).app (op U)) ((b.app M).app (op U)) hz' ⟶
      ShortComplex.mk ((a.app M).app (op U))
        (((pbcCohomologyPresheaf T d i).map (p.app M)).app (op U) ≫
          pbcProductCohomologyComparison T d i M U) hz :=
    ShortComplex.homMk (𝟙 _) (𝟙 _) j (by simp) (by simpa using hbj.symm)
  have : Epi φ.τ₁ := by change Epi (𝟙 _); infer_instance
  have : IsIso φ.τ₂ := by change IsIso (𝟙 _); infer_instance
  have : Mono φ.τ₃ := hj
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hex) hm hep


end AlgebraicGeometry.ProEtale
