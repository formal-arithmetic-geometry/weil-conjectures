# WeilConjectures.OpenCompletedRestriction.TowerComparison and Comparison

## Reason

The original comparison structures embed the full normalization equations into every
generated data recursor. Profiling the unchanged Comparison declaration records 17.0s
for its kernel declaration check, 8.5s for casesOn and 7.4s for mk.noConfusion. Combined
with the original TowerComparison recursors, even a file retaining theorem sorries
reaches the 60-second compile limit. The definition repair groups precisely the same
normalization equations in named Prop-valued predicates; subtypes store their
proofs. Existing field theorem names and types are retained by proved accessors.
No coefficient object, derived functor, comparison equation or hypothesis changes.

## Old

```lean
structure TowerComparison where
  finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n
  finite_sections : ∀ (n : ℕ) (M : integralOperationsFiniteModules l E X n)
      (V : U.ProEt) (x : M.val.obj (op ((inclusion j).obj V))),
    ((finite n).hom.app M).val.app (op V) x = graphSection l E j n M V x
  levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j
  level_sections : ∀ (P : IntegralOnSlice.Cx l E X none) (n : ℕ) (i : ℤ)
      (V : U.ProEt) (x : (P.X i).val.obj (op ((inclusion j).obj V))),
    HEq
      (((((levels.hom.app P).app (op n)).f i).val.app (op V))
        (IntegralOnSlice.generator l E X none n (P.X i)
          (op ((inclusion j).obj V)) 1 x))
      (graphSection l E j n
        (((unrestrictedIntegralFiniteComplex l E X n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E X n (P.X i)
          (op ((inclusion j).obj V)) 1 x))
  product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n)
  product_projections : ∀ (P : IntegralOnSlice.Cx l E X none) (n : ℕ),
    (product P).hom ≫ Pi.π (fun k : ℕ ↦ (targetTower l E j P).obj (op k)) n =
      (complexRestriction l E j).map
        (Pi.π (fun k : ℕ ↦ (sourceTower l E P).obj (op k)) n) ≫
          (levels.hom.app P).app (op n)
  roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j
  roos_first : ∀ P : IntegralOnSlice.Cx l E X none,
    roos.hom.app P ≫ roosProjection (A := IntegralOnSlice.Mod l E U none) (targetTower l E j P) =
      (complexRestriction l E j).map
        (roosProjection (A := IntegralOnSlice.Mod l E X none) (sourceTower l E P)) ≫
          (product P).hom
  roos_second : ∀ (P : IntegralOnSlice.Cx l E X none) (q : ℤ),
    (roos.hom.app P).f q ≫
        roosSecond (A := IntegralOnSlice.Mod l E U none) (targetTower l E j P) q =
      (ordinary l E j).map
        (roosSecond (A := IntegralOnSlice.Mod l E X none) (sourceTower l E P) q) ≫
          (product P).hom.f (q - 1)

structure Comparison extends TowerComparison l E j where
  derived : IntegralOnSlice.completion l E X none ⋙ derivedRestriction l E j ≅
    integralDerivedPullback l E j
  localization : ∀ P : (IntegralOnSlice.Good l E X none).FullSubcategory,
    derived.hom.app ((IntegralOnSlice.qGood l E X none).obj P) ≫
        (integralDerivedPullbackComparison l E j).hom.app P =
      (derivedRestriction l E j).map
        ((IntegralOnSlice.completionComparison l E X none).hom.app P) ≫
      (ordinary l E j).mapDerivedCategoryFactors.hom.app
        ((IntegralOnSlice.roos l E X none).obj P.obj) ≫
      DerivedCategory.Q.map (roos.hom.app P.obj)
```

## New

```lean
/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def FiniteSectionNormalization
    (finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (_levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (_product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (_roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ (n : ℕ) (M : integralOperationsFiniteModules l E X n)
      (V : U.ProEt) (x : M.val.obj (op ((inclusion j).obj V))),
    ((finite n).hom.app M).val.app (op V) x = graphSection l E j n M V x

/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def LevelSectionNormalization
    (_finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (_product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (_roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ (P : IntegralOnSlice.Cx l E X none) (n : ℕ) (i : ℤ)
      (V : U.ProEt) (x : (P.X i).val.obj (op ((inclusion j).obj V))),
    HEq
      (((((levels.hom.app P).app (op n)).f i).val.app (op V))
        (IntegralOnSlice.generator l E X none n (P.X i)
          (op ((inclusion j).obj V)) 1 x))
      (graphSection l E j n
        (((unrestrictedIntegralFiniteComplex l E X n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E X n (P.X i)
          (op ((inclusion j).obj V)) 1 x))

/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def ProductNormalization
    (_finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (_roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ (P : IntegralOnSlice.Cx l E X none) (n : ℕ),
    (product P).hom ≫ Pi.π (fun k : ℕ ↦ (targetTower l E j P).obj (op k)) n =
      (complexRestriction l E j).map
        (Pi.π (fun k : ℕ ↦ (sourceTower l E P).obj (op k)) n) ≫
          (levels.hom.app P).app (op n)

/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def RoosFirstNormalization
    (_finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (_levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ P : IntegralOnSlice.Cx l E X none,
    roos.hom.app P ≫ roosProjection (A := IntegralOnSlice.Mod l E U none) (targetTower l E j P) =
      (complexRestriction l E j).map
        (roosProjection (A := IntegralOnSlice.Mod l E X none) (sourceTower l E P)) ≫
          (product P).hom

/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def RoosSecondNormalization
    (_finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (_levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ (P : IntegralOnSlice.Cx l E X none) (q : ℤ),
    (roos.hom.app P).f q ≫
        roosSecond (A := IntegralOnSlice.Mod l E U none) (targetTower l E j P) q =
      (ordinary l E j).map
        (roosSecond (A := IntegralOnSlice.Mod l E X none) (sourceTower l E P) q) ≫
          (product P).hom.f (q - 1)

/-- The conjunction of the five original normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def TowerNormalization
    (finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  FiniteSectionNormalization l E j finite levels product roos ∧
  LevelSectionNormalization l E j finite levels product roos ∧
  ProductNormalization l E j finite levels product roos ∧
  RoosFirstNormalization l E j finite levels product roos ∧
  RoosSecondNormalization l E j finite levels product roos

/-- Normalization data for the single natural comparison. The finite sections fix
its levels; the two shifted-cone coordinates fix the actual chain map. The final
factorization fixes its descent on every derived morphism, including roofs.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def TowerComparison :=
  { d : (∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n) ×
    (IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j) ×
    (∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n)) ×
    (IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) //
      TowerNormalization l E j d.1 d.2.1 d.2.2.1 d.2.2.2 }

variable {l E j} in
/-- The original finite comparison data.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev TowerComparison.finite (d : TowerComparison l E j) :
    ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n :=
  d.val.1

variable {l E j} in
/-- The original levels comparison data.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev TowerComparison.levels (d : TowerComparison l E j) :
    IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j :=
  d.val.2.1

variable {l E j} in
/-- The original product comparison data.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev TowerComparison.product (d : TowerComparison l E j) :
    ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n) :=
  d.val.2.2.1

variable {l E j} in
/-- The original roos comparison data.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev TowerComparison.roos (d : TowerComparison l E j) :
    IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j :=
  d.val.2.2.2

private theorem tower_normalized (d : TowerComparison l E j) :
    TowerNormalization l E j d.finite d.levels d.product d.roos := d.property

variable {l E j} in
/-- The original finite_sections equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.finite_sections (d : TowerComparison l E j) :
    FiniteSectionNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).1

variable {l E j} in
/-- The original level_sections equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.level_sections (d : TowerComparison l E j) :
    LevelSectionNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).2.1

variable {l E j} in
/-- The original product_projections equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.product_projections (d : TowerComparison l E j) :
    ProductNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).2.2.1

variable {l E j} in
/-- The original roos_first equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.roos_first (d : TowerComparison l E j) :
    RoosFirstNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).the project server

variable {l E j} in
/-- The original roos_second equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.roos_second (d : TowerComparison l E j) :
    RoosSecondNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).the project server


attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

/-- The exact localization normalization as a proposition, keeping data-record recursors small.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
def ComparisonLocalization
    (roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
      integralOperationsPullbackComplexFunctor l E j)
    (derived : IntegralOnSlice.completion l E X none ⋙ derivedRestriction l E j ≅
      integralDerivedPullback l E j) : Prop :=
    ∀ P : (IntegralOnSlice.Good l E X none).FullSubcategory,
    derived.hom.app ((IntegralOnSlice.qGood l E X none).obj P) ≫
        (integralDerivedPullbackComparison l E j).hom.app P =
      (derivedRestriction l E j).map
        ((IntegralOnSlice.completionComparison l E X none).hom.app P) ≫
      (ordinary l E j).mapDerivedCategoryFactors.hom.app
        ((IntegralOnSlice.roos l E X none).obj P.obj) ≫
      DerivedCategory.Q.map (roos.hom.app P.obj)


/-- The descent of the normalized tower and Roos comparisons.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
def Comparison :=
  { d : TowerComparison l E j ×
      (IntegralOnSlice.completion l E X none ⋙ derivedRestriction l E j ≅
        integralDerivedPullback l E j) //
    ComparisonLocalization l E j d.1.roos d.2 }

variable {l E j} in
/-- The representative-level comparison data.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.toTowerComparison (d : Comparison l E j) : TowerComparison l E j := d.val.1

variable {l E j} in
/-- The inherited finite comparison.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.finite (d : Comparison l E j) := d.toTowerComparison.finite

variable {l E j} in
/-- The inherited levels comparison.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.levels (d : Comparison l E j) := d.toTowerComparison.levels

variable {l E j} in
/-- The inherited product comparison.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.product (d : Comparison l E j) := d.toTowerComparison.product

variable {l E j} in
/-- The inherited roos comparison.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.roos (d : Comparison l E j) := d.toTowerComparison.roos

variable {l E j} in
/-- The inherited finite_sections normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.finite_sections (d : Comparison l E j) :
    FiniteSectionNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.finite_sections

variable {l E j} in
/-- The inherited level_sections normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.level_sections (d : Comparison l E j) :
    LevelSectionNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.level_sections

variable {l E j} in
/-- The inherited product_projections normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.product_projections (d : Comparison l E j) :
    ProductNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.product_projections

variable {l E j} in
/-- The inherited roos_first normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.roos_first (d : Comparison l E j) :
    RoosFirstNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.roos_first

variable {l E j} in
/-- The inherited roos_second normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.roos_second (d : Comparison l E j) :
    RoosSecondNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.roos_second

variable {l E j} in
/-- The original derived comparison isomorphism.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.derived (d : Comparison l E j) :
    IntegralOnSlice.completion l E X none ⋙ derivedRestriction l E j ≅
      integralDerivedPullback l E j := d.val.2

variable {l E j} in
/-- The original localization equation, projected from its proof record.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.localization (d : Comparison l E j) :
    ComparisonLocalization l E j d.roos d.derived := d.property
```

The same four tower isomorphisms are stored in a product subtype whose predicate is
exactly the conjunction of the five original equations. `Comparison` is the product
subtype of `TowerComparison` and the derived isomorphism, constrained by exactly the
original localization equation. The original data accessor names are abbreviations;
the equation accessor names are proved theorems. No mathematical assertion is changed.
The internal constructor expressions are adapted; there are no external constructors.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OpenCompletedRestrictionIdentification | T4 | Definitions repaired and constructors adapted. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Stores Comparison and uses kappa; no constructor or equation projection change. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Unchanged; does not construct these records. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Unchanged; does not construct these records. |
| Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed | Unchanged; does not construct these records. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Unchanged; does not construct these records. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Unchanged; does not construct these records. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Unchanged; does not construct these records. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Unchanged; does not construct these records. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Unchanged; does not construct these records. |

`tools/downstream.py --uses TowerComparison Comparison` finds only these two modules.
All nine transitive consumers are unchanged. Their public assertions have the same
meaning. Target statements and coefficient definitions are unchanged; the target
meaning review sees an equivalent representation of the comparison assertion.

## Status

landed 20261025T204922-L-3049725 2026-10-25 (merge of deliver/T4/Sheaf.Paper.OpenCompletedRestrictionIdentification)
