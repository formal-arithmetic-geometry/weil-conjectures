/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Sheaf.Paper.RestrictionDerivedProducts
public import Sheaf.Paper.RingedTopoiTensorSections
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Flat scalar restriction of the strict Koszul tower

Source: Stacks Project, algebraization.tex, Tag 0A0E; sites-cohomology.tex, Tags 0A07
and 0941; more-algebra.tex, Tag 0913.
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison).

## Main statements

* `flatScalarKoszulTowerComparison`: strict and derived normalized comparisons.

The coordinate maps below use the ordered tensor basis of the positive Koszul complex,
its dual evaluation, and the coproduct maps of total tensor. They specify actual maps,
so the comparison cannot be changed by a simultaneous choice of coordinates.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}

/-- The existing category of module sheaves. Source: Stacks 0A0E
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev Modules (O : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)

/-- Strict inverse towers in the existing module category. Source: Stacks 0941
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev Towers (O : Sheaf J CommRingCat.{u}) := ℕᵒᵖ ⥤ Modules O

/-- The tensor bifunctor already used by the Koszul system. Source: Stacks 0A0E
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev tensor (O : Sheaf J CommRingCat.{u}) :=
  @curriedTensor (Modules O) _ (SheafOfModules.monoidalCategory O)

/-- The rank-one module sheaf. Source: Stacks 0A0E
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev one (O : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)

/-- The number of selected factors, as an integer degree. Source: Stacks 0913
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
def degree : (r : ℕ) → (Fin r → Bool) → ℤ :=
  fun r ↦ Nat.rec (fun _ ↦ 0)
    (fun _ ih e ↦ (if e 0 then 1 else 0) + ih (fun i ↦ e i.succ)) r

/-- The basis inclusion in degree zero or one of a positive Koszul factor.
Source: Stacks 0913
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
def factorBasis (O : Sheaf J CommRingCat.{u})
    (a : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (e : Bool) :
    one O ⟶ (ringedKoszulFactor O a m).X (if e then 1 else 0) :=
  match e with
  | false => (HomologicalComplex.doubleXIso₀ _ _).inv
  | true => (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv

/-- The ordered tensor basis inclusion into the positive Koszul complex.
Source: Stacks 0913; the empty tensor has its sole basis vector in degree zero.
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
def positiveBasis (O : Sheaf J CommRingCat.{u}) : (r : ℕ) →
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) → (m : ℕ) →
    (e : Fin r → Bool) → one O ⟶ (ringedKoszulDiagram O r a).obj m |>.X (degree r e) :=
  letI : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  fun r ↦ Nat.rec
    (fun _ _ _ ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one O)).inv)
    (fun r ih a m e ↦
      (λ_ (one O)).inv ≫
        ((tensor O).map (factorBasis O (a 0) m (e 0))).app _ ≫
        ((tensor O).obj _).map (ih (fun i ↦ a i.succ) m (fun i ↦ e i.succ)) ≫
        CochainComplex.ιMapBifunctor (ringedKoszulFactor O (a 0) m)
          ((ringedKoszulDiagram O r (fun i ↦ a i.succ)).obj m) (tensor O)
          (if e 0 then 1 else 0) (degree r (fun i ↦ e i.succ)) (degree (r + 1) e) rfl) r

/-- Evaluate the dual Koszul complex on a specified positive tensor basis vector.
It is zero outside the vector's dual degree. Source: Stacks 0A0E and 0913
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
def dualCoordinate (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (e : Fin r → Bool) (q : ℤ) :
    ((ringedKoszulDualTower O r a).obj (op m)).X q ⟶ one O :=
  if h : degree r e + q = 0 then
    homComplexπ ((ringedKoszulDiagram O r a).obj m) (ringedSiteRingComplex O)
        q (degree r e) 0 h ≫
      SheafOfModules.homObjMap (R := O) (positiveBasis O r a m e)
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one O)).hom ≫
      (SheafOfModules.homObjUnitIso (R := O) (one O)).hom
  else 0

/-- The actual exterior-coordinate projection of a tensor-tower term.
The total complex uses coproducts, and this map is their universal descendent.
Source: Stacks 0A0E; the projection sends c tensor e_S to c.
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
def coordinate (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O)
    (m : ℕ) (e : Fin r → Bool) (n : ℤ) :
    ((ringedKoszulTensorTowerComplex O r a N).X n).obj (op m) ⟶
      N.X (n + degree r e) :=
  letI : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  HomologicalComplex.mapBifunctorDesc
    (K₁ := N) (K₂ := (ringedKoszulDualTower O r a).obj (op m))
    (F := tensor O) (c := .up ℤ) (fun p q _ ↦
      if hp : p = n + degree r e then
        ((tensor O).obj (N.X p)).map (dualCoordinate O r a m e q) ≫
          (ρ_ (N.X p)).hom ≫ eqToHom (congrArg N.X hp)
      else 0)

/-- Restriction of scalars, exactly Mathlib's ring-sheaf functor. Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev restriction {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :=
  SheafOfModules.restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

/-- Termwise restriction on complexes. Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev restrictComplex {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :=
  (restriction φ).mapHomologicalComplex (.up ℤ)

/-- Levelwise restriction on strict towers. Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev restrictTower {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules B) (Modules R)).obj (restriction φ)

/-- Termwise levelwise restriction. Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev restrictTowerComplex {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :=
  (restrictTower φ).mapHomologicalComplex (.up ℤ)

/-- The image list of global sections. Source: Stacks 0A0E
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
def imageSections {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) {r : ℕ}
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections) :
    Fin r → (B.obj ⋙ forget CommRingCat).sections :=
  fun i ↦ ⟨fun U ↦ φ.hom.app U ((a i).val U), fun f ↦ by
    exact congrFun (congrArg (fun g ↦ g.hom) (φ.hom.naturality f).symm) ((a i).val _) |>.trans
      (congrArg (φ.hom.app _) ((a i).property f))⟩

/-- Ordinary inverse limit on complexes of strict towers. Source: Stacks 0941
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev limitComplex (O : Sheaf J CommRingCat.{u}) :=
  (lim : Towers O ⥤ Modules O).mapHomologicalComplex (.up ℤ)

/-- The canonical comparison, identity on compatible families, before deriving limit.
Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
def limitComparison {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :=
  letI : PreservesLimitsOfSize.{0, 0} (restriction φ) :=
    preservesSmallestLimits_of_preservesLimits (restriction φ)
  NatTrans.mapHomologicalComplex
    (preservesLimitNatIso (restriction φ) (J := ℕᵒᵖ)).hom (.up ℤ)

variable {R B : Sheaf J CommRingCat.{u}}
variable [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules B)]
variable [HasDerivedCategory.{w} (Towers R)] [HasDerivedCategory.{w} (Towers B)]

/-- Exact scalar restriction on unbounded derived categories. Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev restrictDerived (φ : R ⟶ B) := (restriction φ).mapDerivedCategory

/-- Exact levelwise scalar restriction on the derived category of strict towers.
Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev restrictTowerDerived (φ : R ⟶ B) := (restrictTower φ).mapDerivedCategory

/-- Exact evaluation on the derived category of strict towers. Source: Stacks 0941
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev evaluateDerived (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    (m : ℕᵒᵖ) := ((evaluation ℕᵒᵖ (Modules O)).obj m).mapDerivedCategory

/-- Restriction and evaluation commute by the exact-functor localization comparisons.
Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
def evaluationComparison (φ : R ⟶ B) (m : ℕᵒᵖ) :
    restrictTowerDerived φ ⋙ evaluateDerived R m ≅
      evaluateDerived B m ⋙ restrictDerived φ :=
  (Functor.mapDerivedCategoryCompIso (restrictTower φ)
    ((evaluation ℕᵒᵖ (Modules R)).obj m)).symm ≪≫
      Functor.mapDerivedCategoryCompIso ((evaluation ℕᵒᵖ (Modules B)).obj m) (restriction φ)

/-- The canonical ordinary inverse-limit projection, applied degreewise.
Source: Stacks 0941
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev limitProjection (O : Sheaf J CommRingCat.{u}) (m : ℕᵒᵖ) :=
  NatTrans.mapHomologicalComplex
    (lim.π m : (lim : Towers O ⥤ Modules O) ⟶ (evaluation ℕᵒᵖ (Modules O)).obj m) (.up ℤ)

/-- Scalar restriction identifies strict Koszul towers, with the identity on each ordered
exterior coordinate, their coaugmentations, and their normalized total derived limits.
The index m : ℕ represents exponent m+1, hence includes exactly the positive powers.

Source: Stacks Project, algebraization.tex, Tag 0A0E; sites-cohomology.tex, Tags 0A07
and 0941; more-algebra.tex, Tag 0913.
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison).

Proof:
1. Expand each finite tensor in its ordered basis indexed by Boolean subsets. On each
   coordinate both total differentials are d_C plus the signed multiplication by phi(a_j)^m.
   Thus the identity coordinates give inverse chain maps, even for unbounded C.
2. The transition on a subset is multiplication by the product of phi(a_j) over that
   subset. The coaugmentation is its empty coordinate. Both commute with the comparison,
   naturally in chain maps C to C'.
3. Each dual Koszul complex is bounded above with finite free terms, hence K-flat by
   lem-pc-bounded-above-flat-kflat-site. Apply lem-weil-pbc-kflat-fixed-tensor-triangulated
   and levelwise exactness of towers to descend both actual tensor functors through Q.
   Exact scalar restriction descends too (def-weil-abstract-derived-category).
4. Flatness and lem-weil-pbc-flat-ringed-diagram-restriction show that restriction preserves
   K-injectives both for modules and towers. By lem-weil-pbc-restriction-derived-products,
   the ordinary limit comparison is identity on compatible families and their projections.
5. Apply lem-weil-ringed-tower-pushforward-limit-comparison to the identity topos with ring
   map phi. The common K-injective model supplied by
   lem-weil-pbc-ringed-strict-tower-homotopy-limit gives alpha with the displayed underived
   normalization. Compose alpha with derived inverse limit of the descended strict h.
6. The canonical unit is the actual ordinary-limit unit followed by the comparison.
   Strict coaugmentation compatibility therefore gives the equality of derived unit arrows.
7. Normalize derived projections by their ordinary projections on K-injective models.
   The same comparison respects every projection; functoriality gives the evaluation square.
8. For the empty list the tower is constant. Evaluation at its first index is exact and
   left adjoint to the constant tower functor. By
   lem-weil-pbc-right-adjoint-preserves-kinjective and prop-pur-kinjective-resolutions-exist,
   a constant K-injective module resolution computes its derived limit. All projections
   and the unit are identity under that identification; the unit equation fixes gamma.
-/
theorem flatScalarKoszulTowerComparison (φ : R ⟶ B)
    (_hflat : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor φ) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor φ))
    (r : ℕ) (a : Fin r → (R.obj ⋙ forget CommRingCat).sections) :
    ∃ (h : ringedKoszulTensorTowerFunctor B r (imageSections φ a) ⋙
          restrictTowerComplex φ ≅
        restrictComplex φ ⋙ ringedKoszulTensorTowerFunctor R r a)
      (DB : RingedKoszulLimitPresentation B r (imageSections φ a))
      (DR : RingedKoszulLimitPresentation R r a)
      (hD : DB.tensorTower ⋙ restrictTowerDerived φ ≅ restrictDerived φ ⋙ DR.tensorTower)
      (alpha : DB.inverseLimit ⋙ restrictDerived φ ≅
        restrictTowerDerived φ ⋙ DR.inverseLimit)
      (gamma : DB.completion ⋙ restrictDerived φ ≅ restrictDerived φ ⋙ DR.completion)
      (pB : ∀ m : ℕᵒᵖ, DB.inverseLimit ⟶ evaluateDerived B m)
      (pR : ∀ m : ℕᵒᵖ, DR.inverseLimit ⟶ evaluateDerived R m),
      (∀ (N : ringedSiteComplex B) (m : ℕ) (e : Fin r → Bool) (n : ℤ),
        ((h.hom.app N).f n).app (op m) ≫
            coordinate R r a ((restrictComplex φ).obj N) m e n =
          (restriction φ).map (coordinate B r (imageSections φ a) N m e n)) ∧
      (∀ (N : ringedSiteComplex B) (m : ℕᵒᵖ) (n : ℤ),
        (restriction φ).map
            ((ringedKoszulTensorUnitComponent B r (imageSections φ a) N m).f n) ≫
            ((h.hom.app N).f n).app m =
          (ringedKoszulTensorUnitComponent R r a ((restrictComplex φ).obj N) m).f n) ∧
      (∀ N : ringedSiteComplex B,
        (restrictTowerDerived φ).map (DB.tensorFactors.hom.app N) ≫
            (restrictTower φ).mapDerivedCategoryFactors.hom.app
              ((ringedKoszulTensorTowerFunctor B r (imageSections φ a)).obj N) ≫
            DerivedCategory.Q.map (h.hom.app N) =
          hD.hom.app (DerivedCategory.Q.obj N) ≫
            DR.tensorTower.map ((restriction φ).mapDerivedCategoryFactors.hom.app N) ≫
            DR.tensorFactors.hom.app ((restrictComplex φ).obj N)) ∧
      (∀ X : CochainComplex (Towers B) ℤ,
        (restrictDerived φ).map (DB.comparison.app X) ≫
            alpha.hom.app (DerivedCategory.Q.obj X) =
          (restriction φ).mapDerivedCategoryFactors.hom.app ((limitComplex B).obj X) ≫
            DerivedCategory.Q.map ((limitComparison φ).app X) ≫
            DR.comparison.app ((restrictTowerComplex φ).obj X) ≫
            DR.inverseLimit.map ((restrictTower φ).mapDerivedCategoryFactors.inv.app X)) ∧
      (∀ E : DerivedCategory (Modules B),
        gamma.hom.app E = alpha.hom.app (DB.tensorTower.obj E) ≫
          DR.inverseLimit.map (hD.hom.app E)) ∧
      (∀ E : DerivedCategory (Modules B),
        (restrictDerived φ).map (DB.unit E) ≫ gamma.hom.app E =
          DR.unit ((restrictDerived φ).obj E)) ∧
      (∀ (X : CochainComplex (Towers B) ℤ) (m : ℕᵒᵖ),
        DB.comparison.app X ≫ (pB m).app (DerivedCategory.Q.obj X) ≫
            ((evaluation ℕᵒᵖ (Modules B)).obj m).mapDerivedCategoryFactors.hom.app X =
          DerivedCategory.Q.map ((limitProjection B m).app X)) ∧
      (∀ (X : CochainComplex (Towers R) ℤ) (m : ℕᵒᵖ),
        DR.comparison.app X ≫ (pR m).app (DerivedCategory.Q.obj X) ≫
            ((evaluation ℕᵒᵖ (Modules R)).obj m).mapDerivedCategoryFactors.hom.app X =
          DerivedCategory.Q.map ((limitProjection R m).app X)) ∧
      (∀ (E : DerivedCategory (Modules B)) (m : ℕᵒᵖ),
        gamma.hom.app E ≫ (pR m).app (DR.tensorTower.obj ((restrictDerived φ).obj E)) =
          (restrictDerived φ).map ((pB m).app (DB.tensorTower.obj E)) ≫
            (evaluationComparison φ m).inv.app (DB.tensorTower.obj E) ≫
            (evaluateDerived R m).map (hD.hom.app E)) ∧
      (r = 0 → ∃ (eB : DB.completion ≅ 𝟭 (DerivedCategory (Modules B)))
          (eR : DR.completion ≅ 𝟭 (DerivedCategory (Modules R))),
        (∀ E, DB.unit E ≫ eB.hom.app E = 𝟙 E) ∧
        (∀ E, DR.unit E ≫ eR.hom.app E = 𝟙 E) ∧
        ∀ E, gamma.hom.app E ≫ eR.hom.app ((restrictDerived φ).obj E) =
          (restrictDerived φ).map (eB.hom.app E)) := by
  sorry

end CategoryTheory.FlatScalarKoszul
