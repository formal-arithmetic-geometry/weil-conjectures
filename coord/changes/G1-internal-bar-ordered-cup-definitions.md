# CategoryTheory.CondensedBar.OrderedCup ordered-cup definitions

## Reason

The proof needs independent lemmas whose statements use the fixed cup and bar
comparison arrows. Keeping those definitions in the theorem module would create
an import cycle. Move all fourteen definitions verbatim to the new module
`Sheaf.CategoryTheory.InternalBarOrderedCupCore` and publicly import that module
from the original item. Existing public imports, names, visibility, signatures,
attributes, and definition bodies are preserved. No target statement or definition
meaning changes. There are no new instances or elaboration attributes.

## Old

In `Sheaf.CategoryTheory.InternalBarOrderedCup`, inside the existing exposed public
noncomputable section:

```lean
/-- The regular coefficient in the cup calculus's ordinary derived category.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def regularZero (A : CondensedBar.Ring.{u}) :=
  (DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)

/-- The source A[-q].
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def degreeSource (A : CondensedBar.Ring.{u}) (q : ℕ) :=
  (regularZero A)⟦(-(q : ℤ))⟧

/-- Multiplication of an object identified with the tensor unit, abstractly.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def unitMultiply {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {U : C} (e : 𝟙_ C ≅ U) : U ⊗ U ≅ U :=
  tensorIso e.symm (Iso.refl _) ≪≫ λ_ U

/-- Assemble the ordered source convention without unfolding the condensed tensor.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def assembleSource {C : Type v} [Category.{w} C] [MonoidalCategory C]
    (D : ℕ → C) (e : D 0 ≅ 𝟙_ C) (s : ∀ q : ℕ, D (q + 1) ≅ D 1 ⊗ D q) :
    ∀ q : ℕ, D q ≅ tensorPower (D 1) q
  | 0 => e
  | q + 1 => s q ≪≫ tensorIso (Iso.refl _) (assembleSource D e s q)

/-- Assemble the fixed convention in an abstract monoidal category with shifts.
The supplied two-variable comparison is used without permutations; in length zero
use the unit and the zero-shift isomorphism.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def assembleShiftedSource {D : Type v} [Category.{w} D] [MonoidalCategory D]
    [HasShift D ℤ] (U : D) (e : 𝟙_ D ≅ U)
    (s : ∀ a b : ℤ, U⟦a⟧ ⊗ U⟦b⟧ ≅ (U ⊗ U)⟦a + b⟧) (q : ℕ) :
    U⟦-(q : ℤ)⟧ ≅ tensorPower (U⟦(-1 : ℤ)⟧) q :=
  assembleSource (fun n : ℕ ↦ U⟦-(n : ℤ)⟧)
    ((shiftFunctorZero' D (0 : ℤ) rfl).app U ≪≫ e.symm)
    (fun n ↦
      (eqToIso (congrArg (fun k : ℤ ↦ U⟦k⟧) (by omega)) :
        U⟦-((n + 1 : ℕ) : ℤ)⟧ ≅ U⟦(-1 : ℤ) + -(n : ℤ)⟧) ≪≫
      ((shiftFunctor D ((-1 : ℤ) + -(n : ℤ))).mapIso (unitMultiply e)).symm ≪≫
      (s (-1 : ℤ) (-(n : ℤ))).symm) q

/-- The fixed right-associated shift convention, including the empty tensor unit.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def sourceTensor (A : CondensedBar.Ring.{u}) (q : ℕ) :
    degreeSource A q ≅ tensorPower (degreeSource A 1) q :=
  assembleShiftedSource (regularZero A) (baseUnitIso A)
    (DerivedCategory.shiftTensorShiftIso (Modules A) (regularZero A) (regularZero A)) q

/-- Tensor a list of arrows in order, without unfolding the concrete tensor construction.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def tensorList {C : Type v} [Category.{w} C] [MonoidalCategory C] {X Y : C} :
    ∀ (q : ℕ) (_f : Fin q → (X ⟶ Y)), tensorPower X q ⟶ tensorPower Y q
  | 0, _ => 𝟙 _
  | q + 1, f => f 0 ⊗ₘ tensorList q (fun i ↦ f i.succ)

variable {A : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The actual unital ordered derived cup with the fixed shift convention.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def characterCup (q : ℕ) (a : Fin q → Character A G) :
    degreeSource A q ⟶ cohomology A G :=
  (sourceTensor A q).hom ≫ tensorList q (fun k ↦ characterClass (a k)) ≫
    orderedProduct (cupUnit (A := A) (G := G)) (cup (A := A) (G := G)) q

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The underived inhomogeneous bar for the trivial regular coefficient.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
abbrev underived {F : InternalFunctions A} (B : BarDiagram (G := G) F) :=
  (cochains B).obj (regularTrivial A G)

/-- The compatible nonnegative derived total on an equivariant injective resolution.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
abbrev resolved {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (I : InjectiveResolution (regularTrivial A G)) :=
  (totalCochains B).obj I.cocomplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution-normalized augmentation in the cup calculus's small-Hom localization.
This maps the resolution augmentation, inverts the computation unit on injectives,
and applies the total augmentation, exactly as `Computation.normalization`.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def augmentationArrow {F : InternalFunctions A} {B : BarDiagram (G := G) F}
    {a : Augmentation (invariants A G) B}
    (t : TotalAugmentation (invariants A G) B a)
    (I : InjectiveResolution (regularTrivial A G)) :
    cohomology A G ⟶ DerivedCategory.Q.obj (extend (resolved B I)) := by
  letI : QuasiIso I.ι' := inferInstance
  letI : I.cochainComplex.IsKInjective := by
    dsimp only [InjectiveResolution.cochainComplex]
    infer_instance
  exact (derived A G).map (DerivedCategory.Q.map I.ι') ≫
    ((invariants A G).functor.rightDerivedFunctorObjQIso I.cochainComplex).hom ≫
    DerivedCategory.Q.map
      (HomologicalComplex.mapExtendIso I.cocomplex ComplexShape.embeddingUpNat
        (invariants A G).functor).hom ≫
    DerivedCategory.Q.map (HomologicalComplex.extendMap (t.map.app I.cocomplex)
      ComplexShape.embeddingUpNat)

/-- The canonical total comparison is fixed by the resolution map into bidegree (n,0).
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def IsUnderivedComparison {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (I : InjectiveResolution (regularTrivial A G))
    (j : underived B ⟶ resolved B I) : Prop :=
  ∀ n : ℕ, j.f n = (B.diagram.map (I.ι.f 0)).app (SimplexCategory.mk n) ≫
    (doubleComplex B I.cocomplex).ιTotal (.up ℕ) n 0 n (by simp)

/-- The cocycle formula on every generalized section. Linearity and evaluation at the
regular unit determine the whole internal map, with empty product 1 for q=0.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def IsCharacterCocycle {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (q : ℕ) (a : Fin q → Character A G)
    (c : (HomologicalComplex.single (Modules A) (.up ℤ) (q : ℤ)).obj
      (Mod.regular A.X) ⟶ extend (underived B)) : Prop :=
  ∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : Fin q → C(T, G)),
    (F.evaluate (power G q) S (Mod.regular A.X)
      (((HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ) (Mod.regular A.X)).inv ≫
        c.f (q : ℤ) ≫ ((underived B).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        (B.term (regularTrivial A G) q).hom).hom.hom.app (op S)
          (1 : sectionRing A S))).val T f (tupleMap g) =
      ∏ k : Fin q, (a k).app T (g k)

/-- The actual localized cocycle followed by the actual total comparison, with source A[-q].
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def cocycleArrow {F : InternalFunctions A} {B : BarDiagram (G := G) F}
    {I : InjectiveResolution (regularTrivial A G)}
    (j : underived B ⟶ resolved B I) (q : ℕ)
    (c : (HomologicalComplex.single (Modules A) (.up ℤ) (q : ℤ)).obj
      (Mod.regular A.X) ⟶ extend (underived B)) :
    degreeSource A q ⟶ DerivedCategory.Q.obj (extend (resolved B I)) :=
  ((DerivedCategory.singleFunctors (Modules A)).shiftIso (-(q : ℤ)) (q : ℤ) 0
    (by omega)).hom.app (Mod.regular A.X) ≫
      DerivedCategory.Q.map c ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap j ComplexShape.embeddingUpNat)

```

## New

Exactly the same declarations and bodies above, verbatim, in
`Sheaf.CategoryTheory.InternalBarOrderedCupCore`. The item publicly imports the
new module, retaining every original public import and reexporting all names.

```lean
public import Sheaf.CategoryTheory.InternalBarOrderedCupCore
```

The unchanged declarations in the new module are:

```lean
/-- The regular coefficient in the cup calculus's ordinary derived category.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def regularZero (A : CondensedBar.Ring.{u}) :=
  (DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)

/-- The source A[-q].
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def degreeSource (A : CondensedBar.Ring.{u}) (q : ℕ) :=
  (regularZero A)⟦(-(q : ℤ))⟧

/-- Multiplication of an object identified with the tensor unit, abstractly.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def unitMultiply {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {U : C} (e : 𝟙_ C ≅ U) : U ⊗ U ≅ U :=
  tensorIso e.symm (Iso.refl _) ≪≫ λ_ U

/-- Assemble the ordered source convention without unfolding the condensed tensor.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def assembleSource {C : Type v} [Category.{w} C] [MonoidalCategory C]
    (D : ℕ → C) (e : D 0 ≅ 𝟙_ C) (s : ∀ q : ℕ, D (q + 1) ≅ D 1 ⊗ D q) :
    ∀ q : ℕ, D q ≅ tensorPower (D 1) q
  | 0 => e
  | q + 1 => s q ≪≫ tensorIso (Iso.refl _) (assembleSource D e s q)

/-- Assemble the fixed convention in an abstract monoidal category with shifts.
The supplied two-variable comparison is used without permutations; in length zero
use the unit and the zero-shift isomorphism.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def assembleShiftedSource {D : Type v} [Category.{w} D] [MonoidalCategory D]
    [HasShift D ℤ] (U : D) (e : 𝟙_ D ≅ U)
    (s : ∀ a b : ℤ, U⟦a⟧ ⊗ U⟦b⟧ ≅ (U ⊗ U)⟦a + b⟧) (q : ℕ) :
    U⟦-(q : ℤ)⟧ ≅ tensorPower (U⟦(-1 : ℤ)⟧) q :=
  assembleSource (fun n : ℕ ↦ U⟦-(n : ℤ)⟧)
    ((shiftFunctorZero' D (0 : ℤ) rfl).app U ≪≫ e.symm)
    (fun n ↦
      (eqToIso (congrArg (fun k : ℤ ↦ U⟦k⟧) (by omega)) :
        U⟦-((n + 1 : ℕ) : ℤ)⟧ ≅ U⟦(-1 : ℤ) + -(n : ℤ)⟧) ≪≫
      ((shiftFunctor D ((-1 : ℤ) + -(n : ℤ))).mapIso (unitMultiply e)).symm ≪≫
      (s (-1 : ℤ) (-(n : ℤ))).symm) q

/-- The fixed right-associated shift convention, including the empty tensor unit.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def sourceTensor (A : CondensedBar.Ring.{u}) (q : ℕ) :
    degreeSource A q ≅ tensorPower (degreeSource A 1) q :=
  assembleShiftedSource (regularZero A) (baseUnitIso A)
    (DerivedCategory.shiftTensorShiftIso (Modules A) (regularZero A) (regularZero A)) q

/-- Tensor a list of arrows in order, without unfolding the concrete tensor construction.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def tensorList {C : Type v} [Category.{w} C] [MonoidalCategory C] {X Y : C} :
    ∀ (q : ℕ) (_f : Fin q → (X ⟶ Y)), tensorPower X q ⟶ tensorPower Y q
  | 0, _ => 𝟙 _
  | q + 1, f => f 0 ⊗ₘ tensorList q (fun i ↦ f i.succ)

variable {A : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The actual unital ordered derived cup with the fixed shift convention.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def characterCup (q : ℕ) (a : Fin q → Character A G) :
    degreeSource A q ⟶ cohomology A G :=
  (sourceTensor A q).hom ≫ tensorList q (fun k ↦ characterClass (a k)) ≫
    orderedProduct (cupUnit (A := A) (G := G)) (cup (A := A) (G := G)) q

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The underived inhomogeneous bar for the trivial regular coefficient.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
abbrev underived {F : InternalFunctions A} (B : BarDiagram (G := G) F) :=
  (cochains B).obj (regularTrivial A G)

/-- The compatible nonnegative derived total on an equivariant injective resolution.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
abbrev resolved {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (I : InjectiveResolution (regularTrivial A G)) :=
  (totalCochains B).obj I.cocomplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution-normalized augmentation in the cup calculus's small-Hom localization.
This maps the resolution augmentation, inverts the computation unit on injectives,
and applies the total augmentation, exactly as `Computation.normalization`.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def augmentationArrow {F : InternalFunctions A} {B : BarDiagram (G := G) F}
    {a : Augmentation (invariants A G) B}
    (t : TotalAugmentation (invariants A G) B a)
    (I : InjectiveResolution (regularTrivial A G)) :
    cohomology A G ⟶ DerivedCategory.Q.obj (extend (resolved B I)) := by
  letI : QuasiIso I.ι' := inferInstance
  letI : I.cochainComplex.IsKInjective := by
    dsimp only [InjectiveResolution.cochainComplex]
    infer_instance
  exact (derived A G).map (DerivedCategory.Q.map I.ι') ≫
    ((invariants A G).functor.rightDerivedFunctorObjQIso I.cochainComplex).hom ≫
    DerivedCategory.Q.map
      (HomologicalComplex.mapExtendIso I.cocomplex ComplexShape.embeddingUpNat
        (invariants A G).functor).hom ≫
    DerivedCategory.Q.map (HomologicalComplex.extendMap (t.map.app I.cocomplex)
      ComplexShape.embeddingUpNat)

/-- The canonical total comparison is fixed by the resolution map into bidegree (n,0).
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def IsUnderivedComparison {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (I : InjectiveResolution (regularTrivial A G))
    (j : underived B ⟶ resolved B I) : Prop :=
  ∀ n : ℕ, j.f n = (B.diagram.map (I.ι.f 0)).app (SimplexCategory.mk n) ≫
    (doubleComplex B I.cocomplex).ιTotal (.up ℕ) n 0 n (by simp)

/-- The cocycle formula on every generalized section. Linearity and evaluation at the
regular unit determine the whole internal map, with empty product 1 for q=0.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def IsCharacterCocycle {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (q : ℕ) (a : Fin q → Character A G)
    (c : (HomologicalComplex.single (Modules A) (.up ℤ) (q : ℤ)).obj
      (Mod.regular A.X) ⟶ extend (underived B)) : Prop :=
  ∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : Fin q → C(T, G)),
    (F.evaluate (power G q) S (Mod.regular A.X)
      (((HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ) (Mod.regular A.X)).inv ≫
        c.f (q : ℤ) ≫ ((underived B).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        (B.term (regularTrivial A G) q).hom).hom.hom.app (op S)
          (1 : sectionRing A S))).val T f (tupleMap g) =
      ∏ k : Fin q, (a k).app T (g k)

/-- The actual localized cocycle followed by the actual total comparison, with source A[-q].
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def cocycleArrow {F : InternalFunctions A} {B : BarDiagram (G := G) F}
    {I : InjectiveResolution (regularTrivial A G)}
    (j : underived B ⟶ resolved B I) (q : ℕ)
    (c : (HomologicalComplex.single (Modules A) (.up ℤ) (q : ℤ)).obj
      (Mod.regular A.X) ⟶ extend (underived B)) :
    degreeSource A q ⟶ DerivedCategory.Q.obj (extend (resolved B I)) :=
  ((DerivedCategory.singleFunctors (Modules A)).shiftIso (-(q : ℤ)) (q : ℤ) 0
    (by omega)).hom.app (Mod.regular A.X) ≫
      DerivedCategory.Q.map c ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap j ComplexShape.embeddingUpNat)

```

## Users

The current repository has zero direct or transitive Lean importers of the item
(`tools/downstream.py`, 2026-10-26). Its DAG parents remain intact: lack of current
Lean imports is not treated as a withdrawal. A name search finds `characterCup`
only in the item itself. The new delivery consumers are:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InternalBarOrderedCup | G1 | Same definitions reexported; complete assembly proof. |
| Sheaf.CategoryTheory.InternalBarSmallHomComparison | G1, new | Imports the fixed arrows for its generic comparison. |
| Sheaf.CategoryTheory.InternalBarCupBracketing | G1, new | Imports the fixed tensor cup for its bracketing comparison. |
| Sheaf.CategoryTheory.InternalBarOrderedCupCore | G1, new | Contains exactly the fourteen moved definitions. |

## Status

landed 20261026T081842-L-2089288 2026-10-26 (merge of deliver/G1/Sheaf.CategoryTheory.InternalBarOrderedCup)
