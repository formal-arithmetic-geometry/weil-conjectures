# AlgebraicGeometry.Etale.rawModuleClassMorphism

## Reason

Expose the actual derived Hom types of the existing raw Yoneda classes. This is a presentation
repair needed by the retirement of the coefficient-factor twin. With the canonical factor
import, the combined pullback statement alone exceeds 60 seconds even with a scratch sorry
proof. After exposing the class values explicitly, the same statement checks in 21.2 seconds.
No timeout is raised and no theorem is split into additional proof obligations.

The new functions return the supplied input z or x directly. The computation rule
rawModuleClassMorphism_heq is proved by rfl and is used to avoid repeating the carrier
conversion in congruence proofs. They construct no coefficient
object, comparison, witness or isomorphism. The raw presheaf carriers are definitionally the
displayed derived Hom types. Reading both inputs and outputs through these functions preserves
the original values and equations, including every zero, identity and degree case. The module
function accepts all integer degrees; the abelian function preserves the original natural
cohomological degree. All original binders and universe parameters stay verbatim.

The typed coefficient view constructs the two actual factors of the raw pullback coefficient
using the direct inverse-image functor. Its heterogeneous reflexivity rule proves that this
is the existing canonical factor; it introduces no new comparison or choice. No target statement or target-used definition changes. The existing raw functors, raw scalar
map, scalar-forgetting comparison and coefficient maps are untouched. The new data functions
have no sorry and use no existence theorem. All affected modules are unclaimed.

## Old

The identity views had no named API. Each equation implicitly converted raw presheaf values
to morphisms. The six original signatures were:

```lean
theorem rawModuleScalarHom_evaluate
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A : Over W)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A)) :
    rawModuleAbelianHomMap Λ k G q U A z =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map z ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ)
```

```lean
theorem rawModuleScalar_pullback_abelian_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B) :
    ∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B)).obj
        (op U)),
      abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G)) U x =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map x ≫
      abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
        (q : ℤ) A B f
```

```lean
theorem rawModuleScalar_pullback_formulas
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z ≫
        moduleCoefficientFactor Λ G (q : ℤ) A B f) ∧
    (∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B)).obj
        (op U)),
      abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G)) U x =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map x ≫
      abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
        (q : ℤ) A B f)
```

```lean
theorem rawModuleScalar_hom_composite_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawModuleAbelianHomMap Λ k G q U A
      ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleCoefficientFactor Λ G (q : ℤ) A B f) ≫
      scalarCoefficientFactor Λ A.hom G (q : ℤ)
```

```lean
theorem rawModuleAbelianHomMap_source_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawModuleAbelianHomMap Λ k G q U A
      ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      ((RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
          (((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦(q : ℤ)⟧) ≫
        (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
          (moduleCoefficientFactor Λ G (q : ℤ) A B f) ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ))
```

```lean
theorem rawModuleAbelianHomMap_target_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) q _ _
      ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
        (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G))
      U (rawModuleAbelianHomMap Λ k G q U B z) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
          (scalarCoefficientFactor Λ B.hom G (q : ℤ)) ≫
        abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
          (q : ℤ) A B f)
```

## New

The raw-class identity functions and the canonical coefficient view have these complete
constructions and computation rules. The coefficient view explicitly constructs the same
shift comparison and shifted coefficient map, using the direct inverse-image functor. Its
heterogeneous rule proves equality with the canonical factor. Its type names the same single
complexes using higherDirectImageRawOverComplex. Using that
type in the pullback formula reduces its statement-only diagnostic to 13.1 seconds. The three
module coefficient tails below use this view, preserving their actual morphisms.

```lean
/-- Read a module raw class as its existing derived morphism.
Source: Stacks Project, Tags 03FD and 03Q8; `higherDirectImageRawOverFunctor` and
`higherDirectImageRawOverComplex`.

Construction: the raw functor is the represented derived Hom presheaf. Its value at
`A` is definitionally this Hom type. Return the supplied class itself; no morphism,
comparison, coefficient object or choice is introduced. This includes every integer
shift, zero classes and identity geometric arrows.
(blueprint: def-sbc-raw-class-native-morphisms). -/
noncomputable def rawModuleClassMorphism
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale)
    (A : Over W)
    (z : (higherDirectImageRawOverFunctor Λ k G q U).obj (op A)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k)).obj ((freeSheaf Λ S).obj U)) ⟶
      (higherDirectImageRawOverComplex Λ G A)⟦q⟧ := z

/-- The native module view is the supplied class itself.
Source: Stacks Project, Tags 03FD and 03Q8; the raw Yoneda definition.
Proof: the function returns its input, so heterogeneous reflexivity proves the equation.
(blueprint: def-sbc-raw-class-native-morphisms). -/
theorem rawModuleClassMorphism_heq
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale)
    (A : Over W) (z : (higherDirectImageRawOverFunctor Λ k G q U).obj (op A)) :
    HEq (rawModuleClassMorphism Λ k G q U A z) z := by
  rfl

/-- Read an abelian raw class as its existing derived morphism.
Source: Stacks Project, Tags 03FD and 03Q8; `abelianHigherDirectImageRawPresheaf`.

Construction: unfold the represented raw presheaf and the concrete free abelian
represented sheaf. Its value is definitionally the displayed derived Hom group.
Return the supplied element itself. This introduces no new datum and applies in
all natural degrees, including zero, to zero classes and empty test schemes.
(blueprint: def-sbc-raw-class-native-morphisms). -/
noncomputable def rawAbelianClassMorphism
    {Y S : Scheme.{u}} (h : Y ⟶ S)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : S.Etale)
    (x : (abelianHigherDirectImageRawPresheaf h q G).obj (op U)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj
          (RawModuleScalarComparison.freeAbelian S U)) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)⟦(q : ℤ)⟧ := x
```

```lean
/-- The existing coefficient morphism with its named raw-complex endpoints.
Source: Stacks Project, Tag 03Q8; `moduleCoefficientFactor`.

Construction: use the coefficient part of the concrete raw triangle pullback: the
shift comparison followed by the shifted fixed coefficient morphism. Use the direct
inverse-image functor at the named raw complexes so these endpoints stay shared.
The following computation rule identifies this same composite with the canonical factor,
for every integer degree, including zero, and every Over arrow.
(blueprint: def-sbc-module-coefficient-native-endpoints). -/
noncomputable def moduleCoefficientFactorNative
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.obj
        ((higherDirectImageRawOverComplex Λ G B)⟦q⟧) ⟶
      (higherDirectImageRawOverComplex Λ G A)⟦q⟧ :=
  ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      (higherDirectImageRawOverComplex Λ G B) ≫
    (shiftFunctor _ q).map (higherDirectImageRawOverCoefficient Λ G f)

/-- The typed view is the canonical coefficient map itself.
Source: Stacks Project, Tag 03Q8; the preceding concrete definition.
Proof: unfold both concrete coefficient composites and the moduleUpperStar abbreviation;
heterogeneous reflexivity identifies their identical factors and endpoints.
(blueprint: def-sbc-module-coefficient-native-endpoints). -/
theorem moduleCoefficientFactorNative_heq
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    HEq (moduleCoefficientFactorNative Λ G q A B f)
      (moduleCoefficientFactor Λ G q A B f) := by
  rfl

/-- The explicit two-factor computation rule at the named raw-complex endpoints.
Source: Stacks Project, Tag 03Q8; the coefficient part of raw triangle pullback.
Proof: unfold the concrete definition; both sides are the identical composite.
(blueprint: def-sbc-module-coefficient-native-endpoints). -/
theorem moduleCoefficientFactorNative_eq
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    moduleCoefficientFactorNative Λ G q A B f =
  ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      (higherDirectImageRawOverComplex Λ G B) ≫
    (shiftFunctor _ q).map (higherDirectImageRawOverCoefficient Λ G f) := by
  rfl
```

The six equivalent public equations are:

```lean
theorem rawModuleScalarHom_evaluate
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A : Over W)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A)) :
    rawAbelianClassMorphism (A.hom ≫ k)
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
      (rawModuleAbelianHomMap Λ k G q U A z) =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (rawModuleClassMorphism Λ k G (q : ℤ) U A z) ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ)
```

```lean
theorem rawModuleScalar_pullback_abelian_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B) :
    ∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B)).obj
        (op U)),
      rawAbelianClassMorphism (A.hom ≫ k)
        (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
        (abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G)) U x) =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
        (rawAbelianClassMorphism (B.hom ≫ k)
          (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B) q U x) ≫
      abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
        (q : ℤ) A B f
```

```lean
theorem rawModuleScalar_pullback_formulas
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    (rawModuleClassMorphism Λ k G (q : ℤ) U A
      ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map
        (rawModuleClassMorphism Λ k G (q : ℤ) U B z) ≫
        moduleCoefficientFactorNative Λ G (q : ℤ) A B f) ∧
    (∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B)).obj
        (op U)),
      rawAbelianClassMorphism (A.hom ≫ k)
        (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
        (abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G)) U x) =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
        (rawAbelianClassMorphism (B.hom ≫ k)
          (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B) q U x) ≫
      abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
        (q : ℤ) A B f)
```

```lean
theorem rawModuleScalar_hom_composite_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawAbelianClassMorphism (A.hom ≫ k)
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
      (rawModuleAbelianHomMap Λ k G q U A
        ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z)) =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map
          (rawModuleClassMorphism Λ k G (q : ℤ) U B z)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleCoefficientFactorNative Λ G (q : ℤ) A B f) ≫
      scalarCoefficientFactor Λ A.hom G (q : ℤ)
```

```lean
theorem rawModuleAbelianHomMap_source_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawAbelianClassMorphism (A.hom ≫ k)
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
      (rawModuleAbelianHomMap Λ k G q U A
        ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z)) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      ((RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
          (((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦(q : ℤ)⟧) ≫
        (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
          (moduleCoefficientFactorNative Λ G (q : ℤ) A B f) ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ))
```

```lean
theorem rawModuleAbelianHomMap_target_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawAbelianClassMorphism (A.hom ≫ k)
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
      (abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) q _ _
      ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
        (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G))
      U (rawModuleAbelianHomMap Λ k G q U B z)) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
          (scalarCoefficientFactor Λ B.hom G (q : ℤ)) ≫
        abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
          (q : ℤ) A B f)
```

The pullback module calculation first uses higherDirectImageRawOverPullbackHom_apply to
evaluate the bundled raw map, then applies associativity to the existing factors. Its private
metaprogram constructs ordinary heterogeneous congruence proofs, using the proved native-class
computation rule and the existing raw-complex endpoint equations. All resulting terms are
checked by the kernel. The abelian component applies the existing abelian formula. The Hom
composite reuses these components; source and target formulas retain their existing arguments.

The six node statements now explicitly name these identity presentations, with complete
statement_change records and an audit of every existing citer. All uses remain valid by
identity of the values and the canonical coefficient comparison.

## Users

The downstream searches for rawModuleScalarHom_evaluate find the Hom composite and target
formula; the composite's user is the source formula. The combined pullback formula previously
had no Lean importer; it is now used directly by the Hom composite. The independent abelian
formula's users are the combined and target formulas. Source and target formulas have no
current Sheaf Lean importer; their DAG parents continue to use exactly the same mathematics.
The adopted upstream modules remain completely untouched. These are all users and adapted
modules; all are unclaimed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Explicitly present the same raw input/output values as derived morphisms; keep all binders and the equation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Explicitly present the same raw input/output values as derived morphisms; keep all binders and the equation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Explicitly present the same raw input/output values as derived morphisms; keep all binders and the equation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Explicitly present the same raw input/output values as derived morphisms; keep all binders and the equation. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Explicitly present the same raw input/output values as derived morphisms; keep all binders and the equation. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Explicitly present the same raw input/output values as derived morphisms; keep all binders and the equation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarClassMorphisms | V3 | New concrete identity functions; no proof hole or arbitrary witness. |

The mathematical statements of the six DAG nodes stay unchanged. Their Lean signature records
and statement dependencies identify the explicit identity views; their proof records describe
the actual calculations. The new definition node is def-sbc-raw-class-native-morphisms. The
unit sk-lem-failure-field's realized route is preserved.

The new RawModuleScalarCoefficientNative API is used in the public statements of
RawModuleScalarPullbackFormulas, RawModuleScalarHomCompositeFormula and
RawModuleAbelianHomSourceFormula. Its canonical underlying factor has the same seven
existing consumers listed in the retirement record.

## Status

landed 20261021T061739-L-1825145 2026-10-21 (merge of deliver/V3/Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors)
