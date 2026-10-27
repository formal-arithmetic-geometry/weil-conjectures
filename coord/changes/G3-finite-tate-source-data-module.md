# Finite Tate scalar source data module

## Reason

Separate the construction/existence assertion from the independent flat-single computation
and uniqueness proof. The existence theorem and the parent both need the specified arrows
and predicates, so those definitions need an independent API module to avoid an import cycle.
The original module publicly reexports that API. All original definition bodies, signatures,
visibility and universes are preserved verbatim; no chosen witness defines data.

The new data module drops four inherited private proof imports, which its
statements and definition bodies do not use. Its already-defined scalar/source
maps are locally irreducible while elaborating later predicates, preventing
unnecessary expansion of their terms. These local annotations do not change any
exported attribute, signature, or definition body. They respond to a 65-second
dry-run rejection; the standalone profile attributed the cost to type checking
and linting rather than proof elaboration.

## Old

The following declarations were in `Sheaf.Paper.FiniteTateScalarSourceNormalization`:

```lean
/-- Place the existing ordinary Tate sheaf in degree zero and shift by its even degree.
Source: sk-prop-an, paragraph 2
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
abbrev finiteTateScalarObject (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (r : ℕ) : Etale.DerivedCategoryModule A T :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateTwist T N A hA r))⟦2 * (r : ℤ)⟧

/-- The zero twist's specified single/unit and zero-shift identifications.
Source: sk-prop-an, paragraph 2 and Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def finiteTateScalarZeroIso (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) :
    finiteTateScalarObject A N hA T 0 ≅ 𝟙_ (Etale.DerivedCategoryModule A T) :=
  (shiftFunctorZero _ ℤ).app _ ≪≫
    Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T

/-- Shift the actual scalar/single adjunct and then apply the given ordinary balancing.
Source: Stacks 06YY, 07A6; sk-prop-an, paragraph 2
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def finiteTateScalarLineMap (φ : A →+* B) (N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (T : Scheme.{u}) (r : ℕ)
    (β : (Etale.purityScalarSheaf φ T).obj (Scheme.finiteEtaleTateTwist T N A hA r) ≅
      Scheme.finiteEtaleTateTwist T N B hB r) :
    (Etale.purityScalarExtension φ T).obj (finiteTateScalarObject A N hA T r) ⟶
      finiteTateScalarObject B N hB T r :=
  (Etale.FiniteSmoothPurity.scalarShiftIso φ T (2 * (r : ℤ))).hom.app _ ≫
    (purityScalarSingleMap φ T (Scheme.finiteEtaleTateTwist T N A hA r) ≫
      (DerivedCategory.singleFunctor _ 0).map β.hom)⟦2 * (r : ℤ)⟧'

/-- The specified source arrow: scalar tensorator, scalar/pullback comparison, then line.
Source: Stacks 07A4; sk-prop-an, paragraph 2
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def finiteTateScalarSourceMap (φ : A →+* B) (N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : ℕ)
    (β : (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
      Scheme.finiteEtaleTateTwist X N B hB r) (K : Etale.DerivedCategoryModule A Y) :
    (Etale.purityScalarExtension φ X).obj
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K ⊗
          finiteTateScalarObject A N hA X r) ⟶
      L(Etale.upperStar (ModuleCat.{u + 1} B) f).obj
          ((Etale.purityScalarExtension φ Y).obj K) ⊗ finiteTateScalarObject B N hB X r :=
  (Etale.purityScalarTensor φ X _ _).hom ≫
    ((Etale.purityScalarPullback φ f).hom.app K ⊗ₘ
      finiteTateScalarLineMap φ N hA hB X r β)

/-- Generator, zero-power and ordinary tensor-power normalization.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarBalancing
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
      (∀ (r : ℕ) (U : X.Etaleᵒᵖ) (a : A) (b : B)
          (z : Fin r → (X.rootsOfUnitySheaf N).obj.obj U),
        ((β r).hom.hom.app U)
            (b • @id (((Etale.purityScalarSheaf φ X).obj
              (Scheme.finiteEtaleTateTwist X N A hA r)).obj.obj U)
              (((Etale.purityScalarSheafAdjunction φ X).unit.app
                (Scheme.finiteEtaleTateTwist X N A hA r)).hom.app U
                  (Scheme.finiteTateEtalePowerGenerator X A N hA U a r z))) =
          Scheme.finiteTateEtalePowerGenerator X B N hB U (φ a * b) r z) ∧
      ((β 0).hom = Functor.OplaxMonoidal.η (Etale.purityScalarSheaf φ X)) ∧
      (∀ r : ℕ, (β (r + 2)).hom =
        Functor.OplaxMonoidal.δ (Etale.purityScalarSheaf φ X)
          (Scheme.finiteEtaleTateTwist X N A hA (r + 1))
          (Scheme.finiteEtaleTateTwist X N A hA 1) ≫
            ((β (r + 1)).hom ⊗ₘ (β 1).hom))

/-- Single/unit and shifted-line invertibility and zero-power normalization.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarLineNormalized
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
      (purityScalarSingleMap φ X (𝟙_ _) ≫
        (DerivedCategory.singleFunctor _ 0).map (β 0).hom = purityScalarUnitMap φ X) ∧
      (∀ r : ℕ, IsIso (finiteTateScalarLineMap φ N hA hB X r (β r))) ∧
      (finiteTateScalarLineMap φ N hA hB X 0 (β 0) ≫
          (finiteTateScalarZeroIso B N hB X).hom =
        (Etale.purityScalarExtension φ X).map (finiteTateScalarZeroIso A N hA X).hom ≫
          (Etale.ExceptionalCoefficients.unitIso φ X).hom)

/-- Invertibility of the specified source comparison on every unbounded input.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarSourceInvertible
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
      (∀ (Y : Scheme.{u}) (_hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
          (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A Y) (r : ℕ),
        IsIso (finiteTateScalarSourceMap φ N hA hB f r (β r) K))

/-- The left-unit diagram, with functor endpoints shared before site specialization.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarLeftUnitEquation
    {C : Type v₁} {D : Type v₂} {E : Type v₃} {F : Type v₄}
    [Category.{w₁} C] [Category.{w₂} D] [Category.{w₃} E] [Category.{w₄} F]
    [MonoidalCategory C] [MonoidalCategory D]
    (Q : C ⥤ D) (R : E ⥤ F) (P : E ⥤ C) (P' : F ⥤ D)
    (U : E) (U' : F) (L : C) (L' : D)
    (s : Q.obj (P.obj U ⊗ L) ⟶ P'.obj (R.obj U) ⊗ L')
    (q : R.obj U ⟶ U') (p : P.obj U ⟶ 𝟙_ C) (p' : P'.obj U' ⟶ 𝟙_ D)
    (l : Q.obj L ⟶ L') : Prop :=
  s ≫ ((P'.map q ≫ p') ▷ L') ≫ (λ_ L').hom =
    Q.map ((p ▷ L) ≫ (λ_ L).hom) ≫ l

/-- The right-unit diagram, with functor endpoints shared before site specialization.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarRightUnitEquation
    {C : Type v₁} {D : Type v₂} {E : Type v₃} {F : Type v₄}
    [Category.{w₁} C] [Category.{w₂} D] [Category.{w₃} E] [Category.{w₄} F]
    [MonoidalCategory C] [MonoidalCategory D]
    (Q : C ⥤ D) (R : E ⥤ F) (P : E ⥤ C) (P' : F ⥤ D)
    (K : E) (L : C) (L' : D)
    (s : Q.obj (P.obj K ⊗ L) ⟶ P'.obj (R.obj K) ⊗ L')
    (e : L ≅ 𝟙_ C) (e' : L' ≅ 𝟙_ D)
    (c : Q.obj (P.obj K) ⟶ P'.obj (R.obj K)) : Prop :=
  s ≫ (P'.obj (R.obj K) ◁ e'.hom) ≫ (ρ_ _).hom =
    Q.map ((P.obj K ◁ e.hom) ≫ (ρ_ _).hom) ≫ c

/-- The coefficient-unit source equation with its specified single/unit maps.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarSourceUnitNormalized
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
  ∀ (Y : Scheme.{u}) (_hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
      (f : X ⟶ Y) (r : ℕ),
    IsFiniteTateScalarLeftUnitEquation
      (Etale.purityScalarExtension φ X) (Etale.purityScalarExtension φ Y)
      L(Etale.upperStar (ModuleCat.{u + 1} A) f)
      L(Etale.upperStar (ModuleCat.{u + 1} B) f)
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))
      (finiteTateScalarObject A N hA X r) (finiteTateScalarObject B N hB X r)
      (finiteTateScalarSourceMap φ N hA hB f r (β r) _)
      (purityScalarUnitMap φ Y)
      (L(Etale.upperStar (ModuleCat.{u + 1} A) f).map
          (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom)
      (L(Etale.upperStar (ModuleCat.{u + 1} B) f).map
          (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} B) Y).hom ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) f).hom)
      (finiteTateScalarLineMap φ N hA hB X r (β r))

/-- The zero-power source equation with its specified right unitors.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarSourceZeroNormalized
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
  ∀ (Y : Scheme.{u}) (_hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
      (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A Y),
    IsFiniteTateScalarRightUnitEquation
      (Etale.purityScalarExtension φ X) (Etale.purityScalarExtension φ Y)
      L(Etale.upperStar (ModuleCat.{u + 1} A) f)
      L(Etale.upperStar (ModuleCat.{u + 1} B) f) K
      (finiteTateScalarObject A N hA X 0) (finiteTateScalarObject B N hB X 0)
      (finiteTateScalarSourceMap φ N hA hB f 0 (β 0) K)
      (finiteTateScalarZeroIso A N hA X) (finiteTateScalarZeroIso B N hB X)
      ((Etale.purityScalarPullback φ f).hom.app K)

```

## New

The declarations above are verbatim in `Sheaf.Paper.FiniteTateScalarSourceData`.
The original module adds `public import Sheaf.Paper.FiniteTateScalarSourceData`.
Its existing public imports and original theorem signature are retained.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | G3 | Publicly reexports identical data; proves flat-single comparison and uniqueness. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Original names, types and definitions remain public and identical. |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed | Original names, types and definitions remain public and identical. |
| Sheaf.Paper.FiniteTateScalarSourceExistence | new G3 | States only existence and compatibility, with no arbitrary data choice. |

## Status

landed 20261025T202103-L-2672233 2026-10-25 (merge of deliver/G3/Sheaf.Paper.FiniteTateScalarSourceNormalization)
