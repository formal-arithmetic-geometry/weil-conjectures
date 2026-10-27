# Affine dualizing coefficient comparison and assertion interfaces

## Reason

The proof repeatedly compares generic monoidal and shift instances with concrete
coefficient-category instances. Kernel checking the Tate-normalization helper took
about 15 seconds with the repeated shift construction; reusing the existing named
scalar-shift comparison reduced this to about 8 seconds in the first diagnostic.
The unit comparison likewise reuses the existing irreducible finite-coefficient
single/unit interface. Both replacements unfold to exactly the original maps.
The module remains one file; no proof was split into another delivery module.

The nested eight-clause conclusion of `AffineDualizingCoefficientAssertion` also
caused a large kernel conversion: the diagnostic full finite-ring assembly spent
34.9 seconds checking that proof, while a version with named structure fields checks
in under a second. `AffineDualizingCoefficientConclusions` stores exactly the same
eight propositions as fields; `AffineDualizingCoefficientAssertion` retains its four
original premises and concludes that structure. This is a representation change of
an equivalent proposition, with no added hypotheses or weakened clauses. It keeps
the proof in one module and does not raise the compilation limit.

## Old

```lean
@[irreducible] def affineDualizingUnitIso
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    ordinaryFiniteUnit A S ≅ 𝟙_ (DerivedCategoryModule A S) :=
  singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S

@[irreducible] def affineDualizingShiftedSingleMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (c : (ProEtale.etaleSheafExtendScalars φ T).obj F ⟶ G) (d : ℤ) :
    (scalarExtension φ T).obj (((_root_.DerivedCategory.singleFunctor _ 0).obj F)⟦d⟧) ⟶
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G)⟦d⟧ :=
  letI : (scalarExtension φ T).CommShift ℤ :=
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).leftAdjointCommShift ℤ
  ((scalarExtension φ T).commShiftIso d).hom.app _ ≫
    (shiftFunctor _ d).map
      (WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T F ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map c)
```

```lean
@[irreducible] def AffineDualizingCoefficientAssertion
    (l : ℕ) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) : Prop :=
  DerivedCategory.isBoundedConstructible A (affineTraceTower S r)
      (dualizingComplex (ModuleCat.{u + 1} A) (affineTraceProjection S r)) →
  (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A (affineTraceTower S r) a b
      (dualizingComplex (ModuleCat.{u + 1} A) (affineTraceProjection S r))) →
  DerivedCategory.isBoundedConstructible B (affineTraceTower S r)
      (dualizingComplex (ModuleCat.{u + 1} B) (affineTraceProjection S r)) →
  (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn B (affineTraceTower S r) a b
      (dualizingComplex (ModuleCat.{u + 1} B) (affineTraceProjection S r))) →
  IsIso (ExceptionalCoefficients.compactSupportMap φ
    (HasCompactification.compactification (affineTraceProjection S r))
    (dualizingComplex (ModuleCat.{u + 1} A) (affineTraceProjection S r))) ∧
  IsIso (ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r)) ∧
  AffineDualizingMateEquation φ S r
    (ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r)) ∧
  (∀ v, AffineDualizingMateEquation φ S r v →
    v = ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r)) ∧
  IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
    (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule A S))) ∧
  IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B)
    (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule B S))) ∧
  (∃ (e : ℕ) (hA : ((l ^ e : ℕ) : A) = 0) (hB : ((l ^ e : ℕ) : B) = 0)
      (hS : IsUnit ((l ^ e : ℕ) : Γ(S, ⊤)))
      (tA : OrdinaryFiniteTwistTransport A (l ^ e) hA)
      (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((l ^ e : ℕ) : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum A (l ^ e) hA tA T hT)
      (tB : OrdinaryFiniteTwistTransport B (l ^ e) hB)
      (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((l ^ e : ℕ) : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum B (l ^ e) hB tB T hT),
    AffineDualizingTraceNormalization A S (l ^ e) hA hS r tA DA ∧
    AffineDualizingTraceNormalization B S (l ^ e) hB hS r tB DB ∧
    Nonempty ((affineTraceRight A (l ^ e) hA S r).obj (ordinaryFiniteUnit A S) ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) A hA r))
          ⟦2 * (r : ℤ)⟧) ∧
    Nonempty ((affineTraceRight B (l ^ e) hB S r).obj (ordinaryFiniteUnit B S) ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) B hB r))
          ⟦2 * (r : ℤ)⟧) ∧
    ∃ c : ∀ d : ℕ,
      (ProEtale.etaleSheafExtendScalars φ (affineTraceTower S r)).obj
        (Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) A hA d) ≅
          Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) B hB d,
      AffineDualizingTateNormalization φ (affineTraceTower S r) (l ^ e) hA hB c ∧
      IsIso (affineDualizingShiftedSingleMap φ (affineTraceTower S r) (c r).hom
        (2 * (r : ℤ)))) ∧
  (r = 0 →
    (ExceptionalCoefficients.unitIso φ S).inv ≫
        (scalarExtension φ S).map (affineDualizingZeroIso A S).inv ≫
        ExceptionalCoefficients.dualizingScalarMap φ (𝟙 S) ≫
        (affineDualizingZeroIso B S).hom = 𝟙 (𝟙_ (DerivedCategoryModule B S)))
```

## New

```lean
@[irreducible] def affineDualizingUnitIso
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    ordinaryFiniteUnit A S ≅ 𝟙_ (DerivedCategoryModule A S) :=
  AffineIntegrationCoefficient.ordinaryUnitIso A S

@[irreducible] def affineDualizingShiftedSingleMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (c : (ProEtale.etaleSheafExtendScalars φ T).obj F ⟶ G) (d : ℤ) :
    (scalarExtension φ T).obj (((_root_.DerivedCategory.singleFunctor _ 0).obj F)⟦d⟧) ⟶
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G)⟦d⟧ :=
  (FiniteSmoothPurity.scalarShiftIso φ T d).hom.app _ ≫
    (shiftFunctor _ d).map
      (WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T F ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map c)
```

```lean
structure AffineDualizingCoefficientConclusions
    (l : ℕ) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) : Prop where
  compactSupport_isIso :
    IsIso (ExceptionalCoefficients.compactSupportMap φ
      (HasCompactification.compactification (affineTraceProjection S r))
      (dualizingComplex (ModuleCat.{u + 1} A) (affineTraceProjection S r)))
  dualizing_isIso :
    IsIso (ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r))
  mate_equation :
    AffineDualizingMateEquation φ S r
      (ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r))
  mate_unique :
    (∀ v, AffineDualizingMateEquation φ S r v →
      v = ExceptionalCoefficients.dualizingScalarMap φ (affineTraceProjection S r))
  counitA_isIso :
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule A S)))
  counitB_isIso :
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B)
      (affineTraceProjection S r)).counit.app (𝟙_ (DerivedCategoryModule B S)))
  trace_normalization :
    (∃ (e : ℕ) (hA : ((l ^ e : ℕ) : A) = 0) (hB : ((l ^ e : ℕ) : B) = 0)
        (hS : IsUnit ((l ^ e : ℕ) : Γ(S, ⊤)))
        (tA : OrdinaryFiniteTwistTransport A (l ^ e) hA)
        (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((l ^ e : ℕ) : Γ(T, ⊤))),
          OrdinaryFiniteP1Datum A (l ^ e) hA tA T hT)
        (tB : OrdinaryFiniteTwistTransport B (l ^ e) hB)
        (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((l ^ e : ℕ) : Γ(T, ⊤))),
          OrdinaryFiniteP1Datum B (l ^ e) hB tB T hT),
      AffineDualizingTraceNormalization A S (l ^ e) hA hS r tA DA ∧
      AffineDualizingTraceNormalization B S (l ^ e) hB hS r tB DB ∧
      Nonempty ((affineTraceRight A (l ^ e) hA S r).obj (ordinaryFiniteUnit A S) ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) A hA r))
            ⟦2 * (r : ℤ)⟧) ∧
      Nonempty ((affineTraceRight B (l ^ e) hB S r).obj (ordinaryFiniteUnit B S) ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) B hB r))
            ⟦2 * (r : ℤ)⟧) ∧
      ∃ c : ∀ d : ℕ,
        (ProEtale.etaleSheafExtendScalars φ (affineTraceTower S r)).obj
          (Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) A hA d) ≅
            Scheme.finiteEtaleTateTwist (affineTraceTower S r) (l ^ e) B hB d,
        AffineDualizingTateNormalization φ (affineTraceTower S r) (l ^ e) hA hB c ∧
        IsIso (affineDualizingShiftedSingleMap φ (affineTraceTower S r) (c r).hom
          (2 * (r : ℤ))))
  zero_normalization :
    (r = 0 →
      (ExceptionalCoefficients.unitIso φ S).inv ≫
          (scalarExtension φ S).map (affineDualizingZeroIso A S).inv ≫
          ExceptionalCoefficients.dualizingScalarMap φ (𝟙 S) ≫
          (affineDualizingZeroIso B S).hom = 𝟙 (𝟙_ (DerivedCategoryModule B S)))

/-- All clauses of affine-space coefficient reduction, on the actual ordinary etale
categories. The two finiteness premises have exactly the bounded constructible and
ordered finite-Tor-interval meaning in the node. The final equation is the literal
identity of B_s in identity-adjunction coordinates, without identifying chosen adjoints
definitionally. Source: blueprint affine-space reduction, statement
(blueprint: lem-coef-dualizing-affine-space). -/
@[irreducible] def AffineDualizingCoefficientAssertion
    (l : ℕ) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) : Prop :=
  DerivedCategory.isBoundedConstructible A (affineTraceTower S r)
      (dualizingComplex (ModuleCat.{u + 1} A) (affineTraceProjection S r)) →
  (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A (affineTraceTower S r) a b
      (dualizingComplex (ModuleCat.{u + 1} A) (affineTraceProjection S r))) →
  DerivedCategory.isBoundedConstructible B (affineTraceTower S r)
      (dualizingComplex (ModuleCat.{u + 1} B) (affineTraceProjection S r)) →
  (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn B (affineTraceTower S r) a b
      (dualizingComplex (ModuleCat.{u + 1} B) (affineTraceProjection S r))) →
  AffineDualizingCoefficientConclusions l φ S r
```

Unfolding `AffineIntegrationCoefficient.ordinaryUnitIso` recovers the original
unit comparison. Unfolding `FiniteSmoothPurity.scalarShiftIso` and `ordinaryScalar`
recovers the original adjunction-induced CommShift and its component. All original
signatures and attributes are preserved. No object, counit, shift sign or generator
normalization changes. The two owning modules are now public imports because the
public definitions use their interfaces.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.AffineDualizingCoefficient | C3 | Uses the identical named comparison interfaces. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | G2 | Sole downstream module; only uses affineDualizingTowerComparison, whose definition is unchanged. No adaptation. |

`tools/downstream.py ... --uses affineDualizingShiftedSingleMap affineDualizingUnitIso`
reports no external declaration users. The same check for
`AffineDualizingCoefficientAssertion` likewise reports only this item module. The sole downstream module was read: its
only two uses of this module's declarations are of the unchanged tower comparison.
A two-file compile checked the item and that unchanged consumer successfully
against the sandbox output; its byte-identical diagnostic copy was then removed.
The unit and shift maps are definitionally unchanged. The assertion is logically
equivalent: its eight old conjuncts are exactly the eight structure fields, with
constructor and projections giving both directions. Its signature is unchanged.
No target declaration or mathematical target meaning changes; the assertion
representation change is explicitly submitted for the independent semantic review. No source-library file is changed and no forced adaptation is needed.

## Status

landed 20261025T142927-L-853118 2026-10-25 (merge of deliver/C3/Sheaf.SixFunctors.AffineDualizingCoefficient)
