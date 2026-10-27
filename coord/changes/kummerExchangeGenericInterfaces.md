# Kummer exchange generic interfaces

## Reason

The concrete definitions repeatedly elaborate large derived-category instance expressions.
The kernel spends most of the single-file limit comparing these expressions after nested
instance proofs have been abstracted. Construct the same canonical maps over a general
coefficient category, and specialize those constructions to `ModuleCat A` by abbreviations.
Use one constant-single comparison throughout. Its factors, and their order, are unchanged;
parenthesization changes only by category associativity. The shift instances now alias the
canonical instances in the source library instead of reconstructing their identical bodies.
No hypothesis or conclusion of the four existing result propositions changes. No Challenge target is
edited. Target meanings through these definitions are unchanged and are available for the
normal independent definition review.

## Old

```lean
noncomputable def kummerExchangeUpper (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X :=
  L(upperStar (ModuleCat.{u + 1} A) f)

noncomputable def kummerExchangeLower (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A Y :=
  R(lowerStar (ModuleCat.{u + 1} A) f)

noncomputable instance kummerExchangeUpperCommShift (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (kummerExchangeUpper A f).CommShift ℤ :=
  Functor.CommShift.ofIso
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ℤ

noncomputable instance kummerExchangeLowerCommShift (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (kummerExchangeLower A f).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).rightAdjointCommShift ℤ

noncomputable def kummerExchangeAdjunction (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    kummerExchangeUpper A f ⊣ kummerExchangeLower A f :=
  derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f

noncomputable def kummerExchangeArrow (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (K : DerivedCategoryModule A X) :
    (kummerExchangeUpper A g).obj ((kummerExchangeLower A a).obj K) ⟶
      (kummerExchangeLower A a').obj ((kummerExchangeUpper A v).obj K) :=
  (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K

noncomputable abbrev kummerExchangeConstant (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

noncomputable def kummerExchangeClassPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategoryModule A Y) (q : ℕ)
    (x : (_root_.DerivedCategory.singleFunctor _ 0).obj (kummerExchangeConstant A Y) ⟶
      K⟦(q : ℤ)⟧) :
    (_root_.DerivedCategory.singleFunctor _ 0).obj (kummerExchangeConstant A X) ⟶
      (kummerExchangeUpper A f).obj K⟦(q : ℤ)⟧ :=
  (_root_.DerivedCategory.singleFunctor _ 0).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).inv.app
        (ModuleCat.of A A)) ≫
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).inv.app _ ≫
    (kummerExchangeUpper A f).map x ≫
    ((kummerExchangeUpper A f).commShiftIso (q : ℤ)).hom.app K

noncomputable def kummerExchangeEdge (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategoryModule A X) (q : ℕ)
    (x : (_root_.DerivedCategory.singleFunctor _ 0).obj (kummerExchangeConstant A X) ⟶
      K⟦(q : ℤ)⟧) :
    kummerExchangeConstant A Y ⟶
      (_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((kummerExchangeLower A f).obj K) :=
  (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
    (_root_.DerivedCategory.homologyFunctor _ 0).map
      ((kummerExchangeAdjunction A f).homEquiv _ _
        ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).hom.app _ ≫
          (_root_.DerivedCategory.singleFunctor _ 0).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
              (ModuleCat.of A A)) ≫ x) ≫
        ((kummerExchangeLower A f).commShiftIso (q : ℤ)).hom.app K) ≫
    ((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso
      (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app _

noncomputable def kummerExchangeSectionPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (s : kummerExchangeConstant A Y ⟶ G) :
    kummerExchangeConstant A X ⟶ (upperStar (ModuleCat.{u + 1} A) f).obj G :=
  (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).inv.app
    (ModuleCat.of A A) ≫ (upperStar (ModuleCat.{u + 1} A) f).map s

noncomputable def kummerExchangeHigherMap (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (K : DerivedCategoryModule A X) (q : ℤ) :
    (upperStar (ModuleCat.{u + 1} A) g).obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((kummerExchangeLower A a).obj K)) ⟶
    (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((kummerExchangeLower A a').obj
        ((kummerExchangeUpper A v).obj K)) :=
  (leftDerivedUpperStarHomologyFunctorIso (ModuleCat.{u + 1} A) g q).hom.app _ ≫
    (_root_.DerivedCategory.homologyFunctor _ q).map
      (kummerExchangeArrow A sq K)

noncomputable def kummerExchangeImage (A : Type (u + 1)) [CommRing A]
    {X B : Scheme.{u}} (a : X ⟶ B)
    (L₀ : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategoryModule A B :=
  (kummerExchangeLower A a).obj
    ((kummerExchangeUpper A a).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))

noncomputable def kummerExchangeTarget (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} (v : X' ⟶ X) (a' : X' ⟶ B') (a : X ⟶ B)
    (L₀ : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategoryModule A B' :=
  (kummerExchangeLower A a').obj
    ((kummerExchangeUpper A v).obj
      ((kummerExchangeUpper A a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)))

theorem relativeKummerExchange_unit (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (kummerExchangeUpper A g).map
        ((kummerExchangeAdjunction A a).unit.app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)) ≫
      kummerExchangeArrow A sq
        ((kummerExchangeUpper A a).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)) =
    (kummerExchangeAdjunction A a').unit.app
        ((kummerExchangeUpper A g).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)) ≫
      (kummerExchangeLower A a').map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).hom.app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)) := by
  exact map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} A) sq.toCommSq _

theorem relativeKummerExchange_edge (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ)
    (x : (_root_.DerivedCategory.singleFunctor _ 0).obj (kummerExchangeConstant A X) ⟶
      (kummerExchangeUpper A a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)⟦(q : ℤ)⟧) :
    kummerExchangeSectionPullback A g (kummerExchangeEdge A a _ q x) ≫
        kummerExchangeHigherMap A sq _ (q : ℤ) =
      kummerExchangeEdge A a' _ q (kummerExchangeClassPullback A v _ q x) := by
  sorry

theorem relativeKummerExchange_generators (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (h₀ : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((kummerExchangeAdjunction A a).unit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))))
    (h₀' : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((kummerExchangeAdjunction A a').unit.app
        ((kummerExchangeUpper A g).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)))))
    (hvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (kummerExchangeImage A a L₀)) ∧
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (kummerExchangeTarget A v a' a L₀)))
    (x : (_root_.DerivedCategory.singleFunctor _ 0).obj (kummerExchangeConstant A X) ⟶
      (kummerExchangeUpper A a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)⟦(1 : ℤ)⟧)
    (hx : IsIso (kummerExchangeEdge A a _ 1 x))
    (hx' : IsIso (kummerExchangeEdge A a' _ 1 (kummerExchangeClassPullback A v _ 1 x))) :
    IsIso (kummerExchangeArrow A sq
      ((kummerExchangeUpper A a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))) := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro i
  by_cases h0 : i = 0
  · subst i
    exact kummerExchange_isIso_zero A sq L₀ h₀ h₀'
  by_cases h1 : i = 1
  · subst i
    have he := relativeKummerExchange_edge A sq L₀ 1 x
    have : IsIso (kummerExchangeSectionPullback A g (kummerExchangeEdge A a _ 1 x)) := by
      dsimp only [kummerExchangeSectionPullback]
      infer_instance
    have : IsIso (kummerExchangeSectionPullback A g (kummerExchangeEdge A a _ 1 x) ≫
        kummerExchangeHigherMap A sq _ (1 : ℤ)) := by
      exact he.symm ▸ hx'
    have : IsIso (kummerExchangeHigherMap A sq _ (1 : ℤ)) :=
      IsIso.of_isIso_comp_left
        (kummerExchangeSectionPullback A g (kummerExchangeEdge A a _ 1 x)) _
    dsimp only [kummerExchangeHigherMap] at this
    exact IsIso.of_isIso_comp_left
      ((leftDerivedUpperStarHomologyFunctorIso (ModuleCat.{u + 1} A) g 1).hom.app _) _
  · exact kummerExchange_isIso_vanishing A sq L₀ i (hvan i h0 h1)

theorem relativeKummerExchange_degreeZero (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (h₀ : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((kummerExchangeAdjunction A a).unit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))))
    (h₀' : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((kummerExchangeAdjunction A a').unit.app
        ((kummerExchangeUpper A g).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)))))
    (hvan : ∀ i : ℤ, i ≠ 0 →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (kummerExchangeImage A a L₀)) ∧
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (kummerExchangeTarget A v a' a L₀))) :
    IsIso (kummerExchangeArrow A sq
      ((kummerExchangeUpper A a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))) := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro i
  by_cases h0 : i = 0
  · subst i
    exact kummerExchange_isIso_zero A sq L₀ h₀ h₀'
  · exact kummerExchange_isIso_vanishing A sq L₀ i (hvan i h0)

end AlgebraicGeometry.Etale
```

## New

```lean
noncomputable abbrev kummerExchangeUpper (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeUpper (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

noncomputable abbrev kummerExchangeLower (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeLower (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

noncomputable instance kummerExchangeUpperCommShift (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (kummerExchangeUpper A f).CommShift ℤ :=
  generic_kummerExchangeUpperCommShift (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

noncomputable instance kummerExchangeLowerCommShift (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (kummerExchangeLower A f).CommShift ℤ :=
  generic_kummerExchangeLowerCommShift (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

noncomputable abbrev kummerExchangeAdjunction (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeAdjunction (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

noncomputable abbrev kummerExchangeArrow (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_kummerExchangeArrow (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

noncomputable abbrev kummerExchangeConstant (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :=
  generic_kummerExchangeConstant (ModuleCat.{u + 1} A) (ModuleCat.of A A) T

noncomputable abbrev kummerExchangeClassPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeClassPullback (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

noncomputable abbrev kummerExchangeEdge (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeEdge (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

noncomputable abbrev kummerExchangeSectionPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)} :=
  generic_kummerExchangeSectionPullback (ModuleCat.{u + 1} A) (ModuleCat.of A A) f (G := G)

noncomputable abbrev kummerExchangeHigherMap (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_kummerExchangeHigherMap (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

noncomputable abbrev kummerExchangeImage (A : Type (u + 1)) [CommRing A]
    {X B : Scheme.{u}} (a : X ⟶ B) :=
  generic_kummerExchangeImage (ModuleCat.{u + 1} A) (ModuleCat.of A A) a

noncomputable abbrev kummerExchangeTarget (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} (v : X' ⟶ X) (a' : X' ⟶ B') (a : X ⟶ B) :=
  generic_kummerExchangeTarget (ModuleCat.{u + 1} A) (ModuleCat.of A A) v a' a

noncomputable abbrev relativeKummerExchange_unit (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_relativeKummerExchange_unit (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

noncomputable abbrev relativeKummerExchange_edge (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_relativeKummerExchange_edge (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

noncomputable abbrev relativeKummerExchange_generators (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_relativeKummerExchange_generators (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

noncomputable abbrev relativeKummerExchange_degreeZero (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_relativeKummerExchange_degreeZero (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

end AlgebraicGeometry.Etale
```

The generic data and proofs are constructed in the same module. The four original
propositions are retained as abbreviation specializations of the proved generic theorems.
Their inferred types are the original propositions (equal after unfolding the reducible specializations), with every hypothesis and conclusion
preserved. This changes their declaration kind from theorem to abbreviation, avoiding
re-elaboration and kernel comparison of the large concrete derived-category instances.
All result arguments after the square are supplied to the specialized generic theorem.
The generic theorems are public because public abbreviations cannot contain private names.

`genericConstantIso` is the canonical single-derived comparison followed by the single
functor applied to the canonical constant comparison. `genericPullback` and `genericEdge`
use that same composite. Their values differ from the old displayed expressions only by
associativity and the canonical shift instance aliases. All data is constructed directly.

The constant-square and shifted-adjunct calculations are local to the edge-naturality
proof, avoiding repeated concrete kernel conversions between separate declarations.
The proof uses ordinary tactics, with no proof-term transformation or extra axiom.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeKummerExchangeGenerators | U6 | Same maps via generic constructions; edge proof completed. |
| Sheaf.AlgebraicGeometry.NormalizedKummerCohomologyArrows | unclaimed | Same constant coefficient sheaf. Compiled unchanged against the delivered module (reviewer, 2026-10-25). |
| Sheaf.AlgebraicGeometry.NormalizedKummerGeneratorArrows | unclaimed | Same Leray edge map. Compiled unchanged against the delivered module (reviewer, 2026-10-25). |
| Sheaf.AlgebraicGeometry.NormalizedKummerGlobalArrows | unclaimed | Same constant coefficient sheaf. Compiled unchanged against the delivered module (reviewer, 2026-10-25). |
| Sheaf.AlgebraicGeometry.RelativeKummerNormalizedStalks | unclaimed | Transitive consumer; names no changed declaration. Not yet in the published build. |

## Status

landed 20261025T034002-L-197176 2026-10-25 (merge of deliver/U6/Sheaf.AlgebraicGeometry.RelativeKummerExchangeGenerators)
