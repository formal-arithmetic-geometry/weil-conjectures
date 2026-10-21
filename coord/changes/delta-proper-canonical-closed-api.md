# ProperAmbientDoubleDualCompatibility

## Reason

Repeated conversion between the specialized derived-Hom presentation and the generic closed
category presentation caused kernel/elaboration timeouts. Use the already proved canonical
closed-category dual comparison and double-dual map, and package the same four clauses before
specializing to ModuleCat. The current-source repair is revalidated through lcompile.py and the delivery preflight.

This is a representation change, not a weakening: all objects, maps, quantifiers, and four
clauses are retained. No target declaration in Challenge.lean is edited. Any target depending
on these definitions should have its semantic review reopened for this representation change.

The equality of the old delta formula and toIhomIhom follows from homEquiv_counit,
Functor.map_id, and id_comp, then the definition of curry. The generic proof
`doubleDual_eq_transpose` checks precisely this normalization. The canonical symmetry wrapper
is the descended Koszul braiding (its wrapper characterization is reflexive).

For exchange, `dualComparison_eq_curry` proves that the generic comparison is the transpose
of the product followed by pushed-forward signed evaluation and trace. The product is the
old projection map followed by the ordinary inverse-image counit:
`product_eq_laxProduct` proves this identity for an arbitrary monoidal adjunction. Substituting
rightDerivedLowerStarProjectionMap_app_app and the definition of the comonoidal tensor
comparison gives its etale instance. The swap written as inverse braiding in that formula
is the original swap with the factors interchanged, since the Koszul symmetry squares to
identity. Thus neither the trace nor the orientation of exchange changes.

Unfolding the new predicate gives naturality, componentwise IsIso, the uninverted square,
and exactly the old final implication. `pre` is the map of derivedHom on opposite arrows;
`verdierDual` is that functor evaluated at the dualizing object. Hence each clause has
exactly its original mathematical meaning. No constructibility or biduality is assumed.

## Old

```lean
noncomputable def ambientDoubleDualMap
    (W K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ (dualityDoubleFunctor (derivedHom A X) W).obj K :=
  (derivedTensorHomAdjunction A (((derivedHom A X).obj (op K)).obj W)).homEquiv K W
    (ambientDualEvaluation A X W K)
```

```lean
noncomputable def properAmbientVerdierExchangeMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] (K : DerivedCategoryModule Λ X) :
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
        ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).obj (op K)) ⟶
      (verdierDual (ModuleCat.{u + 1} Λ) g).obj
        (op ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)
    ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)).homEquiv _ _
    (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)).app
        ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).obj (op K))) ≫
      ambientDirectImageProduct (ModuleCat.{u + 1} Λ) f _ K ≫
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
        (ambientDualEvaluation (ModuleCat.{u + 1} Λ) X
          (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) K) ≫
      properAmbientDualityTrace Λ f g)
```

```lean
def ProperAmbientDoubleDualCompatibility
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] : Prop :=
  (∀ (K L : DerivedCategoryModule Λ X) (h : K ⟶ L),
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
        ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).map h.op) ≫
        properAmbientVerdierExchangeMap Λ f g K =
      properAmbientVerdierExchangeMap Λ f g L ≫
        (verdierDual (ModuleCat.{u + 1} Λ) g).map
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map h).op) ∧
  (∀ K : DerivedCategoryModule Λ X, IsIso (properAmbientVerdierExchangeMap Λ f g K)) ∧
  (∀ K : DerivedCategoryModule Λ X,
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
        (ambientDoubleDualMap (ModuleCat.{u + 1} Λ) X
          (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) K) ≫
        properAmbientVerdierExchangeMap Λ f g
          ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).obj (op K)) =
      ambientDoubleDualMap (ModuleCat.{u + 1} Λ) Y
          (dualizingComplex (ModuleCat.{u + 1} Λ) g)
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K) ≫
        (verdierDual (ModuleCat.{u + 1} Λ) g).map
          (properAmbientVerdierExchangeMap Λ f g K).op) ∧
  (∀ K : DerivedCategoryModule Λ X,
    IsIso (ambientDoubleDualMap (ModuleCat.{u + 1} Λ) Y
      (dualizingComplex (ModuleCat.{u + 1} Λ) g)
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)) →
    IsIso ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
      (ambientDoubleDualMap (ModuleCat.{u + 1} Λ) X
        (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) K)))
```

## New

```lean
noncomputable def ambientDoubleDualMap
    (W K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ (ihom ((ihom K).obj W)).obj W :=
  MonoidalClosed.toIhomIhom W K
```

```lean
noncomputable def properAmbientVerdierExchangeMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] (K : DerivedCategoryModule Λ X) :
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
        ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).obj (op K)) ⟶
      (verdierDual (ModuleCat.{u + 1} Λ) g).obj
        (op ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)) :=
  ambientDirectImageDualComparison (ModuleCat.{u + 1} Λ) f
    (properAmbientDualityTrace Λ f g) K
```

```lean
def ProperAmbientDoubleDualCompatibility
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] : Prop :=
  AmbientDirectImageDoubleDualCompatibility (ModuleCat.{u + 1} Λ) f
    (properAmbientDualityTrace Λ f g)
```

```lean
def TracedDualCompatibility
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.LaxBraided] {W : C} {W' : D} (t : G.obj W ⟶ W') : Prop :=
  (∀ (K L : C) (h : K ⟶ L),
    G.map ((pre h).app W) ≫ dualComparison G t K =
      dualComparison G t L ≫ (pre (G.map h)).app W') ∧
  (∀ K, IsIso (dualComparison G t K)) ∧
  (∀ K, G.map (toIhomIhom W K) ≫ dualComparison G t ((ihom K).obj W) =
    toIhomIhom W' (G.obj K) ≫ (pre (dualComparison G t K)).app W') ∧
  (∀ K, IsIso (toIhomIhom W' (G.obj K)) → IsIso (G.map (toIhomIhom W K)))
```

```lean
def AmbientDirectImageDoubleDualCompatibility
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {W' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (t : (lowerStar A f).rightDerivedFunctor.obj W ⟶ W') : Prop :=
  letI := leftDerivedUpperStarMonoidal A f
  let p := derivedUpperStarLowerStarAdjunction A f
  letI := p.rightAdjointLaxBraidedOfδ (leftDerivedUpperStar_map_braiding_hom_δ A f)
  MonoidalClosed.TracedDualCompatibility (lowerStar A f).rightDerivedFunctor t
```

```lean
noncomputable def ambientDirectImageDualComparison
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {W' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (t : (lowerStar A f).rightDerivedFunctor.obj W ⟶ W')
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (lowerStar A f).rightDerivedFunctor.obj (((derivedHom A X).obj (op K)).obj W) ⟶
      ((derivedHom A Y).obj (op ((lowerStar A f).rightDerivedFunctor.obj K))).obj W' :=
  letI := leftDerivedUpperStarMonoidal A f
  let p := derivedUpperStarLowerStarAdjunction A f
  letI := p.rightAdjointLaxBraidedOfδ (leftDerivedUpperStar_map_braiding_hom_δ A f)
  MonoidalClosed.dualComparison (lowerStar A f).rightDerivedFunctor t K
```

## Users

The downstream tool reports zero importing modules. Each changed declaration is used only
inside the item (ambientDoubleDualMap: 5 old occurrences; exchange: 6; predicate: 2).
No consumer adaptation is needed. All existing declaration names and explicit binders remain;
the generic coefficient universe is named `u'` consistently with the source API, and the
codomain of ambientDoubleDualMap is the definitionally equal canonical internal-Hom type.
The original evaluation, product, proper support comparison, composition mate, dualizing
isomorphism, and trace constructions are retained verbatim apart from universe variable names.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DeltaProperPushforward | S7 | canonical map/predicate presentation; proof completed |

On 2026-10-22, rechecked the current restored source and reapplied this representation
repair after return C-abbd2. The old definitions above still match that source. The three
`tools/downstream.py --uses` checks again report zero importing modules, so the user table
and absence of consumer adaptations remain current. No source-library declaration changes.

## Status

landed 20261021T203901-L-3890121 2026-10-21 (merge of deliver/S7/Sheaf.Paper.DeltaProperPushforward)
