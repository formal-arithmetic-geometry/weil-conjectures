# WeilConjectures.LisseLattice helper data relocation

## Reason

Proof-step modules need the already accepted helper data independently of the parent
theorem. Keeping those definitions in the parent would give an import cycle. Move
them verbatim into `Sheaf.Paper.LisseLatticeHeartLiftData`, and publicly reexport the
new module from the original item. This is a proof-organization change, not a repair
of a mathematical statement. All expressions, names and visibility stay identical.

## Old

In `lean/Sheaf/Paper/LisseLatticeHeartLift.lean`, under the original universe, variables
and namespace, the declarations were exactly:

```lean
/-- The constant uniformizer section of the completed coefficient ring, obtained from
its compatible constant quotient-cone map.
Source: BS 6.8.2 (blueprint: lem-tw-lisse-lattice-heart-lift). -/
def uniformizerSection (X : Scheme.{u}) :
    ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙ forget CommRingCat).sections :=
  (Functor.sectionsFunctor X.ProEtᵒᵖ).map
    (Functor.whiskerRight
      (Functor.whiskerRight
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
        (integralConstantToCompletionOfUniverses l E X).hom)
      (forget RingCat))
    ⟨fun _ ↦ ULift.up (Padic.coefficientExtensionUniformizer l E), fun _ ↦ rfl⟩

/-- The actual rational coefficient ring B_X[1/t], by sheafifying sectionwise localization.
Source: BS 6.8.2(2) (blueprint: lem-tw-lisse-lattice-heart-lift). -/
def rationalRing (X : Scheme.{u}) : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  ringedLocalizationRingOfUniverses.{u + 1, u + 1, u}
    (completedIntegralCommRingSheafUnrestricted l E X) (uniformizerSection l E X)

/-- The canonical localization unit from the completed coefficient ring to B_X[1/t].
Source: BS 6.8.2(2) (blueprint: lem-tw-lisse-lattice-heart-lift). -/
def coefficientMap (X : Scheme.{u}) :
    completedIntegralCommRingSheafUnrestricted l E X ⟶ rationalRing l E X :=
  ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u}
    (completedIntegralCommRingSheafUnrestricted l E X) (uniformizerSection l E X)

/-- The ordinary rational module category in the normalized continuous presentation.
Source: BS 6.8.2 (blueprint: lem-tw-lisse-lattice-heart-lift). -/
abbrev RationalModules (X : Scheme.{u}) :=
  pbcModules X (rationalCoefficientSheaf l X E)

/-- The completed coefficient pullback fixed by all finite quotient projections.
Source: BS 6.8.2, Remark 6.8.15
(blueprint: lem-tw-lisse-lattice-heart-lift). -/
def integralMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (adicTowerInverseImage f).map (purCoefficientIso l E Y).inv ≫
    AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum l E) ≫
      (purCoefficientIso l E X).hom

/-- Ordinary integral restriction; on an etale chart it is ordinary slice restriction.
Source: BS Remark 6.8.15 (blueprint: lem-tw-lisse-lattice-heart-lift). -/
abbrev integralPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ContinuousRational.modulePull f (integralMap l E f)

/-- Just the coefficient presentations and induced functor J named in the statement.
The two normalizations fix the completed and localized rings, rather than choosing an
unrelated coefficient isomorphism. No faithfulness or lisse-image assertion is a field.
Source: BS 6.8.2 and 6.8.14(2) (blueprint: lem-tw-lisse-lattice-heart-lift). -/
structure RealizationAt (X : Scheme.{u}) where
  completion : completedIntegralCommRingSheafUnrestricted l E X ≅
    AlgebraicGeometry.Scheme.integralCoefficientSheaf l X E
  residues : ∀ n : ℕ,
    completion.hom ≫ continuousCoefficientReduction l E X n =
      completedIntegralCommRingProjectionUnrestricted l E X n ≫
        (discreteContinuousCoefficientIso X).hom.app
          (AlgebraicGeometry.Scheme.finiteCoefficientRing l E n)
  localization : rationalRing l E X ≅ rationalCoefficientSheaf l X E
  localization_unit : coefficientMap l E X ≫ localization.hom =
    completion.hom ≫ integralRationalCoefficientMap l E X
  J : sfRationalConstructibleCategory l E X ⥤ DerivedCategory (RationalModules l E X)
  [additive : J.Additive]
  integral : sfRationalConstructibleLocalization l E X ⋙ J ≅
    (sfIntegralConstructible l E X).ι ⋙
      pbcDerivedExtend (completion.hom ≫ integralRationalCoefficientMap l E X)
  fractions : ∀ (K L : sfIntegralConstructibleCategory l E X)
      (f : K ⟶ L) (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    J.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) =
      sfRationalCoefficientEquiv l E a •
        J.map ((sfRationalConstructibleLocalization l E X).map f)

attribute [instance] RealizationAt.additive

/-- The actual scalar-extension map B to A, in the normalized presentation.
Source: BS 6.8.2 (blueprint: lem-tw-lisse-lattice-heart-lift). -/
def RealizationAt.scalar {X : Scheme.{u}} (a : RealizationAt l E X) :=
  a.completion.hom ≫ integralRationalCoefficientMap l E X

/-- Ordinary sheaf tensor extension along the actual localization map.
Source: BS 6.8.2 (blueprint: lem-tw-lisse-lattice-heart-lift). -/
abbrev RealizationAt.tensor {X : Scheme.{u}} (a : RealizationAt l E X) :=
  pbcExtend (a.scalar l E)

/-- The canonical degree-zero comparison, before asserting its invertibility: use the
universal derived tensor counit and the additive single-complex comparison.
Source: Stacks 06YY, BS 6.8.14(2) (blueprint: lem-tw-lisse-lattice-heart-lift). -/
def RealizationAt.singleComparison {X : Scheme.{u}} (a : RealizationAt l E X)
    (N : integralTowerModules l E X)
    (hN : sfIntegralConstructible l E X ((DerivedCategory.singleFunctor _ 0).obj N)) :
    a.J.obj ((sfRationalConstructibleLocalization l E X).obj
      ⟨(DerivedCategory.singleFunctor _ 0).obj N, hN⟩) ⟶
        (DerivedCategory.singleFunctor _ 0).obj ((a.tensor l E).obj N) :=
  a.integral.hom.app ⟨(DerivedCategory.singleFunctor _ 0).obj N, hN⟩ ≫
    pbcComplexCounit (a.scalar l E) ((CochainComplex.singleFunctor _ 0).obj N) ≫
      DerivedCategory.Q.map (((a.tensor l E).mapCochainComplexSingleFunctor 0).hom.app N)

/-- The same normalized realizations on charts, with the balanced tensor restriction.
The section equation characterizes the comparison on pullbacks of every pure tensor.
These are constructions named in the item, not hypotheses about chosen lattices.
Source: BS 6.8.2 and Remark 6.8.15 (blueprint: lem-tw-lisse-lattice-heart-lift). -/
structure Realizations where
  realization : ∀ X : Scheme.{u}, RealizationAt l E X
  balance : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f],
    ((realization Y).tensor l E) ⋙ LisseRealization.ordinaryPull l E f ≅
      integralPull l E f ⋙ ((realization X).tensor l E)
  balance_sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
      (N : integralTowerModules l E Y) (U : Y.ProEt)
      (b : (rationalCoefficientSheaf l Y E).obj.obj (op U)) (n : N.val.obj (op U)),
    ((balance f).hom.app N).val.app (op ((proEtaleBaseChange f).obj U))
      (ContinuousRational.moduleUnit f (LisseRealization.coefficientPull l E f)
        (((realization Y).tensor l E).obj N) U
          (pbcTensorSection ((realization Y).scalar l E) N (op U) b n)) =
      pbcTensorSection ((realization X).scalar l E) ((integralPull l E f).obj N)
        (op ((proEtaleBaseChange f).obj U))
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
          (LisseRealization.coefficientPull l E f)).hom.app (op U) b)
        (ContinuousRational.moduleUnit f (integralMap l E f) N U n)

/-- Constructibility is the recorded finite-stratification, finitely-presented-module
condition, transported through the normalized integral coefficient isomorphism.
Source: BS 6.8.10 (blueprint: lem-tw-lisse-lattice-heart-lift). -/
abbrev Constructible (X : Scheme.{u}) (N : integralTowerModules l E X) :=
  IsIntegralStratifiedFinitelyPresented X (pbcIntegralDatum l E)
    ((pbcRestrict (purCoefficientIso l E X).hom).obj N)

/-- Precisely a choice of global constructible lattice and local lisse lattices.
Integrality of their degree-zero complexes is a conclusion, not a field of this record.
Source: BS 6.8.13 and 6.8.4(6) (blueprint: lem-tw-lisse-lattice-heart-lift). -/
structure Choice (a : Realizations l E) (X : Scheme.{u}) (L : RationalModules l E X) where
  N : integralTowerModules l E X
  constructible : Constructible l E X N
  alpha : (((a.realization X).tensor l E).obj N) ≅ L
  I : Type (u + 1)
  Y : I → X.Etale
  cover : X.smallEtaleTopology.CoversTop Y
  quasiCompact : ∀ i : I, QuasiCompact (Y i).hom
  M : ∀ i : I, integralTowerModules l E (Y i).left
  locallyFree : ∀ i : I, (M i).IsFiniteLocallyFree
  beta : ∀ i : I, (((a.realization (Y i).left).tensor l E).obj (M i)) ≅
    (LisseRealization.ordinaryPull l E (Y i).hom).obj L

/-- The specified map beta inverse after alpha restricted to the chart; the first
factor is exactly the pure-tensor-normalized restriction comparison.
Source: BS 6.8.14(2) (blueprint: lem-tw-lisse-lattice-heart-lift). -/
def Choice.specified {a : Realizations l E} {X : Scheme.{u}} {L : RationalModules l E X}
    (c : Choice l E a X L) (i : c.I) :
    (((a.realization (c.Y i).left).tensor l E).obj ((integralPull l E (c.Y i).hom).obj c.N)) ≅
      (((a.realization (c.Y i).left).tensor l E).obj (c.M i)) :=
  ((a.balance (c.Y i).hom).app c.N).symm ≪≫
    (LisseRealization.ordinaryPull l E (c.Y i).hom).mapIso c.alpha ≪≫ (c.beta i).symm

/-- All assertions for an arbitrary choice. The displayed equations characterize the
image of the chosen lift and its inverse in the derived category, not only on H^0.
Source: BS 6.8.11(3), 6.8.14(2), Remark 6.8.15
(blueprint: lem-tw-lisse-lattice-heart-lift). -/
def Choice.Assertions {a : Realizations l E} {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)] {L : RationalModules l E X}
    (c : Choice l E a X L) : Prop :=
  ∃ hN : sfIntegralConstructible l E X ((DerivedCategory.singleFunctor _ 0).obj c.N),
    sfRationalHeartProperty l E X ((sfRationalConstructibleLocalization l E X).obj
      ⟨(DerivedCategory.singleFunctor _ 0).obj c.N, hN⟩) ∧
    IsIso ((a.realization X).singleComparison l E c.N hN) ∧
    (∀ i : c.I,
      ∃ hNi : sfIntegralConstructible l E (c.Y i).left
          ((DerivedCategory.singleFunctor _ 0).obj ((integralPull l E (c.Y i).hom).obj c.N)),
      ∃ hMi : sfIntegralConstructible l E (c.Y i).left
          ((DerivedCategory.singleFunctor _ 0).obj (c.M i)),
        IsIso ((a.realization (c.Y i).left).singleComparison l E
          ((integralPull l E (c.Y i).hom).obj c.N) hNi) ∧
        IsIso ((a.realization (c.Y i).left).singleComparison l E (c.M i) hMi) ∧
        ∃! e : (sfRationalConstructibleLocalization l E (c.Y i).left).obj
            ⟨(DerivedCategory.singleFunctor _ 0).obj
              ((integralPull l E (c.Y i).hom).obj c.N), hNi⟩ ≅
          (sfRationalConstructibleLocalization l E (c.Y i).left).obj
            ⟨(DerivedCategory.singleFunctor _ 0).obj (c.M i), hMi⟩,
          (a.realization (c.Y i).left).J.map e.hom ≫
              (a.realization (c.Y i).left).singleComparison l E (c.M i) hMi =
            (a.realization (c.Y i).left).singleComparison l E
                ((integralPull l E (c.Y i).hom).obj c.N) hNi ≫
              (DerivedCategory.singleFunctor _ 0).map (c.specified l E i).hom ∧
          (a.realization (c.Y i).left).J.map e.inv ≫
              (a.realization (c.Y i).left).singleComparison l E
                ((integralPull l E (c.Y i).hom).obj c.N) hNi =
            (a.realization (c.Y i).left).singleComparison l E (c.M i) hMi ≫
              (DerivedCategory.singleFunctor _ 0).map (c.specified l E i).inv) ∧
    IsRationalLisse l E X ((sfRationalConstructibleLocalization l E X).obj
      ⟨(DerivedCategory.singleFunctor _ 0).obj c.N, hN⟩)

```

## New

The declarations above are verbatim in
`lean/Sheaf/Paper/LisseLatticeHeartLiftData.lean`, with the same public imports,
universe, variables, namespace and exposure. Only blueprint owner comments change
to `def-tw-lisse-lattice-heart-lift-data`. No definition body or signature changes.
The original module now contains:

```lean
public import Sheaf.Paper.LisseLatticeHeartLiftData
```

Its existing theorem signature is verbatim. Its proof privately imports the five
new theorem modules; this keeps those new proof statements out of the public API.

## Users

Read-only `tools/downstream.py Sheaf.Paper.LisseLatticeHeartLift --uses
WeilConjectures.LisseLattice` reports zero downstream modules and only the item itself
as a textual user. Also searched the complete Lean trees and current change records.
The item remains a live DAG dependency of the unproved parent realization theorem;
it is not withdrawn on the basis of having zero current Lean importers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseLatticeHeartLift | U9 | Reexports all original declarations unchanged; proof uses new substeps. |
| Sheaf.Paper.LisseLatticeHeartLiftData | new in U9 delivery | Owns unchanged helper definitions. |
| Sheaf.Paper.LisseLatticeNormalizedRealizations | new in U9 delivery | Imports data and states normalization substep. |
| Sheaf.Paper.LisseLatticeChoiceExistence | new in U9 delivery | Imports data and states lattice existence substep. |
| Sheaf.Paper.LisseLatticeSingleComparisons | new in U9 delivery | Imports data and states membership/comparison substep. |
| Sheaf.Paper.LisseLatticeRealizationFaithful | new in U9 delivery | Imports data and states Hom-comparison transport substep. |
| Sheaf.Paper.LisseLatticeLisseDescent | new in U9 delivery | Imports data and states completed-pullback descent substep. |

All target statements and definitions retain their meaning. There is no forced
adaptation of a module held by another group and no upstream source edit.

## Status

landed 20261025T124041-L-1929649 2026-10-25 (merge of deliver/U9/Sheaf.Paper.LisseLatticeHeartLift)
