# Canonical étale power normalization declarations

## Reason

Move the three existing normalization declarations into a data-only module so that
strictly smaller power-algebra and tensor-comparison lemmas can use them without
an import cycle. The assigned item publicly imports that module and re-exports
all three names. This is a relocation, with identical signatures and construction
bodies; only the blueprint ownership in the docstrings changes. No target or
mathematical definition changes meaning.

## Old

In `Sheaf.TraceFormula.GradedPushforwardEtaleRestriction`:

```lean
/-- Identify the existing tensor powers on the original site with their values on the
small affine model, using the counit of the actual restriction equivalence.
Source: Stacks, Tags 039Z and 03EL
(blueprint: lem-trf-graded-pushforward-etale-restriction). -/
def gradedPowerChartIso (X : AlgebraicSpace S) (L : X.Modules) (n : ℕ) :
    X.smallModuleRestriction.obj (evaluationLinePower X L n) ≅ evaluationSmallPower X L n :=
  X.smallModuleEquivalence.counitIso.app (evaluationSmallPower X L n)

/-- The canonical identification of the first tensor power with the module itself.
Source: Stacks, Tag 03EL (blueprint: lem-trf-graded-pushforward-etale-restriction). -/
def gradedPowerOneIso (X : AlgebraicSpace S) (L : X.Modules) :
    evaluationLinePower X L 1 ≅ L :=
  X.smallModuleEquivalence.inverse.mapIso (ρ_ (X.smallModuleRestriction.obj L)) ≪≫
    X.smallModuleEquivalence.unitIso.symm.app L

/-- Canonical tensor-power products, checked on an affine basis through the restriction
equivalence. The zero power is the structure module and its unit map is invertible.
The multiplication is concatenation of actual tensor factors, with ordinary symmetry.
Source: Stacks, Tags 03EL, 039Z and 0D3C
(blueprint: lem-trf-graded-pushforward-etale-restriction). -/
def HasCanonicalEtalePowerProducts (X : AlgebraicSpace S) (L : X.Modules)
    (A : EtaleGradedModuleAlgebra (evaluationLinePower X L)) : Prop :=
  IsIso A.unit ∧
  (∀ (m n : ℕ) (V : X.SmallEtaleModel)
    (s : (evaluationLinePower X L m).val.obj (op (X.smallEtaleInclusion.obj V)))
    (t : (evaluationLinePower X L n).val.obj (op (X.smallEtaleInclusion.obj V))),
    (gradedPowerChartIso X L (m + n)).hom.val.app (op V)
        (A.mul m n (X.smallEtaleInclusion.obj V) s t) =
      (evaluationPowerAddIso (X.smallModuleRestriction.obj L) m n).inv.val.app (op V)
        (evaluationSmallTmul X (evaluationSmallPower X L m) (evaluationSmallPower X L n) V
          ((gradedPowerChartIso X L m).hom.val.app (op V) s)
          ((gradedPowerChartIso X L n).hom.val.app (op V) t))) ∧
  (∀ (V : X.SmallEtaleModel)
    (a : X.structureSheaf.obj.obj (op (X.smallEtaleInclusion.obj V))),
    (gradedPowerChartIso X L 0).hom.val.app (op V)
        (A.unit.val.app (op (X.smallEtaleInclusion.obj V)) a) =
      @id ((evaluationSmallPower X L 0).val.obj (op V)) a)
```

## New

In `Sheaf.TraceFormula.EtalePowerProductNormalization`, publicly imported by the
original module:

```lean
/-- Identify the existing tensor powers on the original site with their values on the
small affine model, using the counit of the actual restriction equivalence.
Source: Stacks, Tags 039Z and 03EL
(blueprint: def-trf-etale-power-product-normalization). -/
def gradedPowerChartIso (X : AlgebraicSpace S) (L : X.Modules) (n : ℕ) :
    X.smallModuleRestriction.obj (evaluationLinePower X L n) ≅ evaluationSmallPower X L n :=
  X.smallModuleEquivalence.counitIso.app (evaluationSmallPower X L n)

/-- The canonical identification of the first tensor power with the module itself.
Source: Stacks, Tag 03EL (blueprint: def-trf-etale-power-product-normalization). -/
def gradedPowerOneIso (X : AlgebraicSpace S) (L : X.Modules) :
    evaluationLinePower X L 1 ≅ L :=
  X.smallModuleEquivalence.inverse.mapIso (ρ_ (X.smallModuleRestriction.obj L)) ≪≫
    X.smallModuleEquivalence.unitIso.symm.app L

/-- Canonical tensor-power products, checked on an affine basis through the restriction
equivalence. The zero power is the structure module and its unit map is invertible.
The multiplication is concatenation of actual tensor factors, with ordinary symmetry.
Source: Stacks, Tags 03EL, 039Z and 0D3C
(blueprint: def-trf-etale-power-product-normalization). -/
def HasCanonicalEtalePowerProducts (X : AlgebraicSpace S) (L : X.Modules)
    (A : EtaleGradedModuleAlgebra (evaluationLinePower X L)) : Prop :=
  IsIso A.unit ∧
  (∀ (m n : ℕ) (V : X.SmallEtaleModel)
    (s : (evaluationLinePower X L m).val.obj (op (X.smallEtaleInclusion.obj V)))
    (t : (evaluationLinePower X L n).val.obj (op (X.smallEtaleInclusion.obj V))),
    (gradedPowerChartIso X L (m + n)).hom.val.app (op V)
        (A.mul m n (X.smallEtaleInclusion.obj V) s t) =
      (evaluationPowerAddIso (X.smallModuleRestriction.obj L) m n).inv.val.app (op V)
        (evaluationSmallTmul X (evaluationSmallPower X L m) (evaluationSmallPower X L n) V
          ((gradedPowerChartIso X L m).hom.val.app (op V) s)
          ((gradedPowerChartIso X L n).hom.val.app (op V) t))) ∧
  (∀ (V : X.SmallEtaleModel)
    (a : X.structureSheaf.obj.obj (op (X.smallEtaleInclusion.obj V))),
    (gradedPowerChartIso X L 0).hom.val.app (op V)
        (A.unit.val.app (op (X.smallEtaleInclusion.obj V)) a) =
      @id ((evaluationSmallPower X L 0).val.obj (op V)) a)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.GradedPushforwardEtaleRestriction | W4 | Publicly import the new owner; all names, types and bodies stay identical. |
| Sheaf.TraceFormula.CanonicalEtaleLinePowerAlgebra | new in this delivery | Uses the same canonical-product predicate. |
| Sheaf.TraceFormula.EtaleLinePowerComparison | new in this delivery | Uses the same predicate and first-power isomorphism. |

A search of both Lean roots finds no current direct importer of the assigned
item and no external source occurrence of any of the three moved names.
The DAG parents still need the assigned item, which is retained. New lemmas are
in separate modules and do not mention direct images or the graded base-change
structure. No consumer adaptation is needed.

## Status

landed 20261026T083436-L-2354896 2026-10-26 (merge of deliver/W4/Sheaf.TraceFormula.GradedPushforwardEtaleRestriction)
