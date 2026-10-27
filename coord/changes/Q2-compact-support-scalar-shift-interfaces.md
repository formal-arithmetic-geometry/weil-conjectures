# WeilConjectures.PurStrictScalar canonical shift interfaces

## Reason

The scalar-shift theorem needs independent proofs of original-site mates, strict
mates, and limit constraints. Move its existing instances and OriginalMateShift
predicate to CompactSupportScalarShiftStructures, publicly re-exported by the item,
so those smaller modules can refer to precisely the same canonical structures.
This is an interface extraction for an acyclic proof decomposition, not a timeout
workaround. All moved declaration names, signatures, instance attributes and bodies
are unchanged. No mathematical definition or target meaning changes.

## Old

The following declarations were in Sheaf.Paper.CompactSupportScalarShiftNormalization:

```lean
/-- Canonical integer shifts for tensorCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance tensorCommShift : (T l E F i W).CommShift ℤ :=
  inferInstanceAs ((tensor l E F i W).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for properCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance properCommShift {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).CommShift ℤ :=
  inferInstanceAs ((towerDirectImage
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).rightDerivedFunctor.CommShift ℤ)
/-- Canonical integer shifts for openCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance openCommShift {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).CommShift ℤ :=
  inferInstanceAs ((towerJ
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for sequenceLimitCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance sequenceLimitCommShift : (coefficientSequenceLimit l E W).CommShift ℤ := by
  unfold coefficientSequenceLimit coefficientConstantTowerLimit
  infer_instance
/-- Canonical integer shifts for systemRestrictionCommShift,
 inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance systemRestrictionCommShift : (systemU l E W).CommShift ℤ :=
  inferInstanceAs ((systemRestriction l E W).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for nativeOpenCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance nativeOpenCommShift {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j).CommShift ℤ := by
  unfold ProEtale.VaryingRing.J
  infer_instance
/-- Canonical integer shifts for nativeProperCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance nativeProperCommShift {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g).CommShift ℤ := by
  unfold ProEtale.VaryingRing.P
  infer_instance
/-- Canonical integer shifts for reductionCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance reductionCommShift (S : CoefficientDerivedSystemCalculus.{u, u} l E W) :
    S.reduction.CommShift ℤ := S.adjunction.leftAdjointCommShift ℤ
/-- Canonical integer shifts for supportCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance supportCommShift {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) : (support l E c S).CommShift ℤ := by
  unfold support
  infer_instance
/-- Canonical integer shifts for nativeSupportCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance nativeSupportCommShift {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    (scalarSupportNative l E c S).CommShift ℤ := by
  unfold scalarSupportNative
  infer_instance
/-- Canonical integer shifts for scalarSupportCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance scalarSupportCommShift {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    (scalarSupport l E c S).CommShift ℤ :=
  haveI := nativeSupportCommShift l E c S
  haveI := sequenceLimitCommShift l E Y
  inferInstanceAs ((scalarSupportNative l E c S ⋙ coefficientSequenceLimit l E Y).CommShift ℤ)
/-- Canonical integer shifts for baseTensorCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance baseTensorCommShift : (baseTensor l E F i W).CommShift ℤ :=
  haveI := (baseTensor_exact l E F i W).1
  haveI := (baseTensor_exact l E F i W).2
  inferInstanceAs ((pbcExtend (constantMap l E F i W)).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for constantRestrictionCommShift,
 inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance constantRestrictionCommShift : (scalarConstantRestriction l E W).CommShift ℤ :=
  inferInstanceAs ((constantRestriction l E W).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for subsequenceCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance subsequenceCommShift (e : ℕ) : (subsequence l E W e).CommShift ℤ :=
  inferInstanceAs ((ordinarySubsequence l E W e).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for completedExtensionCommShift,
 inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance completedExtensionCommShift :
    (pbcDerivedExtend (completedCoefficientMap l E F i W)).CommShift ℤ :=
  PurCompactSupport.scalarCommShift (completedCoefficientMap l E F i W)
/-- Canonical integer shifts for scalarCompletionTargetCommShift,
 inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance scalarCompletionTargetCommShift :
    (pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
      scalarConstantRestriction l F W).CommShift ℤ :=
  haveI := completedExtensionCommShift l E F i W
  haveI := constantRestrictionCommShift l F W
  inferInstance
/-- Canonical integer shifts for pullCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance pullCommShift {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).CommShift ℤ :=
  inferInstanceAs ((towerPullback
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).mapDerivedCategory.CommShift ℤ)

/-- The original-site proper/open squares, including the balanced transpose and counit.
Source: Stacks 07A6, 0B56 and 0E8I
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
def OriginalMateShift {R₀ S₀ : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R₀ S₀) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Prop :=
  NatTrans.CommShift (PurCompactSupport.properComparison a c.g) ℤ ∧
  NatTrans.CommShift (PurCompactSupport.openComparison a c.i) ℤ ∧
  NatTrans.CommShift (PurCompactSupport.scalarPull a c.g).inv ℤ ∧
  NatTrans.CommShift (proEtaleRingDerivedAdjunction c.g
    (R₀.ring Y) (R₀.ring c.Z) (R₀.pull c.g)).counit ℤ
```

## New

The exact declarations above (with an additional blueprint attachment in the predicate docstring) reside in Sheaf.Paper.CompactSupportScalarShiftStructures.
The original module publicly imports that module and retains the theorem's signature.
The additional four modules each state one proper part of its proof, with a named
public theorem and its own DAG node. The original module imports these privately.
A new DAG node records the already proved scalarCommShift_existsUnique helper in
IntegralCompactSupportCoefficientComparison independently of that module's larger
coefficient-comparison theorem, avoiding a false dependency on the parent result.
The analogous attachment for the proved integralTriangulated helper records the
actual finiteTorConstructibleIntegral predicate, without using the later main theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompactSupportScalarShiftNormalization | Q2 | Same public declarations re-exported; proof assembled from the smaller steps. |

There are no current Lean importers of the item (tools/downstream.py). Unfinished
DAG parents continue to use the original node and theorem. No consumer is withdrawn.
New modules OriginalScalarMateShift, StrictScalarMateShift, ScalarLimitConstraintShift
and CompactSupportScalarShiftWitness import the extracted structures.

## Status

landed 20261025T164128-L-956705 2026-10-25 (merge of deliver/Q2/Sheaf.Paper.CompactSupportScalarShiftNormalization)
