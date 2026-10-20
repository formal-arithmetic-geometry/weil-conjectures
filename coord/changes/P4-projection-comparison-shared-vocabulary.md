# AlgebraicGeometry.ProEtale.ProjectionComparisonEquation

## Reason

Group: P4. Item: Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin.

The standalone equation module is unclaimed. Its only direct Lean importer is the item module.
Move all six of its declarations, including their docstrings, signatures and bodies verbatim,
into the item module before the proof helpers. Replace its public import with exactly its nine
public dependencies. Withdraw the old module via deleted.txt. Move the definition node's Lean
attachment to the item module; retain its statement, dependencies and declaration names.

The construction and meaning of every definition stay identical. All target signatures stay
identical. No declaration of WeilConjectures is changed or removed. The mathematical unit route
and the canonical proper/open comparison remain in place.

The reason is conversion cost across the module boundary: even an isolated reflexive unfolding
of the equation exhausts a 30,000-heartbeat kernel diagnostic budget. The two elaborated bodies
differ only in generated instance-proof constants. Their derived-category data depend on those
proofs, making repeated proof-irrelevance conversion expensive. Defining the vocabulary and
its proof in one module makes their proof cache available to both. Local proof-sharing tactics
inline the concrete private helper proofs and abstracts their nested class proofs using Lean
Meta.abstractProof, with Meta.abstractNestedProofs on their types. This reuses that cache.
They assign an ordinary proof term, which the kernel checks. No kernel check is disabled. The packet
merges modules and retains the constructions, rather than moving a proof to a separate file.
The compile-server time limit remains 60 seconds.

Consumer search: the item is the only module that imports the withdrawn module. All direct
references to ProjectionComparisonEquation and projectionComparisonConclusion occur in these
two original files. The adapted item imports the vocabulary's original public dependencies.

Validation: the full mathematical proof elaborates and passes normal kernel checking.
The proof-sharing tactics avoid retaining a call to the full term elaborator in a
new declaration, which keeps the delivery's axiom audit inexpensive.
The moved definitions and docstrings and the theorem signature are checked verbatim.
Delivery preflight remains the final validation.

The axiom audit has only the standard axioms plus the inherited sorry dependency already
present in the proved compact-square helper. The packet adds no written or generated holes.

## Old

All six declarations below were in
`lean/Sheaf/AlgebraicGeometry/ProjectionComparisonEtaleOriginEquation.lean`.
The item imported that module publicly.

```lean
/-- Finiteness of the positive-level coefficient quotient, from the recorded coefficient
extension theorem. Source: Serre, Local Fields, II, section 2
(blueprint: def-smooth-purity-projection-comparison-equation). -/
instance projectionComparisonCoefficient_finite
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n (Fact.out : 1 ≤ n)

/-- The derived pullback comparison used in the target transport.
Source: Stacks Tag 099R
(blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonPullbackIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory.symm
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ≪≫
    Functor.leftDerivedFunctorCompNatIso
      (Etale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.isoWhiskerLeft
      (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical target transport from the comparison of pullback and tensor.
Source: Stacks Tags 07A4 and 099R (blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonTargetIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H)) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)) := by
  exact
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).mapIso
      (asIso ((projectionComparisonPullbackIso A f).hom.app H)) ≪≫
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M).app
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)).symm

/-- Tensor target used in the bounded-below witness.
Source: main-20261015 blueprint (blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :=
  (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H))

/-- The asserted equality, with every target identification written explicitly.
The left route is PF-pro, P of the specified target identification, then C at the tensor.
The right route is C at M tensor identity, the inverse comparison tensor map, then V(PF-et).
Source: Stacks Tag 0E48 and the blueprint projection comparison, displayed equation
(blueprint: def-smooth-purity-projection-comparison-equation). -/
@[irreducible] def ProjectionComparisonEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor A (f := f) M H)) : Prop :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (projectionComparisonTargetIso A f M H).hom ≫
      (compactSupportSiteComparison A c).hom.app
        ⟨((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H), hD⟩ =
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
      ((compactSupportSiteComparison A c).hom.app ⟨M, hM⟩)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H) ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A)
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj M)).inv.app H) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app H)

/-- The full existential conclusion of the etale-origin comparison statement.
Source: main-20261015 blueprint, thm-pur-cohomological-smoothness.proof.md
(blueprint: def-smooth-purity-projection-comparison-equation). -/
@[irreducible] def projectionComparisonConclusion
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (H : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) X M)
    (_hH : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) Y H)
    (_hTor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing l E n) Y a b H) : Prop :=
  ∃ (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor (Padic.coefficientExtensionRing l E n) (f := f) M H)),
    ProjectionComparisonEquation (Padic.coefficientExtensionRing l E n) c M H hM hD
```

## New

The same declarations, verbatim, are in
`lean/Sheaf/AlgebraicGeometry/ProjectionComparisonEtaleOrigin.lean`, before its private helpers.
The item publicly imports the nine original public dependencies of the withdrawn module.
The old module becomes empty. The definition node's module and file point to the item.
All declarations keep their names, signatures, attributes, bodies and docstrings.

```lean
/-- Finiteness of the positive-level coefficient quotient, from the recorded coefficient
extension theorem. Source: Serre, Local Fields, II, section 2
(blueprint: def-smooth-purity-projection-comparison-equation). -/
instance projectionComparisonCoefficient_finite
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n (Fact.out : 1 ≤ n)

/-- The derived pullback comparison used in the target transport.
Source: Stacks Tag 099R
(blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonPullbackIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory.symm
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ≪≫
    Functor.leftDerivedFunctorCompNatIso
      (Etale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.isoWhiskerLeft
      (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical target transport from the comparison of pullback and tensor.
Source: Stacks Tags 07A4 and 099R (blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonTargetIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H)) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)) := by
  exact
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).mapIso
      (asIso ((projectionComparisonPullbackIso A f).hom.app H)) ≪≫
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M).app
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)).symm

/-- Tensor target used in the bounded-below witness.
Source: main-20261015 blueprint (blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :=
  (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H))

/-- The asserted equality, with every target identification written explicitly.
The left route is PF-pro, P of the specified target identification, then C at the tensor.
The right route is C at M tensor identity, the inverse comparison tensor map, then V(PF-et).
Source: Stacks Tag 0E48 and the blueprint projection comparison, displayed equation
(blueprint: def-smooth-purity-projection-comparison-equation). -/
@[irreducible] def ProjectionComparisonEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor A (f := f) M H)) : Prop :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (projectionComparisonTargetIso A f M H).hom ≫
      (compactSupportSiteComparison A c).hom.app
        ⟨((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H), hD⟩ =
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
      ((compactSupportSiteComparison A c).hom.app ⟨M, hM⟩)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H) ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A)
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj M)).inv.app H) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app H)

/-- The full existential conclusion of the etale-origin comparison statement.
Source: main-20261015 blueprint, thm-pur-cohomological-smoothness.proof.md
(blueprint: def-smooth-purity-projection-comparison-equation). -/
@[irreducible] def projectionComparisonConclusion
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (H : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) X M)
    (_hH : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) Y H)
    (_hTor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing l E n) Y a b H) : Prop :=
  ∃ (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor (Padic.coefficientExtensionRing l E n) (f := f) M H)),
    ProjectionComparisonEquation (Padic.coefficientExtensionRing l E n) c M H hM hD
```

The target statements and their meaning are unchanged: the construction blocks above are
identical. The independent review can compare these blocks directly. The private local
proof-sharing implementation is the performance repair described in Reason; it changes only proofs.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | P4 | Holds the unchanged vocabulary and its complete proof; replaces the public equation-module import with its dependencies. |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOriginEquation` | unclaimed | Its declarations move verbatim to the item; the old module is withdrawn. |

These are the only current Lean users of the six declaration names. The item is the
only importer of the old module; the two other DAG search hits are historical search
logs, not Lean attachments or proof dependencies. The mathematical definition node
remains attached and is not withdrawn.

## Status

landed 20261020T235615-L-1195379 2026-10-20 (merge of deliver/P4/Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin)
