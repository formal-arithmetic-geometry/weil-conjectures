# AlgebraicGeometry.Etale.compactSupportGraphDerivedComparison_geometric_baseChange

## Reason

The assigned source-library theorem has no Noetherian assumptions. The graph comparison
was restricted to locally Noetherian quasi-compact schemes, although its construction
and its geometric exchange equation use none of those assumptions. Remove them from the
exchange theorem. In the invertibility theorem and its canonical inverse replace them
with `[QuasiCompact f]`, exactly what makes the geometric etale fibre finite. Its proof
then uses the existing finite-etale graph theorem and torsion proper base change unchanged.

Both changed modules were unclaimed when inspected. The proof-only projection-formula
import is replaced by EtaleDerivedJointlySurjectiveConservative: the former imports the
assigned parent theorem and therefore creates an import cycle. The new theorem proves
conservativity for arbitrary jointly-surjective scheme morphisms by the existing sheaf
conservativity theorem and the cohomology criterion; no source declaration is moved. Their constructions are unchanged:
`etaleCompactificationGraphMap`, `compactSupportDerivedComparison`, all exchange maps,
and the inverse natural transformation remain exactly the same. The core comparison
field is eta-expanded to supply its original Noetherian arguments to the broader API.
The type of
`canonicalEtaleCompactSupportCore` and every normalization field remains unchanged.
This strengthens intermediate theorem interfaces; it changes no target signature or
meaning and introduces no choice of new data and no additional `sorry`.

Edge cases: empty source/fibre, empty base and the zero coefficient ring are included.
The exchange is an equality of actual constructed transformations. The finite-fibre
proof applies also to the empty finite morphism. Quasi-compactness of `f` is retained
explicitly where finiteness of the fibre is needed.

## Old

```lean
theorem compactSupportGraphDerivedComparison_geometric_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f) (y : X) :
    Functor.whiskerRight
        (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c))
        (upperStar (ModuleCat.{u + 1} A) (X.algClosurePoint y)).mapDerivedCategory ≫
      exactCompactSupportExchange A c (X.algClosurePoint y) =
    (exactEtaleSumExchange A f (X.algClosurePoint y)).hom ≫
      Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} A)
          (pullback.snd (X.algClosurePoint y) f)).mapDerivedCategory
        (compactSupportDerivedComparison A (pullback.fst (X.algClosurePoint y) f)
          (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)
          (etaleCompactificationGraphMap A (pullback.fst (X.algClosurePoint y) f)
            (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)))

theorem isIso_compactSupportGraphDerivedComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f) :
    IsIso (compactSupportDerivedComparison A f c
      (etaleCompactificationGraphMap A f c))

noncomputable def canonicalEtaleCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory

noncomputable def canonicalEtaleCompactSupportCore
    (A : Type (u + 1)) [CommRing A] [Finite A] : EtaleCompactSupportCore A where
  comparison := canonicalEtaleCompactSupportComparison A
  sheafComparison := fun f _ _ _ _ _ _ c => etaleCompactificationGraphMap A f c
  sheaf_normalization := fun f _ _ _ _ _ _ c M =>
    compactSupportGraphSheafComparison_normalization A f c M
  derived_normalization := by
    intro U X f hf hs hU hUc hX hXc c K
    exact compactSupportDerivedComparison_app A f c (etaleCompactificationGraphMap A f c) K
```

## New

```lean
theorem compactSupportGraphDerivedComparison_geometric_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f) (y : X) :
    Functor.whiskerRight
        (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c))
        (upperStar (ModuleCat.{u + 1} A) (X.algClosurePoint y)).mapDerivedCategory ≫
      exactCompactSupportExchange A c (X.algClosurePoint y) =
    (exactEtaleSumExchange A f (X.algClosurePoint y)).hom ≫
      Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} A)
          (pullback.snd (X.algClosurePoint y) f)).mapDerivedCategory
        (compactSupportDerivedComparison A (pullback.fst (X.algClosurePoint y) f)
          (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)
          (etaleCompactificationGraphMap A (pullback.fst (X.algClosurePoint y) f)
            (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)))

theorem isIso_compactSupportGraphDerivedComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f]
    (c : Compactification f) :
    IsIso (compactSupportDerivedComparison A f c
      (etaleCompactificationGraphMap A f c))

noncomputable def canonicalEtaleCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f]
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory

noncomputable def canonicalEtaleCompactSupportCore
    (A : Type (u + 1)) [CommRing A] [Finite A] : EtaleCompactSupportCore A where
  comparison := fun f _ _ _ _ _ _ c ↦ canonicalEtaleCompactSupportComparison A f c
  sheafComparison := fun f _ _ _ _ _ _ c => etaleCompactificationGraphMap A f c
  sheaf_normalization := fun f _ _ _ _ _ _ c M =>
    compactSupportGraphSheafComparison_normalization A f c M
  derived_normalization := by
    intro U X f hf hs hU hUc hX hXc c K
    exact compactSupportDerivedComparison_app A f c (etaleCompactificationGraphMap A f c) K
```

## Users

`tools/downstream.py` was run separately for both modules and the three changed names.
The geometric exchange theorem is directly used only by GraphDerivedIso. The two
broadened derived comparisons are used only within GraphDerivedIso; its unchanged core
constructor is used by GraphCoherence and Normalization.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange | unclaimed | Remove unnecessary Noetherian/compact-space binders; existing named hole retained. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso | unclaimed | Replace the four scheme hypotheses by quasi-compactness of the morphism; existing proof and core type retained. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | unclaimed | Unchanged core type; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Unchanged core type; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Unchanged normalization type; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleDerivedJointlySurjectiveConservative | A2 new | Fully proved general conservativity prerequisite, avoiding the import cycle. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization | A2 | Use the broader comparison, compose compact-support adjunctions, and apply right-adjoint uniqueness. |

## Status

landed 20261018T094933-L-3721634 2026-10-18 (merge of deliver/A2/WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization)
