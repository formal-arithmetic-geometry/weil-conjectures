# AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_modelGlobalHomology

## Reason

Repair the returned restoration against the actual current source. The return at
988cd807c27 says that the path was created after the previous delivery's base
95c08b42e. Its current contents are an empty withdrawal stub, quoted below.
The previous report and change record incorrectly described a currently absent
quarantined file; the current rework table has no row for this item. The T9 return
and claim still assign the restoration, and the current DAG still attaches the
original small-model theorem to this path and requires it from the closed-stalk node.

Restore that complete proved declaration and its five private proof helpers from
the retained sandbox. Publicly import the actual provider of the original small-model
definitions, WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap,
in place of the retired Sheaf wrapper in the historical source. Preserve the full
original theorem signature, docstring and proof. The theorem is not an exact duplicate
of the upstream same-named theorem: that one takes an isomorphism to strictLocalization
and a square over strictLocalizationToBase. The unchanged current node instead uses
strictHenselizationScheme and strictHenselizationStructuralMap.

This restores an interface with a complete proof, not merely a delivery base. No data
or definition is changed, no source-library declaration is changed, and no target
meaning changes. No quarantine file is edited or deleted.

## Old

Actual current source, verbatim:

```lean
module

/-! Withdrawn: no declarations remain; use the official WeilConjectures twin. -/
```

The DAG's original-model theorem remains attached to this otherwise empty module.
The report of the previous packet instead quoted the archive's retired public import;
that was not the actual current source and has been corrected here.

## New

Public imports:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.RingTheory.Henselian
```

Restored public signature, equal to the current DAG's Lean statement after whitespace
normalization:

```lean
theorem isIso_strictHenselization_baseChange_modelGlobalHomology
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap s))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    IsIso ((Sheaf.Γ (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app K)))
```

The declaration's original complete proof and all five private helpers are restored.
The module privately imports the original-model canonical global-homology theorem,
horizontal derived pasting, derived mate comparison, injective representatives,
global sections, exact inverse-image homology, and the square comparison. There is
no sorry and no change to any mathematical definition, parent dependency or unit route.

The restored module compiles without warnings in 11.4 seconds. Its full proof has only
propext, Classical.choice and Quot.sound. A temporary original-model closed-stalk
consumer compiles in 5.2 seconds and has the same permitted axioms. That check retains
the full closed-stalk helper and the existing assembly from the current upstream
consumer, substituting only the original-model scheme/map in its interface and the
restored module import. Its signature matches the current parent node. The temporary
Lean source is excluded from the packet.

## Users

The current downstream.py census reports zero Lean importers and zero downstream
modules. Source searches of lean/Sheaf and lean/WeilConjectures confirm no direct
importer of this Sheaf module. The similarly named upstream consumer imports the
upstream model theorem and is untouched. No currently archived direct consumer file
is present at the paths cited in the old report.

The DAG parent still cites this module's node in its proof step and proof_deps:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | unclaimed; withdrawn stub with original-model DAG attachment | Its recorded statement and application remain unchanged; validated by the temporary full consumer proof. No adaptation submitted. |

No other module is adapted. The current node's statement, Lean attachment and all
five proof dependencies already describe the restored theorem and proof. Unit
sk-thm-p1 and its realized statements and steps are preserved. No node is deleted
or detached, and no module is withdrawn.

## Status

landed 20261021T204028-L-3921954 2026-10-21 (merge of deliver/T9/Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology)
