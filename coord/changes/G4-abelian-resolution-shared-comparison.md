# abelianInjectiveResolutionIso

## Reason

The evaluation theorem is acyclic-comparison naturality followed by composition with
terminal-source Ext precomposition and the site-sections comparison. Repeated conversion
of the expanded prefix exceeded the standard 60-second compile limit. Construct the
prefix once as the real irreducible isomorphism `abelianExtSectionsIso`, in the G4-held
`AbelianCounitCocycleCalculation` module, and use it in that module's existing target
comparison. The original source comparison is identified with the factored composition
by a local equation in the evaluation proof, proved by `Iso.trans_assoc`.

Repair of return A3 (reviewer X-15ff5, head 15ff5cacc): removed all edits to
`ModuleCohomologyExtResolutionNormalization` from this delivery. Its original definition
of `abelianResolutionIso`, its private proofs, signatures, imports and visibility are
preserved. The helper now belongs to the already G4-held cocycle module. Both edited
modules are G4-held; no forced-adaptation exception is used.

Every existing signature, attribute and visibility is unchanged. Expanding the new
prefix and using `Iso.trans_assoc` gives the original target comparison, so its
mathematical value and every target's meaning are unchanged. The helper composes two
existing isomorphisms explicitly. It contains no postponed data, arbitrary witness,
axiom or theorem hole. The cocycle theorem and all current imports are unchanged.

## Old

```lean
@[irreducible]
def abelianInjectiveResolutionIso (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (R : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology p :=
  (Abelian.Ext.precompAddEquiv (terminalSourceIso X)
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p).toAddCommGrpIso ≪≫
    siteSectionsObjIso (Opens.grothendieckTopology X) ⊤
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p ≪≫
    (abelianSections X).rightDerivedObjIsoOfResolution R.ι
      (fun n ↦ Functor.rightAcyclic_of_injective (R.cocomplex.X n)) p
```

## New

```lean
/-- The common Ext-to-derived-sections part of the resolution comparisons.
Source: Stacks Project, Tags 03FD and 06XR. This is the composition of the
terminal-source Ext precomposition with the site-sections comparison. -/
@[irreducible]
def abelianExtSectionsIso (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
      ((abelianSections X).rightDerived p).obj
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) :=
  (Abelian.Ext.precompAddEquiv (terminalSourceIso X)
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p).toAddCommGrpIso ≪≫
    siteSectionsObjIso (Opens.grothendieckTopology X) ⊤
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p

@[irreducible]
def abelianInjectiveResolutionIso (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (R : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology p :=
  abelianExtSectionsIso X F p ≪≫
    (abelianSections X).rightDerivedObjIsoOfResolution R.ι
      (fun n ↦ Functor.rightAcyclic_of_injective (R.cocomplex.X n)) p
```

## Users

`tools/downstream.py` reports 379 downstream modules and exactly two declaration users
of `abelianInjectiveResolutionIso`, listed below. The new helper is used only by these
two delivered modules. Transitive users retain the same public imports and declarations.
The evaluation proof checks the unchanged source comparison directly by associativity.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation | G4 | Constructs the prefix and factors the existing target comparison; cocycle theorem unchanged. |
| Sheaf.AlgebraicGeometry.AbelianResolutionComparisonEvaluation | G4 | Proves the assigned evaluation using naturality and the original source comparison. |

`ModuleCohomologyExtResolutionNormalization` is not edited or delivered. None of its
users requires an adaptation. No module held by another group is edited. The unit's
statement and realized steps are preserved; no target statement changes.

## Status

landed 20261014T122435-L-2705369 2026-10-14 (merge of deliver/G4/Sheaf.AlgebraicGeometry.AbelianResolutionComparisonEvaluation)
