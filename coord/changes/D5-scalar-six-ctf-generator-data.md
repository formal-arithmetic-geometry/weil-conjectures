# ScalarSixCtf canonical generator definitions

## Reason

Factor the two existing data definitions out of the assembly module so new independent
proof-step modules can use them without an import cycle. Their names, signatures,
attributes and bodies are unchanged. The original module publicly reexports them.
No target changes meaning and no consumer needs adaptation.

## Old

In Sheaf.SixFunctors.ScalarSixCtf:

```lean
def sfbLocallyClosedDerivedExtension (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {S : Scheme.{u}} (a : S ⟶ X.left) (ha : IsImmersion a) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X S) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left) :=
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  (openImmersionLowerShriek Λ.X a.toImage).mapDerivedCategory ⋙
    (lowerStar Λ.X a.imageι).rightDerivedFunctor

/-- The generators a_!P with locally perfect scalar models, up to derived isomorphism.
Source: blueprint scalar-six-ctf (1)
(blueprint: det-prop-scalar-six-ctf). -/
def sfbPerfectScalarGenerator (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    ObjectProperty (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)) :=
  fun K ↦ ∃ (S : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S)),
    IsLocallyPerfectScalarModel Λ.X S P ∧
      Nonempty (K ≅ (sfbLocallyClosedDerivedExtension Λ a ha).obj P)
```

## New

The identical declarations above live in Sheaf.SixFunctors.ScalarSixCtfGenerators.
The original module adds:

```lean
public import Sheaf.SixFunctors.ScalarSixCtfGenerators
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.ScalarSixCtf | D5 | Uses the identical definitions through public import. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Public declarations reexported unchanged. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed | Public declarations reexported unchanged. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | Public declarations reexported unchanged. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | Public declarations reexported unchanged. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | Public declarations reexported unchanged. |

The two tools/downstream.py --uses queries each found only the assembly module as a
textual user. All five downstream importers retain the same visible interface.
The five new proof-step modules import the data module directly; they are D5 additions.
No WeilConjectures file is changed.

## Status

landed 20261025T201625-L-2587893 2026-10-25 (merge of deliver/D5/Sheaf.SixFunctors.ScalarSixCtf)
