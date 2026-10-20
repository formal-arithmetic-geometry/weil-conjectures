# Retirement of AffineSheafResolutionOfRingModel

## Reason

The queue assigns this module as kind `retire` (zero holes). Follow the human's
2026-10-20 retirement instruction in `coord/changes/retire-sheaf-twins-20261020.md`.
The original resolution theorem exists with exactly the same statement in
`WeilConjectures.AlgebraicGeometry.AffineSheafResolutionOfRingModel`.
The two extra public homology declarations also exist with exactly the same
statements in `WeilConjectures.AlgebraicGeometry.AffineSheafResolutionOfRingModelExtension`.
Thus the previously recorded missing-API obstacle is resolved by importing the extension.

## Old

The withdrawn Sheaf module declares:

```lean
theorem exists_affine_sheaf_resolution_of_ring_model {T : Scheme.{u}} (U : T.Opens) [IsAffine U.toScheme] (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ) (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent) (P : CochainComplex (ModuleCat.{u} (U.toScheme.ringCatSheaf.obj.obj (.op ⊤))) ℤ) (hP : P.IsStrictlyLE d) (hfree : ∀ i : ℤ, Module.Free (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) (P.X i) ∧ Module.Finite (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) (P.X i)) (f : P ⟶ ((SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf (.op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) [QuasiIso f] : ∃ Q : CochainComplex U.toScheme.Modules ℤ, Q.IsStrictlyLE d ∧ (∀ n : ℤ, ∃ r : ℕ, Nonempty (Q.X n ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧ ∃ e : Q ⟶ C, QuasiIso e

def sectionsHomologyIso {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D] (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (unit : 𝟭 C ≅ L ⋙ R) (ε : R ⋙ L ⟶ 𝟭 D) (K : CochainComplex D ℤ) (hε : ∀ n : ℤ, IsIso (ε.app (K.X n))) (n : ℤ) : ((R.mapHomologicalComplex (.up ℤ)).obj K).homology n ≅ R.obj (K.homology n)

theorem nonempty_affineSectionsHomologyIso (X : Scheme.{u}) [IsAffine X] (K : CochainComplex X.Modules ℤ) (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) (n : ℤ) : Nonempty ((((SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤)).mapHomologicalComplex (.up ℤ)).obj K).homology n ≅ (SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤)).obj (K.homology n))
```

The consumer imported:

```lean
public import Sheaf.AlgebraicGeometry.AffineSheafResolutionOfRingModel
```

## New

Withdraw the duplicate module through `deleted.txt`. Every public declaration above
is retained upstream, unchanged; the first is in the base module and the last two
are in its extension. No upstream source file is edited.

The consumer now imports:

```lean
public import WeilConjectures.AlgebraicGeometry.AffineSheafResolutionOfRingModel
public import WeilConjectures.AlgebraicGeometry.AffineSheafResolutionOfRingModelExtension
```

Update the node's Lean attachment to the upstream resolution theorem. Its statement,
proof plan, dependencies and unit route stay unchanged. No target definition or
statement changes meaning, so no target statement review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel | unclaimed | Replace one public import by the upstream base and extension imports; all declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProperCohomologyFiniteFreeResolution | retired before this delivery | No file remains to adapt; its upstream replacement already imports the upstream resolution module. |
| Sheaf.AlgebraicGeometry.AffineSheafResolutionOfRingModel | S3 | Withdraw the duplicate declarations. |

The only current direct importer is DescentFirstProperFlatCechModel. The source
scan finds the homology theorem's use there; its call is unchanged. No module calls
sectionsHomologyIso directly outside its defining module and extension. The upstream
ProperCohomologyFiniteFreeResolution uses the upstream resolution theorem already.
The adapted consumer compiles through lcompile.py (11.2 seconds, no diagnostics).
The three public signatures were compared using the project's declaration parser
and all match verbatim. The consumer's source import closure is checked for new
twin clashes before delivery.

## Status

landed 20261020T145538-L-2409803 2026-10-20 (merge of deliver/S3/Sheaf.AlgebraicGeometry.AffineSheafResolutionOfRingModel)
