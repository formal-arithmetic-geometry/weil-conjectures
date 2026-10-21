# AlgebraicGeometry.exists_affineTildeTensorSourceComparisonCore

## Reason

Restore the quarantined item recorded in `coord/rework.tsv` by consolidating
its duplicate implementation with the complete adopted source implementation.
The two public imports from the archive are retained, and the adopted core-final
module is publicly imported to supply the existing theorem under its original
fully qualified name. No source-library file or quarantine archive is changed.
The restored module is an importable compatibility interface, not a withdrawal.

The prerequisite precomparison and associated-sheaf repairs have already
consolidated their duplicate declarations. In particular, `affineTildeFunctor A`
is an abbreviation of `affinePushforwardTilde A`. After replacing that
abbreviation, the entire archived public theorem, including its proof, is
identical to the adopted implementation after whitespace normalization. The
historical twin-retirement entry marking this module DIFFERENT therefore no
longer requires a second implementation of the theorem.

## Old

The archive publicly imports:

```lean
public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
```

It declares the following theorem with a complete proof:

```lean
theorem exists_affineTildeTensorSourceComparisonCore
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (F₀ : DerivedCategory.{wM} (ModuleCat.{u} B) ⥤
      schemeDerivedCategory.{u, w} (Spec (.of B)))
    (hF₀ : F₀ = Functor.mapDerivedCategory.{wM, w} (affineTildeFunctor B)) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)
    ∃ χ : F₀.obj
          (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
            (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
              (.up ℤ)).obj M)))) ≅
        (derivedPullback g).obj ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj H)),
      ∀ (φ : A →+* D) (ψ : B →+* D)
        (hw : Spec.map (CommRingCat.ofHom φ) ≫ f =
          Spec.map (CommRingCat.ofHom ψ) ≫ g),
        let p := Spec.map (CommRingCat.ofHom φ)
        let f' := Spec.map (CommRingCat.ofHom ψ)
        χ.hom ≫ schemeDerivedBaseChangeMap f f' g p hw (DerivedCategory.Qh.obj H) ≫
          (schemeDerivedDirectImage f').map ((SingleComplexBaseChange.counit p).app H) =
        affineTildeTensorDerivedCounit R A B D M m F₀ hF₀ ≫
          DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom ≫
          DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p hw).app H) ≫
          (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
            (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H)
```

The archive also declares eight local elaboration instances, the proved private
helper `normalized_unit_exchange`, and local transparency/irreducibility setup.
The abelian instance uses the universe-sensitive expression
`SheafOfModules.instAbelian Y.ringCatSheaf`. It locally marks the now globally
irreducible `derivedPullback` irreducible again.

## New

Retain the two public imports above and add:

```lean
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal
```

The adopted module supplies the theorem above with `affinePushforwardTilde`
in place of its definitionally equal abbreviation `affineTildeFunctor`.
Its eight local instance declarations have the same names and displayed
category types. Its abelian instance uses the explicit universe:

```lean
inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))
```

The adopted proof retains the counit-normalized precomparison, invertibility
of the actual affine right-derived pushforward unit, and the pinned derived
base-change unit compatibility. No new witness, data construction, proof
obligation, target definition, or mathematical hypothesis is introduced.
Its private generic associativity helper is proved in the source module.
The compatibility module needs no duplicate instances, helper or local options.

The DAG node `lem-pc-affine-tilde-tensor-source-comparison` remains attached to
`AlgebraicGeometry.exists_affineTildeTensorSourceComparison` in the separate
main comparison module. Its statement, dependency lists and proof route are
unchanged. The quarantined parent still needs this item; it is not pruned.

## Users

`tools/downstream.py` with `--allow-missing --direct --uses
exists_affineTildeTensorSourceComparisonCore` reports zero active direct
importers, because the sole Sheaf consumer remains quarantined. Searches of
both `lean/Sheaf` and `quarantine/Sheaf` identify the consumer below. Its claim
file is absent at the time of this check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison | unclaimed | Quarantined; the restored public import supplies its unchanged core theorem. No interface adaptation is needed. |

Consumer checks restate the archived core signature under a fresh private
name and apply the re-exported theorem. A second scratch check uses the
quarantined parent's unchanged signature and original proof. Scratch local
instances have fresh names to avoid the adopted instance names, and use the
explicit-universe abelian instance above. These checks are not library modules
in the packet. The independent reviewer can repeat them directly from the
archives and inspect the full source proof. An import-direction check accepts
the additional public import.

Validation with `lcompile.py --all` passed for the restored module and both
scratch consumer checks. `#print axioms` for the adopted core theorem, the
archived core signature and the archived consumer proof reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The restored module compiled in 5.1 seconds. Scratch modules have been removed
from the delivery's `lean/` tree after validation.

## Status

landed 20261021T174252-L-3775916 2026-10-21 (merge of deliver/T7/Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal)
