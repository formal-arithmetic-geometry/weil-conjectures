# AlgebraicGeometry.exists_affineTildeTensorSourceComparison

## Reason

Restore the explicitly quarantined module in `coord/rework.tsv` using the
complete adopted source implementation. The original file fails to compile
at its local abelian instance: Lean cannot infer the sheaf universe in
`SheafOfModules.instAbelian Y.ringCatSheaf`, yielding a stuck universe constraint
and a missing `WEqualsLocallyBijective AddCommGrpCat` instance.

The source library already proves this exact comparison. The prerequisite
Sheaf core-final, precomparison, prebase, helper and normalization interfaces
have been restored and consolidated with their adopted implementations.
`affineTildeFunctor` is now an abbreviation of `affinePushforwardTilde`.
After replacing that abbreviation, the whole archived public theorem and its
proof are textually identical to the source theorem after whitespace normalization.
Re-exporting the existing proof restores the original API without duplicating
local instances or a theorem name that the source module already supplies.

The quarantine archive and all source-library files are untouched. The original
Sheaf import path is restored, not withdrawn. No target definition changes.

## Old

The archive publicly imports:

```lean
public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal
```

It declares the following theorem, with a complete proof:

```lean
theorem exists_affineTildeTensorSourceComparison
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

Its proof obtains the core comparison, chooses its isomorphism and applies the
core universal transport equation to each pair of coefficient maps. It also
contains eight local elaboration instances, including the universe-sensitive
abelian instance described above.

## New

The restored module retains its original public import and adds:

```lean
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
```

The source module supplies the theorem above under the same fully qualified name,
with the definitionally equal `affinePushforwardTilde` spelling. Its complete
proof is the archived proof. Its local instances are the same, except that the
abelian instance explicitly selects its sheaf universe:

```lean
inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))
```

The compatibility interface has no duplicate theorem or instances and introduces
no existential choice, data construction or proof obligation. The original
K-flat source-precomparison, affine pushforward-unit invertibility and universal
base-change counit transport are retained in the adopted implementation.

The node `lem-pc-affine-tilde-tensor-source-comparison` keeps its existing Lean
attachment to this restored Sheaf module and the same public theorem, statement,
proof dependencies and proof plan. It remains an input to the quarantined mate
and its parents. No node or unit route is bypassed, so no node edit is needed.

## Users

`tools/downstream.py` with `--allow-missing --direct --uses
exists_affineTildeTensorSourceComparison` reports zero live direct importers.
The item and four Sheaf consumers are quarantined; searching `quarantine/Sheaf/`
finds the following complete direct-consumer list. None has a current claim file
at the time of this check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate | unclaimed | Its call at explicit universes and the resulting universal equation retain the archived type. No forced adaptation. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange | unclaimed | Its public import regains all existing declarations. No forced adaptation. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization | unclaimed | Its public import regains all existing declarations. No forced adaptation. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain | unclaimed | Its public import regains all existing declarations. No forced adaptation. |

The corresponding source consumers import the source comparison module directly
and are unchanged. No consumer is weakened or adapted. Their separate quarantine
repairs are not claimed by this packet.

Validation via `lcompile.py --all` compiles the restored interface and two scratch
consumer checks. The first check repeats the entire archived theorem signature
and applies the re-exported theorem. The second repeats the archived theorem
proof, verifying the core API as well. Both use fresh local instance names and
the explicit-universe abelian instance, and retain the old `affineTildeFunctor`
spelling in every type and map. The checks compile in 21.3 and 44.0 seconds;
the interface compiles in 1.8 seconds. All three axiom checks report exactly
`propext`, `Classical.choice`, and `Quot.sound`. Scratch modules are excluded
from the delivery. The import-direction check accepts the added source import.

## Status

landed 20261021T182613-L-1235843 2026-10-21 (merge of deliver/W6/Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison)
