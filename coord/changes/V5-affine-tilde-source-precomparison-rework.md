# AlgebraicGeometry.affineTildeTensorSourcePrecomparison

## Reason

Restore the quarantined precomparison module from `coord/rework.tsv` by
consolidating its duplicate implementation with the complete adopted source
implementation. The source already proves precisely the archived theorem.
The earlier W2 prebase repair already re-exported the source prebase data and
generic comparison helpers, and made `affineTildeFunctor` an abbreviation of
`affinePushforwardTilde`. Re-declaring the precomparison is unnecessary and
would retain obsolete local elaboration setup.

No file under `lean/WeilConjectures/` is changed. The quarantine archive is
untouched. The old import path is restored as a public compatibility interface;
it is not withdrawn or replaced by an empty module.

## Old

The archive defines the following public theorem, followed by its complete proof:

```lean
theorem affineTildeTensorSourcePrecomparison
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)
    let qs := HomotopyCategory.quotient (Spec (.of R)).Modules (.up ℤ)
    ∃ χpre : (affineTildeFunctor B).mapDerivedCategory.obj
        (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).obj M)))) ≅
      (derivedPullback g).obj (DerivedCategory.Q.obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M))),
      χpre.hom ≫ (SingleComplexBaseChange.counit g).app
          (qs.obj (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
              (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M))) =
        affineTildeTensorDerivedCounit R A B D M m
          (affineTildeFunctor B).mapDerivedCategory rfl ≫
          DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom
```

It also declares eight local elaboration instances, sets the two backwards
transparency options, and locally marks `derivedPullback` irreducible together
with the other comparison constructions. Its five public imports are retained
verbatim by the restored module.

## New

The module adds one public import:

```lean
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre
```

The imported theorem retains the same fully qualified name and complete proof.
Its displayed tilde is `affinePushforwardTilde`; the old
`affineTildeFunctor` reduces to exactly that abbreviation. Its unused `let H`
binder is named `_H`. After these two substitutions, the entire archived
theorem, including its proof, is identical to the source declaration after
whitespace normalization. There is no new existential witness, definition,
axiom, or proof obligation.

All eight old local instance names are supplied by that same source module.
Their displayed tilde abbreviations are definitionally the same. The old
universe-sensitive abelian-instance proof is replaced by the source proof
`inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))`. The restored
interface needs none of the archived local option or irreducibility commands.

The mathematical route of
`lem-pc-affine-tilde-tensor-source-comparison` is unchanged. This node remains
attached to the main source-comparison theorem in its separate module; this
helper restoration changes neither that attachment nor its dependencies. The
K-flat resolution, scalar-extension comparison, and counit naturality argument
are preserved verbatim in the adopted implementation. No target definition
changes its meaning and no unit route is bypassed.

## Users

`tools/downstream.py` with `--allow-missing --direct --uses
affineTildeTensorSourcePrecomparison` reports no active importers: the item
and its sole direct consumer remain quarantined. A search of both `lean/` and
`quarantine/` finds the following consumer. Its current claim record is absent.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal | unclaimed | Quarantined; its two uses of the unchanged precomparison are supplied through the restored public import. No adaptation is needed. |

The consumer-signature check imports the restored module, states the archived
precomparison type verbatim under a fresh private name, and applies the
re-exported source theorem. Its local elaboration instances have fresh names
to avoid colliding with the source module's eight existing names, and use the
same displayed sheaf-universe abelian instance. It also checks the theorem's
axioms. Scratch checks are not part of the delivered library. The independent
reader can repeat this check and compare the two implementations directly.

## Status

landed 20261021T165943-L-2314343 2026-10-21 (merge of deliver/V5/Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre)
