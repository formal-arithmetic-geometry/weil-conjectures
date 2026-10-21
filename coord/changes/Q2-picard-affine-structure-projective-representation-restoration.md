# AlgebraicGeometry.Scheme.picard_affine_structure_projective_representation

## Reason

Restore the quarantined stage-3 item from its existing archive, as assigned by
`coord/rework.tsv`. The archive contains a complete proof and zero `sorry`s.
The landed record `A4-open-immersion-restriction-retirement.md` explicitly calls
for this archived consumer to migrate its private restriction import and its
additivity helper on restoration.

Use `WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`
in place of the retired Sheaf twin, and infer the sectionwise additive instance
instead of referring to the removed `restriction_additive` helper. Import
`WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward` directly for
`Modules.pushforwardRestrictIso`, replacing the unnecessarily broad private
`import all` of `Cohomology.DirectImage.Sections`.

No definition, public import, theorem signature or target meaning changes.
The archive and its DAG attachment and mathematical dependencies are preserved.
The proof remains the existing open-square comparison followed by proper-flat
perfectness and the affine bounded-projective characterization.

## Old

The module is absent from `lean/` and preserved at
`quarantine/Sheaf/AlgebraicGeometry/PicardAffineStructureProjectiveRepresentation.lean`.
The archived public theorem signature is:

```lean
theorem picard_affine_structure_projective_representation
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf)) :
    ∃ P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite (W.presheaf.obj (.op U)) (P.X n)) ∧
      (∀ n : ℤ, Module.Projective (W.presheaf.obj (.op U)) (P.X n)) ∧
      Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P))
```

The affected archived lines are:

```lean
import all WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties
  have : A.Additive := restriction_additive q
```

## New

The same module is restored at
`lean/Sheaf/AlgebraicGeometry/PicardAffineStructureProjectiveRepresentation.lean`.
Its public theorem signature is unchanged, verbatim:

```lean
theorem picard_affine_structure_projective_representation
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf)) :
    ∃ P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite (W.presheaf.obj (.op U)) (P.X n)) ∧
      (∀ n : ℤ, Module.Projective (W.presheaf.obj (.op U)) (P.X n)) ∧
      Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P))
```

The three lines become:

```lean
import WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward
import WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties
  have : A.Additive := inferInstance
```

The node's first proof step now names the direct `pushforwardRestrictIso` source;
its statement, attachment, dependency arrays and remaining proof steps are unchanged.

## Users

`tools/downstream.py` reports the module as unknown because its source is
quarantined. A complete text search of both `lean/` and `quarantine/`, and a
reverse-edge scan of DAG statement dependencies, proof dependencies and proof-step
uses, find one direct consumer. There are no current live Lean importers.
The consumer keeps exactly the theorem signature and public imports it expects;
no adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation | Q2 | Restore the existing proof with three environment repairs. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel | rework archive; no local claim | The existing application at line 85 has the identical theorem type; no adaptation. |

The unit `sk-prop-av-cube` has empty realized arrays. Its statement and route,
and the parent node's dependency on this item, remain intact. No target statement
or definition used by a target changes.

Validation: the restored module compiles cleanly via `lcompile.py` in 45.1 seconds.
A source comparison checks byte-for-byte equality of the public theorem signature
and all public imports against the archive. Both archive and restoration contain
zero `sorry`s, and every restored line is at most 100 characters.

## Status

landed 20261021T225204-L-3791728 2026-10-21 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation)
