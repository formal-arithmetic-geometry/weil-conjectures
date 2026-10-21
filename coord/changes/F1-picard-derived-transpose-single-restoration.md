# AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose_single

## Reason

The cluster-restore rollback quarantined this proved module. During this session
its full original source was restored independently to the live library. The
final delivery preserves that restoration and simplifies the existing private
transposeFromHomology proof, rather than submitting an unchanged copy.

Use the compatibility equality directly to transport the recovered single
morphism through the derived adjunction. This removes an intermediate congrArg
calculation and redundant equation chaining. The explicitly typed recovery of
the ordinary morphism is retained to keep elaboration bounded. The mathematical
argument, statements and definitions remain unchanged; both declarations have
zero proof holes.

## Old

The public signature, under its unchanged shared derived-category parameter, is:

```lean
variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

theorem picardDirectImageDerivedTranspose_single
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    picardDirectImageDerivedTranspose f L W k t ξ =
      Modules.canonicalSinglePullbackMap (pullback.snd f (t ≫ k))
        (SheafOfModules.unit (moduleRings T.toRingedSpace)) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace)) 0).map
          (SheafOfModules.pullbackObjUnitToUnit
            (pullback.snd f (t ≫ k)).toRingCatSheafHom ≫
              picardDirectImageUnitMorphism f L W k t ξ)
```

The original private helper contains:

```lean
  have ht : G.map m ≫ Modules.canonicalSingleDirectImageMap p N = q := by
    have he := congrArg (adj.homEquiv _ _) hb
    rw [Equiv.apply_symm_apply] at he
    exact (compat b).symm.trans he
```

## New

The public signature and the main theorem's proof are verbatim unchanged.
The corresponding private helper steps become:

```lean
  have ht : G.map m ≫ Modules.canonicalSingleDirectImageMap p N = q := by
    rw [← compat b, hb, Equiv.apply_symm_apply]
```

All imports, private and public signatures, universes, shared derived-category
parameter, documentation and elaboration settings remain unchanged. Only the
existing node's lean.by, lean.date and lean.note document this delivery. Its
attachment, statement, proof route, dependencies and unit route are retained.
The quarantine archive is preserved. There is no target-signature or
target-meaning change and no adopted-source edit.

## Users

A scan of lean/ and quarantine/, with live sources taking precedence, finds one
direct importer and sixteen consumers in total. Their theorem interfaces remain
identical and no consumer is delivered or adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback | separate quarantined rework; no local claim snapshot | Direct importer and declaration user; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored theorem, no adaptation. |

The single mathematical parent is
lem-sc-picard-direct-image-unit-morphism-pullback. Its proof and dependency lists
still cite this node. An unchanged copy of the original theorem compiled in
34.0 seconds, then in 46.0 seconds with #print axioms, which reported exactly
propext, Classical.choice and Quot.sound. The final simplified proof also
compiled cleanly in 57.1 seconds, within the single-file limit.

The original quarantined direct consumer independently fails at line 35 in its
private singlePullback_naturality helper: inside namespace Modules,
derivedPullback resolves to Scheme.Modules.derivedPullback instead of the
AlgebraicGeometry.derivedPullback used by canonicalSinglePullbackMap. The compiler
reports a Type v versus Type (v + 1) morphism mismatch. A scratch-only validation
copy qualifies this single name; the consumer then compiles in 42.8 seconds,
accepting both original uses of picardDirectImageDerivedTranspose_single. Its
archived factorization and pasting dependencies also compiled (29.0 seconds and
0.1 seconds cached). No consumer adaptation is delivered; that consumer retains
its own quarantined rework assignment. Copies under scratch/consumer-check are
validation artifacts only.

## Status

landed 20261021T061037-L-1688583 2026-10-21 (merge of deliver/F1/Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeSingle)
