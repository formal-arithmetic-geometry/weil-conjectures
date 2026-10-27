# AlgebraicGeometry.Etale.strictHenselizationModuleFibre_factorization

## Reason

Retire the duplicate listed at coord/retire-items.tsv row 2933, under the human hand-off
in coord/changes/retire-sheaf-twins-20261020.md. The item has zero holes. The adopted
factorization theorem is proved in the full affine-neighbourhood strictLocalization
presentation, whereas the copy uses the small representative coordinate-ring colimit.
These presentations are canonically isomorphic over the base, rather than definitionally
equal: smallStrictHenselizationColimitIso and smallStrictLocalization_toBase give the
comparison. The DAG attachment and its proof now describe the adopted presentation.

The row's sole listed consumer, Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero,
has already been retired. Its official replacement imports and applies the official
factorization theorem, using strictHenselization and strictLocalizationToBase. Thus no
consumer edit or new transport theorem is required. Source scans and tools/downstream.py
find zero current importers of the duplicate. The parent node remains attached to the
unchanged official consumer and retains its dependency on this result. The unit record
sk-lem-universal-datum has no realized entry for this node, and its route is preserved.

Read the two factorization modules, the full official consumer, all listed dependency
records and signatures, and Stacks etale-cohomology.tex theorem-higher-direct-images,
remark-stalk-fibre and lemma-proper-base-change-f-star. The last source omits the
compatibility verification; both existing Lean proofs supply that calculation.

## Old

The duplicate module exports the following signature verbatim, and a proved private
pointedStrictHenselizationLift. It contains no definition or instance.

```lean
theorem strictHenselizationModuleFibre_factorization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    [QuasiCompact f] [QuasiSeparated f]
    [IsLocalRing (strictHenselizationRing s)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (t : Spec (.of Ω) ⟶ strictHenselizationScheme s)
      (ht : t ≫ strictHenselizationStructuralMap s = s),
      t (IsLocalRing.closedPoint Ω) =
        IsLocalRing.closedPoint (strictHenselizationRing s) ∧
      ∃ (i : X' ⟶ pullback f (strictHenselizationStructuralMap s)),
        IsPullback i f' (pullback.snd f (strictHenselizationStructuralMap s)) t ∧
        i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g' ∧
      ∃ Θ : (pointSmallEtale s).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≅
          (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
            ((pullback.fst f (strictHenselizationStructuralMap s))^*[ModuleCat.{u + 1} Λ].obj F),
      ∃ b : (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
          ((i)^*[ModuleCat.{u + 1} Λ].obj
            ((pullback.fst f (strictHenselizationStructuralMap s))^*[ModuleCat.{u + 1} Λ].obj F)) ≅
          ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
        (z : F.obj.obj (op (f.Etale.obj V))),
        b.hom.hom ((globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
          ((pullback.fst f (strictHenselizationStructuralMap s))^*[ModuleCat.{u + 1} Λ].obj F)).hom
          (Θ.hom.hom ((pointSmallEtale s).toPresheafFiber V v
            ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj z))) =
        (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z
```

Its public imports are WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms,
WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap and
WeilConjectures.SixFunctors.BaseChange.GlobalSections. Its proof imports are
WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative,
Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison,
Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction,
Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps and
WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison.

## New

Withdraw the duplicate module; retain the unchanged official theorem and attach the
node to it. Its signature, copied verbatim from the adopted source, is:

```lean
theorem strictHenselizationModuleFibre_factorization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    [QuasiCompact f] [QuasiSeparated f]
    [IsLocalRing (strictHenselization s)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (t : Spec (.of Ω) ⟶ strictLocalization s)
      (_ : t ≫ strictLocalizationToBase s = s),
      t (IsLocalRing.closedPoint Ω) =
        IsLocalRing.closedPoint (strictHenselization s) ∧
      ∃ (i : X' ⟶ pullback f (strictLocalizationToBase s)),
        IsPullback i f' (pullback.snd f (strictLocalizationToBase s)) t ∧
        i ≫ pullback.fst f (strictLocalizationToBase s) = g' ∧
      ∃ Θ : (pointSmallEtale s).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≅
          (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
            ((pullback.fst f (strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F),
      ∃ b : (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
          ((i)^*[ModuleCat.{u + 1} Λ].obj
            ((pullback.fst f (strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F)) ≅
          ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
        (z : F.obj.obj (op (f.Etale.obj V))),
        b.hom.hom ((globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
          ((pullback.fst f (strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F)).hom
          (Θ.hom.hom ((pointSmallEtale s).toPresheafFiber V v
            ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj z))) =
        (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z
```

The node's presentation change is explicit in statement_change, with the active parent
checked. Its updated proof and proof_deps follow the adopted source proof, not the
withdrawn small-model proof. No upstream declaration, definition, import or target
statement changes, and no renamed duplicate or new node is introduced.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | F1 | withdraw duplicate; node attaches to official theorem |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | already absent | historical consumer in retirement row; already migrated upstream |
| WeilConjectures.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | unchanged; already imports and applies the full-model official theorem; compiled |
| WeilConjectures.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | unclaimed | unchanged; official replacement compiled |

There are no current downstream modules of the withdrawn copy. No forced adaptation
is made. The adopted consumer's local-ring hypothesis and all factorization witnesses
already use the full presentation; the conclusion and the germ-restriction equation
are unchanged. Historical references in change records are retained as history.

## Status

landed 20261022T040159-L-2826110 2026-10-22 (merge of deliver/F1/Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization)
