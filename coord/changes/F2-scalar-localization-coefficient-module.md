# CategoryTheory.scalarLocalizationDerivedLinear and coefficient helpers

## Reason

The Hom comparison must import ScalarLocalizationUnderlyingTelescope. That telescope and
its module/complex colimit dependencies imported the Hom comparison solely for the
coefficient definitions, creating a cycle. Move those existing definitions to the
independent coefficient-action module, publicly re-export them from the item, and point
the three telescope consumers at that lower module. This realizes the existing
`def-weil-pbc-scalar-localization-coefficient-actions` node. Definition bodies, types,
universes, attributes, and public names are preserved. No target changes meaning.

## Old

The following declarations were in
`lean/Sheaf/CategoryTheory/ScalarLocalizationDerivedHom.lean`:

```lean
/-- Image of a compatible coefficient family is again compatible.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom).
Proof: commute each restriction with the ring-sheaf morphism, and then use the
restriction compatibility of the original family. -/
theorem scalarLocalizationSectionsMap_mem {R S : Sheaf J CommRingCat.{u}}
    (f : R ⟶ S) (a : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    (fun U ↦ f.hom.app U (a.val U)) ∈
      RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat) := by
  intro U V g
  change S.obj.map g (f.hom.app U (a.val U)) = f.hom.app V (a.val V)
  have h := ConcreteCategory.congr_hom (f.hom.naturality g) (a.val U)
  change f.hom.app V (R.obj.map g (a.val U)) =
    S.obj.map g (f.hom.app U (a.val U)) at h
  rw [← h]
  exact congrArg (f.hom.app V) (a.property g)

/-- The map of global coefficient rings induced by a ring-sheaf morphism.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
def scalarLocalizationSectionsMap {R S : Sheaf J CommRingCat.{u}} (f : R ⟶ S) :
    RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat) →+*
      RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat) :=
  (RingHom.pi (fun U ↦ (f.hom.app U).hom.comp
    ((Pi.evalRingHom (fun V ↦ R.obj.obj V) U).comp
      (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)).subtype))).codRestrict
    (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    (scalarLocalizationSectionsMap_mem f)

/-- The usual coefficient action on module-sheaf Homs, by restriction from global sections.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
@[instance_reducible]
def scalarLocalizationCoefficientLinear (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear A (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  letI : Linear (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) a
    smul_comp := fun M N P r f g ↦ Linear.smul_comp M N P (a r) f g
    comp_smul := fun M N P f r g ↦ Linear.comp_smul M N P f (a r) g }

/-- The induced coefficient action on the ordinary derived category.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
@[instance_reducible]
def scalarLocalizationDerivedLinear (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    Linear A (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :=
  letI := scalarLocalizationCoefficientLinear A R a
  DerivedCategory.instLinear A _

/-- The localized coefficient is a unit in the ring of sections of R[1/t].
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom).
Proof: the sectionwise image of t is a unit by localization. Its inverses commute
with restriction by uniqueness of inverses. Apply sheafification to this section
and its inverse; their products remain one, also for the zero ring and empty site. -/
theorem scalarLocalizationSections_isUnit (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    IsUnit ((scalarLocalizationSectionsMap
      (ringedLocalizationRingUnit R (a t))).comp a t) := by
  classical
  let b := (scalarLocalizationSectionsMap (ringedLocalizationRingUnit R (a t))).comp a t
  have hu (U : Cᵒᵖ) : IsUnit (b.val U) := by
    change IsUnit ((toSheafify J (ringedLocalizationRingPresheaf R (a t))).app U
      (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrier R (a t) U)
        ((a t).val U)))
    exact (IsLocalization.Away.algebraMap_isUnit (R := R.obj.obj U)
      (S := ringedSectionLocalizationCarrier R (a t) U) ((a t).val U)).map
        ((toSheafify J (ringedLocalizationRingPresheaf R (a t))).app U).hom
  choose c hc using fun U ↦ (hu U).exists_right_inv
  let d : RingCat.sectionsSubring
      ((ringedLocalizationRing R (a t)).obj ⋙ forget₂ CommRingCat RingCat) :=
    ⟨c, by
      intro U V g
      let ρ := (((ringedLocalizationRing R (a t)).obj ⋙
        forget₂ CommRingCat RingCat).map g).hom
      change ρ (c U) = c V
      apply (hu V).mul_left_cancel
      have hb : ρ (b.val U) = b.val V := b.property g
      calc
        b.val V * ρ (c U) = ρ (b.val U * c U) := by rw [← hb, map_mul]
        _ = 1 := by rw [hc, map_one]
        _ = b.val V * c V := (hc V).symm⟩
  exact IsUnit.of_mul_eq_one d (by ext U; exact hc U)

/-- The canonical A[1/t]-algebra structure of the localized ring sheaf.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
def scalarLocalizationCoefficientMap (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    Localization.Away t →+* RingCat.sectionsSubring
      ((ringedLocalizationRing R (a t)).obj ⋙ forget₂ CommRingCat RingCat) :=
  IsLocalization.Away.lift t
    (g := (scalarLocalizationSectionsMap (ringedLocalizationRingUnit R (a t))).comp a)
    (scalarLocalizationSections_isUnit A R a t)
```

The three adapted consumers publicly imported
`Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`.

## New

The identical declarations above are in
`lean/Sheaf/CategoryTheory/ScalarLocalizationCoefficientActions.lean`, publicly imported
by the item. The docstring blueprint links now point to their independent definition
node. Each of the three adapted consumers replaces its former public import with
`Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions`; their declarations are
unchanged. `ScalarLocalizationUnderlyingTelescope` also explicitly publicly imports
the statement dependencies previously exposed through the Hom module: site axioms,
ringed modules and section localization, tensor functoriality, the exact derived
functor interface, derived-category basics, change of rings, limits, and the
pretriangulated interface.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.ScalarLocalizationDerivedHom | F2 | Publicly re-exports the same definitions and uses them in both original statements. |
| Sheaf.CategoryTheory.ScalarLocalizationModuleColimit | unclaimed | One public import redirected to the coefficient module; all statements and proofs preserved. |
| Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore | unclaimed | One public import redirected to the coefficient module; all statements and proofs preserved. |
| Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope | unclaimed | Public import redirected to the coefficient module; statement dependencies explicitly imported; all statements and proofs preserved. |
| Sheaf.Algebra.Homology.RationalTermHomComparison | unclaimed | Uses the same coefficient action through the item's public re-export; no source change. |
| Sheaf.CategoryTheory.KoszulFibreLinearDescent | X3 | Uses `scalarLocalizationCoefficientLinear` through the item's public re-export in `KoszulFibreLinearDescentData`; its definition, theorem statement and proof are unchanged. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.AdicNormalizedFibreExactness | B9 | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.CondensedERealization | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.ConstructibleRationalHomComparison | T2 | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | P2 | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.LocalizedDirectImageComparison | S2 | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Indirect importer; relocated declarations stay publicly available; no source change. |
| Sheaf.Paper.RationalStratumIntegralModels | D9 | Indirect importer; relocated declarations stay publicly available; no source change. |

The inventory is `tools/downstream.py Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
--uses scalarLocalizationSectionsMap_mem scalarLocalizationSectionsMap
scalarLocalizationCoefficientLinear scalarLocalizationDerivedLinear
scalarLocalizationSections_isUnit scalarLocalizationCoefficientMap`, read on 2026-10-21.
The returned delivery omitted `Sheaf.CategoryTheory.KoszulFibreLinearDescent` from this
table. Its public import of the item still exposes the identical coefficient action,
so no source adaptation is needed. Its current holder is X3.
The three adapted consumers have no current claim records. Redirecting their coefficient
imports breaks the cycle; all compile against the relocated definitions.

The refreshed inventory has twenty downstream modules (five direct importers and
fifteen indirect importers), plus the item itself. The previous record's indirect
`InternalHomLocalizationComparison` importer is no longer in this current inventory.
All twenty preserve the same public coefficient definitions and statements.

For reviewer corrections with `--apply-fixes`, the delivery's change-record path is
`coord/changes/F2-scalar-localization-coefficient-module.md`, and the fix-directory
filename required by `tools/batch_land.py` is
`F2-scalar-localization-coefficient-module.change.md`. The previous landing failed
because the reviewer fix used the plain `.md` basename, which that tool does not map.

## Status

landed 20261021T154022-L-2760972 2026-10-21 (merge of deliver/F2/Sheaf.CategoryTheory.ScalarLocalizationDerivedHom)
