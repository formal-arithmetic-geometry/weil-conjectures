# AlgebraicGeometry.Etale.torModelCoefficientRing and scalar-restriction interface

## Reason

Separate the scalar-restriction interface, its equivalence proof, and its natural identity comparison from the Tor-amplitude assembly so the tensor comparison can import the interface without an import cycle. The same four definitions and the additive instance retain their names, types, values and public visibility. The item publicly imports the new module. The coefficient-ring abbreviation becomes a semireducible definition with exactly its previous body, avoiding eager expansion of constant-ring sheafification during typeclass inference. This changes elaboration transparency only; it does not change the coefficient object, tensor, amplitude, representative, pullback quantifiers, or any target meaning. The new identity comparison is constructed explicitly on sections, with no arbitrary existence witness.

## Old

Located in lean/Sheaf/AlgebraicGeometry/TorAmplitudeKFlatResolution.lean:

```lean
/-- The constant commutative coefficient ring on the small etale site.
Source: Stacks Tag 0F1M (blueprint: lem-kun-0f1m). -/
abbrev torModelCoefficientRing (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology CommRingCat.{u + 1} :=
  (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- Forget commutativity of the constant coefficient sheaf.
Source: Stacks Tag 0F1M (blueprint: lem-kun-0f1m). -/
abbrev torModelRing (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology RingCat.{u + 1} :=
  (sheafCompose T.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (torModelCoefficientRing Λ T)

/-- The unit from constant scalars to the constant ring sheaf.
Source: Stacks Tag 0H7J, used in 0F1M (blueprint: lem-kun-0f1m). -/
def torModelScalarUnit (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    (Functor.const T.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ (torModelRing Λ T).obj :=
  Functor.whiskerRight
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of Λ)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the action to constant scalars, keeping the underlying sheaf and maps.
Source: Stacks Modules on Sites, Section 093I, and Tag 0F1M
(blueprint: lem-kun-0f1m). -/
def torModelRestriction (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (torModelRing Λ T) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj M :=
    { obj :=
        { obj := fun X ↦
            ((PresheafOfModules.restrictScalars (torModelScalarUnit Λ T)).obj M.val).obj X
          map := fun f ↦
            ((PresheafOfModules.restrictScalars (torModelScalarUnit Λ T)).obj M.val).map f
          map_id := fun X ↦ by ext x; simp; rfl
          map_comp := fun f g ↦ by ext x; simp; rfl }
      property := by
        apply Presheaf.isSheaf_of_isSheaf_comp T.smallEtaleTopology _
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
        exact M.isSheaf }
  map f := ObjectProperty.homMk
    { app := fun X ↦ (ModuleCat.restrictScalars
        ((torModelScalarUnit Λ T).app X).hom).map (f.val.app X)
      naturality := fun {_ _} g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x }
  map_id M := by ext X x; rfl
  map_comp f g := by ext X x; rfl

```

The public additive instance follows these definitions, with its existing signature.

## New

Located in lean/Sheaf/AlgebraicGeometry/TorModelRestriction.lean, and publicly re-exported by the original module:

```lean
/-- The constant commutative coefficient ring on the small etale site.
Source: Stacks Tag 0F1M (blueprint: lem-kun-tor-model-restriction). -/
def torModelCoefficientRing (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology CommRingCat.{u + 1} :=
  (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- Forget commutativity of the constant coefficient sheaf.
Source: Stacks Tag 0F1M (blueprint: lem-kun-tor-model-restriction). -/
abbrev torModelRing (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology RingCat.{u + 1} :=
  (sheafCompose T.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (torModelCoefficientRing Λ T)

/-- The unit from constant scalars to the constant ring sheaf.
Source: Stacks Tag 0H7J, used in 0F1M (blueprint: lem-kun-tor-model-restriction). -/
def torModelScalarUnit (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    (Functor.const T.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ (torModelRing Λ T).obj :=
  Functor.whiskerRight
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of Λ)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the action to constant scalars, keeping the underlying sheaf and maps.
Source: Stacks Modules on Sites, Section 093I, and Tag 0F1M
(blueprint: lem-kun-tor-model-restriction). -/
def torModelRestriction (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (torModelRing Λ T) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj M :=
    { obj :=
        { obj := fun X ↦
            ((PresheafOfModules.restrictScalars (torModelScalarUnit Λ T)).obj M.val).obj X
          map := fun f ↦
            ((PresheafOfModules.restrictScalars (torModelScalarUnit Λ T)).obj M.val).map f
          map_id := fun X ↦ by ext x; simp; rfl
          map_comp := fun f g ↦ by ext x; simp; rfl }
      property := by
        apply Presheaf.isSheaf_of_isSheaf_comp T.smallEtaleTopology _
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
        exact M.isSheaf }
  map f := ObjectProperty.homMk
    { app := fun X ↦ (ModuleCat.restrictScalars
        ((torModelScalarUnit Λ T).app X).hom).map (f.val.app X)
      naturality := fun {_ _} g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x }
  map_id M := by ext X x; rfl
  map_comp f g := by ext X x; rfl

```

The same public additive instance is proved by pointwise addition. The new module also proves that restriction is an equivalence by its explicit natural identity comparison with the existing constant-scalar realization. Existing theorem signatures are unchanged.

## Users

Recomputed on the current source with `tools/downstream.py` on 2026-10-22.
The original large consumer list predates the sync and is replaced by this current list.
No downstream module refers directly to the moved scalar declarations. Both downstream
modules are checked unchanged against the packet; no source adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | unclaimed | Private import; statements unchanged |
| Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction | unclaimed | Transitive import; statements unchanged |
| Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution | S3 | Own item; public re-export; same theorem signature |

## Status

landed 20261021T214853-L-1874809 2026-10-21 (merge of deliver/S3/Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution)
