# PresheafOfModules.exists_pullback_monoidal_normalized

## Reason

The chosen presheaf pullback has no sectionwise monoidal API. This proved theorem constructs
that API from the existing sectionwise change-of-rings presheaf, then transports it along
the unique comparison between left adjoints. The assigned global-section theorem composes
it with the constant functor and module sheafification.

## Old

No declaration. No existing signature, definition, attribute or public import changes.

## New

```lean
theorem exists_pullback_monoidal_normalized
    {C : Type u} [SmallCategory C]
    (R S : Cᵒᵖ ⥤ CommRingCat.{u})
    (φ : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      (𝟭 C).op ⋙ (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    ∃ mon : (pullback.{u} φ).Monoidal,
      letI := mon
      ∀ (X : Cᵒᵖ) (r : R.obj X),
        ((pullbackPushforwardAdjunction φ).homEquiv _ _
          (Functor.OplaxMonoidal.η (pullback φ))).app X r = φ.app X r
```

The proof imports are private. All supporting constructions are private to the new module.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.GlobalSectionModuleOplaxNormalized | P2 | Uses the new theorem in its proof. |

No existing interface is changed; existing consumers keep their statements and definitions.

## Status

landed 20261026T130612-L-3481778 2026-10-26 (merge of deliver/P2/Sheaf.Paper.GlobalSectionModuleOplaxNormalized)
