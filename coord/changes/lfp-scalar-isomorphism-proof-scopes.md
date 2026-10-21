# AlgebraicGeometry.ProEtale.isLocallyFinitelyPresented_comap_iff_sameCover

## Reason

The new proof uses private, fully proved helpers. Declaration-local `omit` commands
remove unused commutativity assumptions from their inferred signatures. The original
public theorem keeps both commutativity assumptions: its statement already mentions
the scalar-extension construction, and the original section variables are unchanged.
The shorter proof does not use commutativity of S, so a declaration-local
`set_option linter.unusedSectionVars false in` suppresses that warning while keeping
the original public interface. This setting affects only lint, never kernel checking.
Preflight classifies these commands as a scope change and requires this record.

## Old

```lean
variable {X : Scheme.{u}}
variable {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
```

The public statement is:

```lean
theorem isLocallyFinitelyPresented_comap_iff_sameCover
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S} :
    (IsLocallyFinitelyPresented S N ↔
        IsLocallyFinitelyPresented R ((Mod.comap φ).obj N)) ∧
      (∀ (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (i : 𝒰.I₀)
          (m n : ℕ),
        (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj S) m ⟶
            Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj S) n,
          Nonempty
            ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod S).obj N) ≅
              cokernel f)) ↔
          (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj R) m ⟶
            Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj R) n,
          Nonempty
            ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj
              ((Mod.comap φ).obj N)) ≅ cokernel f))) ∧
      (∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
        (IsLocallyFinitelyPresented R M ↔
          IsLocallyFinitelyPresented S ((Mod.extendScalars φ).obj M)) ∧
        ∀ (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (i : 𝒰.I₀)
            (m n : ℕ),
          (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj R) m ⟶
              Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj R) n,
            Nonempty
              ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj M) ≅
                cokernel f)) ↔
            (∃ f : Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj S) m ⟶
              Mod.finiteFree ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj S) n,
            Nonempty
              ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod S).obj
                ((Mod.extendScalars φ).obj M)) ≅ cokernel f)))
```

## New

The section variables and public statement above remain verbatim. Only the following
local modifiers are added around the indicated declarations:

```lean
omit [IsCommMonObj R] [IsCommMonObj S] in
```

This applies individually to `presentation_comap`, `presentation_comap_iff`,
`presentation_mapMod_comap_iff`, and `lfp_comap_iff`, all private proved helpers.

```lean
set_option linter.unusedSectionVars false in
```

This applies only to the existing public theorem. No public declaration, attribute,
instance, definition, signature, or import changes. No target definition changes.

## Users

`tools/downstream.py` reports zero downstream modules and the item itself as the
only textual use of its public theorem. Public import lists are identical.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.ModuleObjects.LfpScalarIsomorphism | T2 | Proof closes its only hole; local scope and lint modifiers described above. |

## Status

landed 20261021T120532-L-3907480 2026-10-21 (merge of deliver/T2/Sheaf.CategoryTheory.ModuleObjects.LfpScalarIsomorphism)
