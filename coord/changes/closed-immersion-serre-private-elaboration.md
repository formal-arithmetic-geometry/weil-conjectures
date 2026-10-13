# exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion

## Reason

The ring-general proof needs private helper declarations with local variables and open commands.
The conservative interface check classifies changes in these commands as an interface change.
No public declaration, definition, instance, notation, attribute, public import, or theorem type
changes. Every new declaration is private. The additional namespace and variable commands only
supply parameters and name resolution while elaborating those private helpers. This record
makes the flagged command changes reviewable; there is no changed mathematical notion.

## Old

The public theorem signature is:

```lean
theorem exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ t₀ : ℕ, ∀ (p t : ℕ), 0 < p → t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (tensorObj F (ProjectiveSpace.twistRestrict i t)))
```

The outer commands were `universe u`, `open CategoryTheory CategoryTheory.Limits`, and
`namespace AlgebraicGeometry.Scheme.Modules`; there were no private helper variables.

## New

The identical public theorem signature is:

```lean
theorem exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ t₀ : ℕ, ∀ (p t : ℕ), 0 < p → t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (tensorObj F (ProjectiveSpace.twistRestrict i t)))
```

The outer open also names MonoidalCategory. The equivalent nested namespaces are
AlgebraicGeometry, then Scheme.Modules. Private helpers live in AlgebraicGeometry.RingTwistCech,
with `open ProjectiveSpace Scheme.Modules Opposite MvPolynomial`, variables `{n : Type u}`,
`[Fintype n]`, `(k : Type u) [CommRing k] (m : Z)`, binder updates `{k m}`, and scoped variable
updates on the comparison definitions. `omit [Fintype n] in` excludes the section instance from
the private finite-coordinate vanishing theorem. All such commands affect elaboration in this
file only; there are no new global instances. The helper declarations are explicit constructions
or complete proofs, with no holes. Removed and added proof-only imports are named in the report.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing --uses
exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion` lists 213 transitive importers
and two textual uses, including the item's own declaration. No importer needs adaptation:
the existing theorem type and all public imports are identical. The sole external application
at CoherentSerreVanishing's residue-class step still applies the theorem to the same module.
All five Challenge targets keep their statements and definitions unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing | E1 | Sole existing public signature identical; proof completed; only private helpers added. |
| Sheaf.AlgebraicGeometry.CoherentSerreVanishing | unclaimed | Application unchanged; no source changes or adaptation needed. |

## Returned-delivery repair

All five source lemmas identified in return X-3b543 elaborate with a `[Field k]` binder,
as checked through `#check @AlgebraicGeometry.ProjectiveSpace.<name>`. The five corresponding
private lemmas here now have an explicit `[CommRing k]` binder (and explicit `n`, `Fintype n`,
and `m` binders where used) and `ring_` names. Thus their signatures visibly record their
strictly more general coefficient assumption. The original public statement and all source
library declarations remain unchanged. No forced adaptations are needed.

## Status

landed 20261013T060414-L-582346 2026-10-13 (merge of deliver/E1/Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing)
