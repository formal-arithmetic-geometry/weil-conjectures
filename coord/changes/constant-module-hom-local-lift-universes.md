# CategoryTheory.finitePresentation_linearLiftSieve_mem

## Reason

The assigned internal Hom theorem permits independent object and arrow universes. The
existing local linear lifting lemma unnecessarily identifies them with the coefficient
universe. Generalize its universe parameters and reuse the original proof, instead of
maintaining a second copy of the finite-presentation argument.

## Old

```lean
universe u
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {Λ : Type u} [CommRing Λ] {M N : ModuleCat.{u} Λ}
  {P : Cᵒᵖ ⥤ ModuleCat.{u} Λ} (η : (Functor.const Cᵒᵖ).obj N ⟶ P)
```

The declarations `linearLiftSieve` and `finitePresentation_linearLiftSieve_mem`
use these section variables. Their bodies and explicit statement text are unchanged.

## New

```lean
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ] {M N : ModuleCat.{w} Λ}
  {P : Cᵒᵖ ⥤ ModuleCat.{w} Λ} (η : (Functor.const Cᵒᵖ).obj N ⟶ P)
```

Both declarations now allow these independent universes. All old uses specialize
`v = w = u`; their mathematical meaning and inferred types stay the same.
No target statement or definition is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.FinitePresentationLocalLift` | unclaimed | Generalized parameters only; original construction and proof retained. |
| `Sheaf.CategoryTheory.SiteConstantModuleHomSurjective` | unclaimed | Sole pre-existing direct importer and sole external textual user of the theorem; specializes the generalized parameters to its original universe. No source adaptation. |
| `Sheaf.CategoryTheory.SiteConstantModuleHom` | Q9 | Assigned item; uses the generalized theorem with site universes u,v and coefficient universe max u v. |

Both required downstream checks completed in this session:

- `tools/downstream.py Sheaf.CategoryTheory.FinitePresentationLocalLift --direct
  --uses finitePresentation_linearLiftSieve_mem` lists the one direct importer
  `Sheaf.CategoryTheory.SiteConstantModuleHomSurjective`, and finds the theorem's
  own declaration plus that consumer as its textual uses.
- A source search of both library roots for the import and both declaration names
  agrees with that list. No consumer source adaptation is needed; its original
  universe parameters specialize the generalized lemma.

The transitive importers see the same definitions and statements after specialization.

## Status

landed 20261019T005408-L-2763623 2026-10-19 (merge of deliver/Q9/Sheaf.CategoryTheory.SiteConstantModuleHom)
