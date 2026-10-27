# Profinite.CondensedAction.InternalBarCharacter shared data

## Reason

Move the existing concrete complex and component definitions from the assigned item to a
new publicly reexported data module. This permits the three independent proof steps to
import the definitions without an import cycle through the theorem they help prove.
No existing declaration changes its name, universe, type, attributes, or definition body.
The additional recursive ordered composite and augmentation are actual constructions.

## Old

The following declarations are defined in `Sheaf.CategoryTheory.InternalBarCharacterLifts`:
`chains`, `complex`, `termIso`, `component`, `IsLift`, `augmentedComponent`,
`cocycleComponent`, all in namespace `Profinite.CondensedAction.InternalBarCharacter`.
Their signatures and bodies are precisely the seven blocks moved verbatim to
`Sheaf.CategoryTheory.InternalBarCharacterData` (only the blueprint docstring tags change).
The original module has a single postponed theorem `exists_lifts`.

```lean
def chains (D : Resolution A.toMon G) : ChainComplex (Modules A.toMon) ℕ

def complex (D : Resolution A.toMon G) : CochainComplex (Modules A.toMon) ℤ

def termIso (D : Resolution A.toMon G) (n : ℕ) :
    (complex D).X (-(n : ℤ)) ≅ (D.objects n).module

def component (D : Resolution A.toMon G) {q : ℕ}
    (f : complex D ⟶ (complex D)⟦(q : ℤ)⟧) (n : ℕ) :
    (D.objects (n + q)).module ⟶ (D.objects n).module

def IsLift (D : Resolution A.toMon G) (a : Character A G)
    (L : complex D ⟶ (complex D)⟦(1 : ℤ)⟧) : Prop

def augmentedComponent (D : Resolution A.toMon G)
    (e : complex D ⟶ (HomologicalComplex.single (Modules A.toMon) (.up ℤ) 0).obj
      (Mod.regular A.X)) {q : ℕ} (Fq : complex D ⟶ (complex D)⟦(q : ℤ)⟧) :
    (D.objects q).module ⟶ Mod.regular A.X

def cocycleComponent {H : CategoryTheory.CondensedBar.InternalFunctions A}
    (B : CategoryTheory.CondensedBar.BarDiagram (G := G) H) {q : ℕ}
    (c : (HomologicalComplex.single (Modules A.toMon) (.up ℤ) (q : ℤ)).obj
      (Mod.regular A.X) ⟶ CategoryTheory.CondensedBar.extend
        ((CategoryTheory.CondensedBar.cochains B).obj
          ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)))) :
    Mod.regular A.X ⟶ (H.functor (CategoryTheory.CondensedBar.power G q)).obj
      (Mod.regular A.X)
```


## New

The same seven declarations are defined in `Sheaf.CategoryTheory.InternalBarCharacterData`.
The original module publicly imports it, with all previous public imports retained.
Their signatures and bodies are unchanged. `Lifts` and `exists_lifts` remain in the item.

```lean
def chains (D : Resolution A.toMon G) : ChainComplex (Modules A.toMon) ℕ

def complex (D : Resolution A.toMon G) : CochainComplex (Modules A.toMon) ℤ

def termIso (D : Resolution A.toMon G) (n : ℕ) :
    (complex D).X (-(n : ℤ)) ≅ (D.objects n).module

def component (D : Resolution A.toMon G) {q : ℕ}
    (f : complex D ⟶ (complex D)⟦(q : ℤ)⟧) (n : ℕ) :
    (D.objects (n + q)).module ⟶ (D.objects n).module

def IsLift (D : Resolution A.toMon G) (a : Character A G)
    (L : complex D ⟶ (complex D)⟦(1 : ℤ)⟧) : Prop

def augmentedComponent (D : Resolution A.toMon G)
    (e : complex D ⟶ (HomologicalComplex.single (Modules A.toMon) (.up ℤ) 0).obj
      (Mod.regular A.X)) {q : ℕ} (Fq : complex D ⟶ (complex D)⟦(q : ℤ)⟧) :
    (D.objects q).module ⟶ Mod.regular A.X

def cocycleComponent {H : CategoryTheory.CondensedBar.InternalFunctions A}
    (B : CategoryTheory.CondensedBar.BarDiagram (G := G) H) {q : ℕ}
    (c : (HomologicalComplex.single (Modules A.toMon) (.up ℤ) (q : ℤ)).obj
      (Mod.regular A.X) ⟶ CategoryTheory.CondensedBar.extend
        ((CategoryTheory.CondensedBar.cochains B).obj
          ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)))) :
    Mod.regular A.X ⟶ (H.functor (CategoryTheory.CondensedBar.power G q)).obj
      (Mod.regular A.X)
```

The data module additionally constructs `orderedIterate` by right recursion and
`barAugmentation` by extending the chain augmentation. Its proved lemmas give the
recursion equations, augmentation normalization, degree-zero vanishing and sole-component
vanishing. These additions do not change any existing definition.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InternalBarCharacterLifts | R4 | Definitions available through public reexport; identical existing signatures and definition bodies. Proof now assembles three smaller arguments. |

There are no current direct Lean importers of the item (checked with `rg` on the shared
library). This is not a withdrawal: unfinished DAG parents still need the item, which is
preserved. The dependency and unit records are retained. No other existing module is
changed, and there is no target statement or target-definition change.

## Status

landed 20261026T082841-L-2231382 2026-10-26 (merge of deliver/R4/Sheaf.CategoryTheory.InternalBarCharacterLifts)
