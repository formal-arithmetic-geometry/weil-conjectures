# AlgebraicGeometry.exists_compact_flat_finite_subcomplex_diagrams

## Reason

The full proof adds private helpers under two scoped sections with generic category
parameters. The textual interface checker records new `section`, `variable`, and `omit`
commands as an interface change, so this record documents those commands. Every existing
public declaration, definition, import, signature and visibility is identical. The private
instances are proof-local implementation declarations; no public instance is added.
No target definition or target statement changes meaning.

## Old

The original file has these surrounding commands, verbatim:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
```

The theorem's original proof is `:= by sorry`. There are no auxiliary sections or
category variables between the structure and the theorem.

## New

The existing surrounding commands above are unchanged. The added helper contexts are:

```lean
section FinitePieces

variable {C : Type*} [Category.{u} C] [Abelian C] [HasCoproducts.{u} C]
    {K : CochainComplex C ℤ} {I : ℤ → Type u} (G : ∀ i, I i → C)
    (e : ∀ i, K.X i ≅ ∐ G i)
```

and, after `end FinitePieces`:

```lean
section TowerPieces

variable {C : Type*} [Category.{u} C] [Abelian C] [HasCoproducts.{u} C]
    (L : ℕ → CochainComplex C ℤ) (l : ∀ n, L n ⟶ L (n + 1))
    (I : ℕ → ℤ → Type u) (G : ∀ n i, I n i → C)
    (e : ∀ n i, (L n).X i ≅ ∐ G n i)
```

This context is closed by `end TowerPieces` before the existing public theorem.
Three private tower-map lemmas use the scoped command
`omit [HasCoproducts.{u} C] in` to avoid an unused instance parameter.
A private colimit constructor uses
`set_option backward.isDefEq.respectTransparency false in`, scoped to that declaration.
All helpers, including the six named helper instances, are explicitly `private` and
contain no `sorry`. They are used only in proofs or other private helper bodies.
The existing theorem's proof is replaced with the completed construction.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams | P2 | Own proof now compiles without sorry; public API identical. |
| Sheaf.AlgebraicGeometry.CompactFlatBarUnionAugmentation | P2 | Sole direct importer; all public imports and declarations unchanged, so no adaptation. |
| Sheaf.AlgebraicGeometry.CompactFlatTelescopeBarEnlargement | unclaimed | Uses the proved existence theorem with its identical signature; no adaptation. |

The read-only downstream query found 364 transitive importers, and only the first direct
importer above mentions `CompactFlatFiniteSubcomplexDiagrams`. Scoped variables and private
helpers are not part of their public types. No downstream source needs editing and no
forced adaptation is included.

## Status

landed 20261014T092936-L-609180 2026-10-14 (merge of deliver/P2/Sheaf.AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams)
