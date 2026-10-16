# CategoryTheory.Presheaf.hom_eq_zero_of_sheafification_zero: private proof scopes

## Reason

Complete the finite-cover local-zero proof without adding public API or holes.
The preflight conservatively classifies the added top-level universe and `omit`
commands as an interface change, so this record documents their scope and consumers.

## Old

The module declared `universe u' u`, opened `CategoryTheory Limits Opposite`, and used
this unchanged section context:

```lean
variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  (J : GrothendieckTopology C) [HasSheafify J A]
  [∀ V : C, HasFiniteProducts (Over V)]
```

The only public theorem had its existing signature and proof `by sorry`.

## New

The module declares `universe u' u w v`. The additional universes w and v are used
only in the private generic filtered-colimit helper `kills_kernel_colimit`.
The section context, namespace, open commands, three public imports, and public
`hom_eq_zero_of_sheafification_zero` signature remain exactly as before.

Private proved helpers are preceded where appropriate by the command
`omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in`, omitting hypotheses
unused by that single helper. They do not alter the surrounding context or the public
theorem. All new declarations are private; no new attributes or instances are registered.
One proof-only `import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
exposes the existing source proof dependencies needed for presentability and convergence.
The public theorem is now proved, with no other axioms beyond the three permitted ones.

## Users

`tools/downstream.py --uses hom_eq_zero_of_sheafification_zero` finds only the item
and its direct consumer. No consumer adaptation is needed. The unchanged direct
consumer was compiled against the sandbox's compiled item artifact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CategoricalFiniteCoverLocalZero | C4 | Its sole public theorem is proved with the same signature; helpers and their scope commands are private. |
| Sheaf.CategoryTheory.CategoricalFiniteCoverLocalEpi | unclaimed | Existing application of `hom_eq_zero_of_sheafification_zero` compiles unchanged. |

Every further downstream module receives the same public imports and declaration
signature. The newly declared universe names introduce no binders into the public
signature, as confirmed by the final `#check` audit. The helper `omit ... in` commands
are local to the immediately following private declaration.

## Status

landed 20261016T101204-L-2230131 2026-10-16 (merge of deliver/C4/Sheaf.CategoryTheory.CategoricalFiniteCoverLocalZero)
