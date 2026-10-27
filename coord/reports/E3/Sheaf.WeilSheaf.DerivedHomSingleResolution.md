## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.derivedHom_single_resolution` with its statement unchanged. Constructed the comparison directly from the source library's equivalence between K-injectives in the homotopy category and the derived category. The lift of the equivalence counit is unique, so it gives a canonical comparison without choosing an arbitrary existential witness. Proved its resolution formula and both naturality squares, composed it with the already proved degree-zero projection and the canonical right-derived-unit isomorphism, and transported along `kInjectiveRepIso` for arbitrary targets.

Added `Sheaf.WeilSheaf.NativeHomPrecompositionQuasiIso`, proving native product-Hom precomposition preserves quasi-isomorphisms into K-injectives. The proof forgets Frobenius using exact orbit induction, compares the actual product projections, and proves ordinary module-Hom invariance by a flat separator and the signed source-cone isomorphism. All helper constructions are private and their properties are proved. The chain comparison is proved for an abstract product-preserving additive functor, then specialized to forgetting Frobenius, avoiding repeated kernel expansion of the concrete sheaf construction. Added proof imports only; the item's public imports and all existing declaration signatures are preserved.

## Proved and sorry left

Closed the item's one remaining hole, `AlgebraicGeometry.ProEtaleWeilSheaf.derivedHom_single_resolution` (node `lem-sf-weil-derived-hom-single-resolution`). Its previously proved projection lemmas are preserved.

Added and proved `AlgebraicGeometry.ProEtaleWeilSheaf.quasiIso_bifunctorHomMapLeft` (node `lem-sf-native-hom-precomposition-quasi-iso`). No holes were added; none remain in either delivered Lean module. This is a proof, not a decomposition into retained holes. The complete two-module packet compiled without warnings through `lcompile.py --all`: native invariance in 21.2 seconds and the main comparison in 46.7 seconds. The main theorem signature was checked verbatim against the assigned source.

## No longer needed

No Lean module is withdrawn, and no existing public import is removed. The item's proof no longer needs the planned `Sheaf.CategoryTheory.EquivariantHomQuasiIsomorphism` or `Sheaf.CategoryTheory.EquivariantHomResolutionCalculus` modules, corresponding to `lem-sf-equivariant-hom-quasi-isomorphism` and `lem-sf-equivariant-hom-resolution-calculus`. The former is replaced by the proved concrete native invariance lemma; the latter by direct calculations with the existing native bifunctor and K-injective equivalence. Other consumers of these modules remain unaffected.

The parent no longer directly calls `lem-pur-ringed-site-grothendieck-abelian` or `lem-sf-free-derived-weil-resolution`: source-library instances already supply the category and resolutions. These results are not withdrawn. Removed obsolete parent `tool_uses` entries for `lem-pur-ringed-site-grothendieck-abelian`, `lem-weil-pbc-right-adjoint-preserves-kinjective`, `lem-pur-rhom-well-defined`, and `lem-sf-free-derived-weil-resolution`; the right-adjoint argument is now used inside the concrete native lemma instead.

## Where the brief, the DAG or earlier work was wrong

The generic ringed-presentation invariance module already marks its final statement disputed because an underlying sheaf-of-sets comparison need not preserve scalar multiplication. Its presentation also does not directly match the native internal coefficient-module category. This delivery uses the actual native module operations, tensor-Hom adjunction and product projections; it neither assumes that disputed theorem nor changes its statement.

The source's native row-sign differential differs from the standard Hom differential. The flat-separator argument uses the existing signed cochain equivalence, and the cone argument uses the existing signed source-cone isomorphism. The source-degree-zero projection has sign +1, so all asserted normalization formulas retain the original native maps.

## New nodes

`lem-sf-native-hom-precomposition-quasi-iso` records the strictly separate source-variable quasi-isomorphism-invariance input. It is fully proved in its new module. Its statement allows unbounded complexes and arbitrary quasi-isomorphisms and is checked by the flat-separator argument, including zero source or target. The item node's proof, proof dependencies and origin now describe the actual categorical assembly. The inherited unit and chapter routes are unchanged. No definition or statement was repaired, so no change record is needed.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
