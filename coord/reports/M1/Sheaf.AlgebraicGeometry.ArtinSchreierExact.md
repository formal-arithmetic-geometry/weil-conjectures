## What changed

Proved `AlgebraicGeometry.artinSchreier_data_shortExact` by applying a new companion theorem supplying exactness, monomorphism, and epimorphism, then `ShortExact.mk'`. Added `Sheaf.AlgebraicGeometry.ArtinSchreierExactComponents` with the intermediate theorem (left as a named sorry). Updated the target node proof dependencies.

## Proved and sorry left

`artinSchreier_data_shortExact` is proved. `artinSchreier_data_exact_components` remains sorry, node `lem-sc-as-sequence-exact-components`.

## No longer needed

None; the existing data import is required by the theorem signature and the companion theorem.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof had no usable Lean-level decomposition of exactness. The argument requires the three component conjunction as an intermediate statement.

## Earlier second reading (a previous round; superseded)

Pending second reading of the intermediate node and proof route.

## New nodes

`lem-sc-as-sequence-exact-components`, implemented by `Sheaf.AlgebraicGeometry.ArtinSchreierExactComponents.artinSchreier_data_exact_components`.

## Second reading by M1

1. **Statements unchanged.** Compared both delivered modules with the repository. The
signature of `artinSchreier_data_shortExact` is byte-for-byte unchanged; the new
companion declaration is recorded by its node.
2. **Proof and axioms.** Compiled all three sandbox modules with `lcompile.py --all`.
The target theorem has no `sorry`; the only remaining `sorry` is the named
`artinSchreier_data_exact_components`. No forbidden declaration or hollow definition
was introduced. The target proof uses only `ShortExact.mk'` and the companion result.
3. **Split statement.** The companion theorem is a component-level reduction: it
returns exactness, monomorphism, and epimorphism separately, exactly the fields
consumed by `ShortExact.mk'`. Its node and docstring give the sectionwise kernel and
surjectivity argument and identify the source.
4. **Pruning and imports.** The proof requires `ArtinSchreierData`,
`ArtinSchreierExactComponents`, and `ShortExact`; no old import or proof dependency
can be removed. The unit route remains the Artin--Schreier exactness component route.
5. **DAG agreement.** Updated node proof dependencies and proof text match the Lean
proof; the companion node records its declaration, source, and split status.

Changed the companion docstring to include the complete natural-language proof
obligation and added this second-reading review. No target statement or definition
was changed.
