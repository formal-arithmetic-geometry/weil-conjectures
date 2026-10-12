## What changed

Proved `AlgebraicGeometry.GrpObj.infPointsMap_infBracket` by applying injectivity of
toMixed and simplifying the commutator through a homomorphism. Added one private helper,
`toMixed_infBracket`, which follows directly from `mixedEquiv.apply_symm_apply`. All public
imports, definitions, and signatures remain unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.GrpObj.infPointsMap_infBracket`. The existing `sorry`s remain in
`toMixed_bijective`, `commutator_mem_mixedPoints`, the instance `LieRing (Lie G)`,
the instance `LieAlgebra Γ(S, ⊤) (Lie G)`, and `infBracket_mem_range_infPointsMap`. No new `sorry` was added.

The remaining declarations are `instance instance : LieRing (Lie G)` and `instance instance : LieAlgebra Γ(S, ⊤) (Lie G)`.

## No longer needed

No imports or DAG nodes were pruned. The proof uses the existing `toMixed_bijective` and
`infBracket` declarations and adds no public dependency.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox proof was valid but exceeded the 60-second local compile limit under
current load. This smaller proof compiles within the limit and preserves the target statement.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

The reduced proof was independently checked by local compilation. It preserves the target
statement and adds no public declarations or new holes; the remaining instance holes are
inherited from the baseline module.

## Second reading by K2

1. **Comparison with the repository.** The delivered module was diffed against the repository
version. Existing declaration signatures, definitions, and visibility are unchanged; the only
additions are a private helper and the proof of `infPointsMap_infBracket`.

2. **Compilation and proof checks.** The module compiles with `lcompile.py` in 18 seconds. No
new `sorry`, axiom, unsafe, opaque, extern, or implemented-by declaration was introduced. The
remaining holes are inherited named declarations listed above; the proved theorem relies only on
the existing `toMixed_bijective` and `commutator_mem_mixedPoints` interfaces.

3. **Statement and split review.** `infPointsMap_infBracket` has its original statement and is
proved by injectivity of `toMixed`, functoriality of the group homomorphism, and `map_mul`/`map_inv`.
The private helper is an immediate `Equiv.apply_symm_apply` identity and introduces no public
statement or split-off node. No new statement is needed.

4. **Shortest route and pruning.** The proof uses the direct mixed-point equivalence route and
does not bypass any realized unit step. All imports remain used by declarations in the module,
and no DAG node or module can be pruned.

5. **DAG and unit agreement.** The theorem declaration and its unchanged signature agree with the
existing DAG references, and the unit `sk-i-restriction` route remains represented by the module.

I changed only the theorem proof and added the private helper; no public interface or dependency
was changed.
