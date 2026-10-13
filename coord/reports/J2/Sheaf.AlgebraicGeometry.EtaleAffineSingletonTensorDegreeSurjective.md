## What changed

Completed the earlier sandbox's decomposition of
`AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_surjective` without
changing its signature. Its proof defines evaluation at the unique outer Cech
index followed by `ULift.down`, proves this evaluation injective with
`productUniqueIso`, and shows the evaluated comparison range is the whole section
group using additive subgroup closure. Range membership then provides a preimage,
and evaluation injectivity proves the required equality.

Two new modules isolate strictly smaller steps: affine generation of the target
section group, and membership of each normalized pure section in the evaluated
range. Both are ordinary propositions, with no new definitions or chosen data.
Their statements have been checked at degree zero, on empty affine schemes, and
for zero coefficient modules. Generation is independent of the comparison map;
range membership does not assert generation or require affineness.

The entire three-module sandbox compiles through `lcompile.py`. The target node's
proof and dependencies now describe this subgroup-generation argument. Existing
statement signatures and public imports are unchanged.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_surjective`
(node `new-etale-affine-singleton-tensor-degree-surjective`).

Added two holes, each exactly `:= by sorry` in a separate module:

- `AlgebraicGeometry.Scheme.singletonTensorSections_span`, node
  `new-etale-affine-singleton-tensor-sections-span`, module
  `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorSectionsSpan`.
- `AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_normalized_range`,
  node `new-etale-singleton-tensor-normalized-range`, module
  `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRange`.

This is a decomposition, not a net reduction in holes. No sorry remains in the
item's proof, and there is no sorry inside any definition.

## No longer needed

No existing imports were removed: the original module imported only the
normalization interface. Both new proof imports are used.

The item no longer directly depends on
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-quasi-coherent`,
`lem-pc-module-pullback-adjunction`,
`lem-weil-pbc-module-pullback-affine-sections`, or
`lem-sc-etale-qcoherent-presheaf-functorial`: the geometric generation node retains
these dependencies. They are not claimed to be globally pruned. The normalization
interface remains a statement dependency.

The unused experimental module
`Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorSectionsEquiv` was never part of
the repository or the delivery; neither its equivalence nor tensor induction is
needed by the final assembly. No blueprint unit statement or realized proof step
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox had a compiling reduction but no report. Its helper files
were new modules, not upstream declarations; both holes are explicitly accounted
for above. The original target docstring describes an equivalence-based argument;
the delivered DAG records the actual additive-generation assembly.

Direct proofs of normalized range membership were attempted using the pure tensor
as witness and the supplied normalization equation. Elaborating or kernel-checking
these terms expanded the section/tensor implementation beyond the single-file
compiler limit. No compiler limit was raised and no shared interface was changed.
The remaining helper's docstring specifies this elementary witness proof for its
next worker. Its hole is not counted as a completed proof.

## New nodes

`new-etale-affine-singleton-tensor-sections-span` states that the products of the
projection functions acting on normalized coefficient restrictions generate the
sections on the affine iterated product. Its source and proof identify the affine
ring tensor calculation, the pullback section formula, and the composition-unit
normalization. Its conclusion is independent of any comparison homomorphism.

`new-etale-singleton-tensor-normalized-range` states only generator range membership
for a normalized homomorphism. Its source and proof supply the explicit lifted
pure tensor witness. It assumes no affine opens and contains no surjectivity or
spanning assertion. No change record is needed because no existing interface was
changed.

## Second reading by J2

1. I compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; only its proof and proof-only imports were added. The two helper modules are new declarations with nodes matching their signatures.

2. I compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds with no errors. The target has no remaining `sorry`; the two helper declarations intentionally remain exactly `:= by sorry` and are listed above. No forbidden declarations or hollow definitions were introduced.

3. The split-off statements are strictly smaller than the target: one is affine section generation and the other is pure-generator range membership. Their docstrings give the intended constructions, their DAG nodes and sources match, and they are not duplicate library declarations. The edge cases n = 0, empty affine schemes, and zero coefficients are covered by the stated formulations.

4. The proof follows the shortest available assembly from the supplied normalization interface: injective singleton evaluation, closure of the normalized generators, and range membership. The imports of both helper modules are used; no stale experimental module is delivered. The unit route is preserved through the generation and normalized-range steps recorded in `dag/units/sk-prop-h2.json`.

5. The DAG proof and dependency records agree with the Lean proof: the target depends on both helper nodes, while each helper depends only on the normalization node and has status `split`. No existing statement or definition was changed.

I changed only this report section after the first dry run; no Lean source or DAG content was altered during second reading.
