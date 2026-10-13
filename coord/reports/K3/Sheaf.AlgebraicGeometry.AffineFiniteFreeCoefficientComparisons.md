## What changed

Replaced the sorry in `AlgebraicGeometry.affine_finite_free_coefficient_comparisons`
by a complete proof from a natural forward comparison and a finite-basis inverse.
The original signature and visibility are unchanged. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.AffineHomComparisonMaps` and
`Sheaf.AlgebraicGeometry.AffineHomComparisonFiniteFree`.

The latter module is fully proved: for any additive T, source naturality and
invertibility on the rank-one module imply invertibility on every finite free
source. Its inverse is an explicit finite sum of coordinate maps. The main module
uses this result degreewise and proves the inverse naturality squares by cancellation.
No public definition chooses data from an existence theorem. The comparison witness
is used only inside an existential theorem proof; its inverse is uniquely determined.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.affine_finite_free_coefficient_comparisons`
(node `lem-sc-affine-finite-free-coefficient-comparisons`). No sorry remains in that module.

Fully proved the new theorem
`AlgebraicGeometry.affine_hom_comparison_isIso_of_finite_free`
(node `lem-sc-k3-affine-hom-comparison-finite-free`). It has no sorry dependencies.

Added exactly one remaining hole:
`AlgebraicGeometry.exists_affine_hom_comparison_maps`
(node `lem-sc-k3-affine-hom-comparison-maps`). This asserts natural forward maps
for arbitrary modules and invertibility only in rank one; it does not assert
finite-free invertibility, choose complex comparisons, or assert naturality of
arbitrary isomorphisms. Its docstring and node give the fraction construction,
restriction compatibility, naturality, and rank-one evaluation proof.

This is a decomposition: one original hole closed, one strictly lower hole added;
net zero holes. The finite-basis invertibility step and the inverse-square assembly
are actual proved Lean and no longer require future proof work. All three modules
compile with lcompile.py without warnings. Empty bases, zero coefficients, zero
rings and unbounded complexes require no excluded cases.

## No longer needed

No imports removed from the original module, and no existing dependency modules
claimed pruned. The two original proof dependencies
`lem-weil-pbc-spec-module-tilde-sections` and `def-pur-sheaf-hom`
are still used by the new forward-map node, so neither is pruned from the closure.
The original node now directly depends on the two new nodes instead.
No finite-free structure-sheaf-only dual comparison, Koszul coordinate comparison,
or derived-category lemma is needed by this proof. No such module was imported.

## Where the brief, the DAG or earlier work was wrong

The discarded earlier attempt stated naturality for an arbitrary isomorphism family;
that is false. The current reduction obtains one natural family c and derives both
inverse squares for its inverse. No property is asserted of unrelated isomorphisms.

The original DAG names the tilde-sections and internal-Hom definitions, but neither
contains the comparison map or its naturality theorem. The new forward-map node
makes this missing part explicit; the finite-free upgrade is proved rather than holed.
The finite-basis route of the original node is preserved. The unit record's realized
fields contain no bound nodes that this reduction would bypass. No chapter or unit
record, existing statement, definition, or other holder's module changed.

Read the cited Stacks Tags 01HV and 0BQZ online because the local Stacks text is not
present in this checkout. LeanSearch returned Internal Server Error; LeanFinder,
Loogle and source searches were also performed and recorded on the new nodes.

## New nodes

`lem-sc-k3-affine-hom-comparison-maps`:
`lean/Sheaf/AlgebraicGeometry/AffineHomComparisonMaps.lean`, one named public sorry.
It isolates construction/naturality of the forward comparison and its rank-one case.

`lem-sc-k3-affine-hom-comparison-finite-free`:
`lean/Sheaf/AlgebraicGeometry/AffineHomComparisonFiniteFree.lean`, fully proved.
It extends rank-one invertibility by an explicit finite-basis sum inverse.

No change record is needed: no existing public signature or definition changes,
and the new imports in the original module are proof-only.

## Second reading by K3

1. **Visible declarations — pass.** I diffed the delivered item against the repository version. The existing theorem signature and visibility are unchanged; the two additional modules are new proof-support modules and introduce no modification to an existing declaration.

2. **Proof checking — pass.** I compiled all three sandbox modules with `lcompile.py --all` and compiled each changed module individually. The item theorem and the finite-free upgrade contain no `sorry`; the only remaining `sorry` is the named public theorem `exists_affine_hom_comparison_maps`, exactly as listed above. No forbidden `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition occurs.

3. **Statements and split — pass.** The finite-free theorem is a strictly lower, general algebraic reduction: additivity, source naturality, and rank-one invertibility imply invertibility for finite free sources by an explicit finite-basis inverse. The affine comparison-map theorem is the remaining geometric construction and asserts only forward maps, naturality, and rank-one invertibility. Neither theorem restates the target, strengthens its hypotheses, or weakens its conclusion. The edge cases of empty bases, zero modules, and zero rings are covered by the finite sums and categorical identities.

4. **Route and pruning — pass.** The target proof follows the stated unit route: construct one natural forward family, apply the finite-basis upgrade degreewise, and obtain the inverse family by cancellation. The two added imports are proof-only and are used. No old proof dependency is bypassed, and no unused import or module was found to prune.

5. **DAG agreement — pass.** The existing node records the new proof dependencies and proof origin, and both new node records match their Lean declarations, statements, proof plans, sources, and module paths. The unit and chapter records are untouched, so the realized route remains intact.

I changed only this report section after the first dry run; no Lean proof, statement, definition, or DAG record required repair.
