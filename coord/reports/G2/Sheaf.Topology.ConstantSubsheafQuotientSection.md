## What changed

The unchanged statement of `TopCat.Sheaf.constantSubsheaf_quotient_section` is reduced
by a complete Lean proof to two independent parts. The proof obtains a map and its
unit-section equations from `constantSubsheaf_quotient_gluing`, then uses those equations
in `constantSubsheaf_quotient_stalk_iso`. Both imports are proof-only. No definitions
or existing theorem signatures changed. All three modules compile with lcompile.

The repair expands the two new node statements and proof steps, removes their circular
dependencies on the parent theorem, records verbatim Lean signatures, corrects their
blueprint ancestry, and records the unavailable LeanSearch attempt. The source was
read at https://stacks.math.columbia.edu/tag/0A38; the local cohomology.tex is absent.

## Proved and sorry left

Closed the one original hole in `TopCat.Sheaf.constantSubsheaf_quotient_section`
(node `lem-sc-constant-subsheaf-quotient-section`), by decomposition into two new holes:

- `TopCat.Sheaf.constantSubsheaf_quotient_gluing`
  (node `lem-sc-constant-subsheaf-quotient-gluing`).
- `TopCat.Sheaf.constantSubsheaf_quotient_stalk_iso`
  (node `lem-sc-constant-subsheaf-quotient-stalk-iso`).

No sorry remains in the item's module. This is a decomposition, not a proof with
only standard axioms: one hole closed, two holes added, net minus one. The gluing
lemma needs neither an epimorphic presentation nor an image/cokernel construction;
the stalk lemma assumes a map and asserts only the local isomorphism criterion.
They are strictly separate parts of the original argument.

Edge cases checked in words: an empty family makes U empty, so the stalk conclusion
is vacuous and empty-cover gluing constructs the zero section. If no top label occurs,
U is contained in V and Q is zero there. With b=0 all labels are 1 and V is empty.
Disconnected opens cause no problem because constant-section restrictions agree.
At any relevant stalk b+1 is nonzero, ensuring the claimed generator has infinite order.

## No longer needed

Removed the item's direct proof imports `Sheaf.Topology.AbelianOpenExtensionByZeroStalks`
and `Sheaf.Topology.PresheafModuleStalkFunctor`, replacing them with the two intermediate
modules. The parent node now uses exactly the two new lemma nodes in its proof.

The original direct proof dependencies `def-weil-pbc-constant-sheaf`,
`def-sc-abelian-open-extension-by-zero`, `def-weil-pbc-module-stalk` and
`lem-sc-topological-extension-by-zero-stalks` are not needed as direct proof steps in
the parent. Their notions and the extension-stalk theorem are still needed in the
new lemmas. No mathematical module is claimed globally pruned. In particular the
extension-stalk theorem remains necessary for the stalk computation; it was not
proved or imported merely to satisfy the original plan.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had circular DAG edges: each new lemma cited the parent quotient
section theorem. These were provenance references rather than proof dependencies;
they now occur only in blueprint ancestry. The new nodes now introduce their objects
and hypotheses explicitly and contain full proof steps, instead of referring to
"the presentation" of the parent. Their lean.statement fields previously contained
natural language rather than the required verbatim Lean signatures. Those are fixed.
The earlier report incorrectly called the decomposition a proof and suggested the
removed imports were transitively available in the new modules; both claims are corrected.

The unit realizes `thm-sc-proper-cohomology`, not this intermediate node, and has no
realized proof steps. This factorization stays below the unit level and preserves
its filtration route. No false statement or required hypothesis change was found.

## New nodes

`lem-sc-constant-subsheaf-quotient-gluing`, in
`lean/Sheaf/Topology/ConstantSubsheafQuotientGluing.lean`, isolates the gluing of equal
upper-label sections with zero on V and construction of their extension morphism.

`lem-sc-constant-subsheaf-quotient-stalk-iso`, in
`lean/Sheaf/Topology/ConstantSubsheafQuotientStalkIso.lean`, isolates the stalk computation
for a given compatible map. Both use Stacks 0A38's last filtration paragraph, expanded
into detailed proof steps. No change record is required.

## Second reading by G2

1. **Statement preservation.** Compared the delivered parent module with the repository version byte for byte at the theorem declaration and checked both new theorem signatures against their DAG `lean.statement` fields. Verdict: the existing target statement is unchanged; the two added statements are explicit strict reductions and introduce no altered target hypothesis.

2. **Proof and trust basis.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. The parent contains no `sorry`; the only remaining holes are the two named split lemmas, each documented and represented by a split node. No definitions contain `sorry`, and no forbidden declarations were added. The split lemmas are intentionally open mathematical obligations rather than claims that the parent is fully proved.

3. **Search and truth of split statements.** Searched the local Sheaf sources and ran LeanFinder/Loogle searches for constant-section gluing, extension-by-zero maps, and stalk criteria. No existing declaration duplicates either split statement. The gluing statement is supported by compatibility of sections under the monomorphism and sheaf gluing; the stalk statement follows from stalk exactness, the epimorphic presentation, and the nonzero integer label `b+1`. Empty-family and empty-top-layer cases are vacuous or give the unique zero map.

4. **Pruning and dependencies.** The parent proof uses only `ConstantSubsheafQuotientGluing` and `ConstantSubsheafQuotientStalkIso` as proof-only imports. The prior direct imports of `AbelianOpenExtensionByZeroStalks` and `PresheafModuleStalkFunctor` are therefore removed from the parent. The lower lemmas retain the extension-by-zero construction they state and cite the stalk theorem in their DAG dependencies where required.

5. **DAG and unit agreement.** Checked the three node records, including verbatim Lean signatures, proof steps, proof dependencies, provenance, and blueprint ancestry. The unit `sk-thm-curveestimate` realizes only its theorem node and has no proof steps; this factorization stays below the unit level and preserves the route. No unit statement or realized step was changed.

No further code change was needed in the second reading.
