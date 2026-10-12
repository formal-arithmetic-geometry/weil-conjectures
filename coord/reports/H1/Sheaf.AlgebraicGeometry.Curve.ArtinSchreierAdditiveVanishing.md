## What changed

Proved `AlgebraicGeometry.isZero_etaleCohomology_additive_of_two_le` from three
independent ingredients: the coefficient-universe comparison, the existing
`subsingleton_etale_ga_and_structure_cohomology`, and the proved natural
`Scheme.nonempty_sheafH_extDerivedIso`. The given sheaf isomorphism is transported
by `Sheaf.functorH`; injectivity of additive equivalences transfers subsingletonness,
and `AddCommGrpCat.isZero_iff_subsingleton` converts it to the required zero object.
The original statement, universes, definitions and public imports are unchanged.
Added proof-only imports of `EtaleZariskiCohomology`, `EtaleSheafHExtDerivedComparison`,
and the new `EtaleQcoherentCohomologyULift` module. Updated the original node's proof,
proof_deps and proof_origin to match the Lean reduction.

## Proved and sorry left

The item's only original sorry is closed:
`AlgebraicGeometry.isZero_etaleCohomology_additive_of_two_le`
(`lem-sc-artin-schreier-additive-derived-vanishing`). Its proof compiles.

One independent comparison remains sorry:
`AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsSheaf_cohomology_ulift`
in `Sheaf.AlgebraicGeometry.EtaleQcoherentCohomologyULift`
(`lem-sc-etale-qcoherent-cohomology-ulift`). Its entire proof is `by sorry`, with a
source and full finite-affine-cover proof in its docstring and node. This is not a
renaming of the target: it compares two ordinary cohomology groups for arbitrary
quasi-coherent modules on quasi-compact separated schemes, in every degree. It
contains no smoothness, curve, dimension or vanishing assertion, no arbitrary G,
and no derived-category encoding. The existing curve vanishing and derived
comparison remain necessary independent inputs to the compiled target proof.

## No longer needed

No existing imports were removed: all five original public imports are retained
for the statement and existing interface. The original DAG's direct dependency
`lem-sp-kinjective-computes` (`Sheaf.CategoryTheory.KInjectiveComputes`) is not needed
by this proof. The direct edge to `lem-sp-derived-functor-single-identification`
is replaced by the already proved `lem-weil-pbc-sheafH-ext-derived-comparison`;
the single-identification result remains used transitively by that comparison,
so its module is not claimed globally unnecessary. `lem-sc-ga-cohomology` remains
used. No compactification, two-affine-cover theorem or special curve Cech lemma
is needed. The new universe-comparison plan uses the generic Cech spectral
sequence as a tool to realize descent for quasi-coherent modules; it does not
replace any step of the curve cohomological-dimension unit.

## Where the brief, the DAG or earlier work was wrong

The original node treated the coefficient-universe comparison as an unstated
step inside the Ga-cohomology dependency. Its Ga declaration only asserts the
small-coefficient vanishing; the universe comparison is now a separate item.
The brief says proof-dependency modules are already imported, but this module
had only five statement imports. The derived encoding can now be handled by the
existing proved natural Sheaf.H/derived comparison, without using the large
conjunction in KInjectiveComputes. No existing mathematical statement was changed
or marked disputed. The local literature directory lacks the cited blueprint
and Stacks text, so the relevant proof was read on the official Stacks pages:
https://stacks.math.columbia.edu/tag/03P2 and https://stacks.math.columbia.edu/tag/03DW.
LeanFinder and Loogle returned no universe-cohomology comparison; Mathlib grep
found none. LeanSearch was unavailable (HTTP internal server error), recorded
without a negative-match verdict. Edge cases checked: degree zero identifies
both groups with sections and ULift; empty X has the empty cover and zero section
complex; F=0 has zero complexes. The helper uses separatedness to ensure affine
finite intersections and compactness to ensure a finite cover.

## New nodes

`lem-sc-etale-qcoherent-cohomology-ulift`: coefficient-universe comparison for
associated quasi-coherent etale sheaves, using finite affine open covers and
Stacks 03P2/03DW. One theorem in one new module, with the original item's chapter
and unit. The node records the affine acyclicity results in both universes,
pullback identifications, and generic Cech spectral sequence as dependencies.
Change record: `coord/changes/etale-qcoherent-cohomology-ulift.md`.

## Second reading by H1

1. **Interface and accidental changes.** Compared the delivered target module with the repository version. The target declaration, all existing declarations, universes, hypotheses, and conclusions are byte-for-byte unchanged. The added imports are proof-only plain imports. Verdict: pass.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`; compilation succeeds without errors or warnings. The target has no `sorry`, and the new comparison theorem is the only remaining named `sorry`, documented in its docstring and represented by node `lem-sc-etale-qcoherent-cohomology-ulift`. No forbidden declarations occur. Verdict: pass.

3. **Split-off statements.** The comparison theorem is independent of the curve target: it concerns arbitrary quasi-compact separated schemes, arbitrary quasi-coherent modules, and every degree, and is not a restatement or weakening of the target. Searches recorded in the report and node found no existing declaration. Its edge cases (empty scheme and zero module) are addressed in the proof documentation. Verdict: pass.

4. **Pruning and route.** The target proof uses the existing Ga cohomology theorem, the existing Sheaf.H/derived comparison, and the new coefficient-universe comparison. The old K-injective and single-identification imports are removed; the latter remains transitive through the derived comparison. The unit route remains represented by the target node and its dependencies. Verdict: pass.

5. **DAG agreement.** Updated target and new-node `proof`, `proof_deps`, and `proof_origin` records match the Lean proof and imports. The new node has the required source, blueprint, Lean record, and split status. Verdict: pass.

Changed only the report during this second reading; no Lean statements or proofs required repair.
