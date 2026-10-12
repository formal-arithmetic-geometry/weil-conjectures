## What changed

The original theorem now constructs the finite scheme coproduct W explicitly. It proves the
map W → U etale and surjective, W affine, and its section-ring map faithfully flat using
Mathlib. It composes two new complex comparisons. No statement or definition changed.
Both intermediate signatures and the full assembly compile through lcompile.py.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.exists_etaleTensorSectionsSheaf_ulift_cech_amitsur_iso`
(node `new-etale-affine-tensor-cech-amitsur-comparison`). No sorry remains in the item.
Added two holes: `AlgebraicGeometry.Scheme.nonempty_etale_over_coproduct_cech_iso`
(node `new-etale-over-coproduct-cech-comparison`) and
`AlgebraicGeometry.Scheme.nonempty_etale_affine_singleton_tensor_amitsur_iso`
(node `new-etale-affine-singleton-tensor-amitsur`). This is a decomposition: one original
hole closed, two proper intermediate holes added, net -1. The coproduct comparison is
independent of coefficients, affineness and covering; the singleton comparison is
independent of a family, faithful flatness and existence of a ring witness. Neither
repackages the original conclusion. Data B and a are constructed from W before invoking
any new existence theorem, and neither comparison chooses object data used in a definition.

## No longer needed

Removed proof imports from the item:
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
- `Sheaf.Paper.EtaleStandardCoverCech`
- `Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent`
- `Sheaf.AlgebraicGeometry.TensorPullback`

The first, third, fourth and sixth remain mathematical ingredients for the new lower
comparison nodes. Descent remains through the public tensor-section-sheaf definition.
The direct standard-cover node `lem-sc-etale-standard-cover-cech` and its module
`Sheaf.Paper.EtaleStandardCoverCech` are bypassed: the item proves its affine, etale,
surjective and faithfully-flat conclusions directly; the coproduct comparison isolates
only its sheaf-comparison argument. This is pruning of the item's direct route, not a
claim that another target no longer imports these modules. The old direct proof dependencies removed are:
- `lem-weil-pbc-module-pullback-quasi-coherent`
- `lem-pc-module-pullback-identity-composition`
- `lem-sc-etale-qcoherent-descent`
- `lem-sc-etale-standard-cover-cech`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-module-pullback-affine-sections`
- `lem-weil-pbc-etale-site-cech-complex-comparison`

These are removals from the upper node's direct proof dependencies. Except for the
standard-cover theorem, they remain ingredients of lower comparisons or the public
sheaf definition. No global import-closure pruning figure is asserted.
No unit realization is bypassed:
`sk-prop-h2.realized` has no statement or step assigned to these tool nodes.

## Where the brief, the DAG or earlier work was wrong

The available standard-cover theorem accepts I : Type u, a base literally equal to Spec A,
and a cover over the terminal etale object. The item accepts I : Type (u+1) and a family
over U in X_et. It cannot be applied directly; transferring its selected coproduct and
complex across the affine chart, index reindexing and localized-site equivalence requires
additional comparisons. The new coproduct lemma states that proper comparison step with
no affine-chart or covering hypotheses. The affine singleton tensor comparison is the
missing chain-level identification; degreewise affine sections alone do not prove it.
Search found no existing full comparison. LeanSearch was unavailable; LeanFinder, Loogle,
Mathlib rg and library rg were checked. Tags 03OZ and 03P2 were read online because the
local literature checkout is absent. Empty family, empty W, and identity-map edge cases
were checked mathematically and explained in the intermediate docstrings.

## New nodes

`new-etale-over-coproduct-cech-comparison` has its own module, source, full proof in words
and signature. It isolates coproduct distribution and the sheaf restriction isomorphism,
including the large finite index and nonterminal slice. It uses existing fibre-product,
disjoint-section and chosen-product comparison nodes.

`new-etale-affine-singleton-tensor-amitsur` has its own module, source, full proof in words
and signature. It isolates the affine singleton calculation, without flatness or
surjectivity, from affine fibre products, affine pullback sections and normalized
pullback composition. The original node's proof and proof_deps match the actual assembly.
No change records are needed.


## Second reading by E2

1. Compared the delivered upper module with the repository using diff. Its existing
   theorem signature is byte for byte unchanged; only proof imports, the docstring and
   proof changed. The two additional modules and their statements are new. No definition
   or target statement changed, and no change record is required. Verdict: pass.
2. Compiled all three modules in import order through lcompile.py without errors or
   unexpected warnings. Printed the axioms of all three theorems from a scratch copy:
   only propext, Classical.choice, Quot.sound and sorryAx occur. The only new direct
   holes are the two reported public named comparison theorems, each with a complete
   proof docstring and node. No forbidden declaration or data hole occurs. The witness
   ring and map are explicit section-ring constructions. Verdict: pass as decomposition.
3. Read both intermediate signatures, their docstrings, their nodes, the existing
   standard-cover, disjoint-restriction, affine-sections and site-comparison statements,
   and Stacks Tags 03OZ and 03P2. Checked degree zero, empty family, empty W, identity
   map, and repeated summands: the family complex includes tuples with repetitions,
   and the coproduct decomposition includes exactly those tuples. No covering is needed
   for the first comparison; no faithful flatness is needed for the second. Both are
   strictly separate parts of the original argument. Independent LeanFinder search
   for disjoint-union restriction cochains, Loogle search for Cech isomorphisms and rg
   on the library and Mathlib found no existing full comparison. The terminal-base
   restriction theorem needs the slice-site transport and index reindexing explained
   below; it cannot directly close this hole. Neither hole can be closed in a few
   minutes by an existing declaration. Verdict: pass.
4. The upper proof uses Mathlib directly for the coproduct, affine, etale, surjective
   and faithfully-flat facts, then composes the two complex comparisons. Its public
   imports are needed by the unchanged signature; the new comparisons are plain
   proof imports. The six old direct proof imports are removed. Expanded the pruning
   section with all seven old proof-dependency node ids no longer directly used.
   sk-prop-h2.realized has empty statement and step realizations, so no required unit
   realization is bypassed. Verdict: pass; no global pruning claim.
5. Checked the Lean signatures against all three lean.statement records and checked
   each node's proof_deps equals the union of its proof steps' uses. The upper node
   matches the explicit construction and composition; new nodes have source, searches,
   created, blueprint, chapter, unit and Lean records. Verdict: pass.

Second reading changed the lower proof docstrings and node proof steps to spell out
slice-site/universe transport and transport of quasi-coherence from abstract pullback
to tensorPullback; corrected the upper proof_origin attribution; completed the removed
node list and clarified its direct-dependency scope. No executable Lean proof or
signature changed. One original hole is closed and two lower holes are added; this
is a decomposition, not an axiom-free completion or positive net progress.
