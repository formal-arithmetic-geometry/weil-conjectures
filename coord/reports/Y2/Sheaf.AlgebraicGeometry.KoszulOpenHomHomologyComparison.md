## What changed

Replaced the sorry in `AlgebraicGeometry.koszulOpenHom_homology_comparison` with a
compiled proof from two new intermediate statements. The existing signature, universes,
visibility and docstring are unchanged. The proof constructs the affine counit complex
isomorphism using Mathlib, proves K-projectivity of every tail from exterior-power
freeness, and defines alpha by additive equivalence composition. Transition naturality
uses the actual cochain formula of `koszulCechHomDiagram_exists`, homology functoriality
and cancellation of the object isomorphisms. For the zero clause, a chain representative
and its cycle identify alpha(phi); the restriction formula at psi=0 then gives zero by
additivity. There are no data definitions selected from mere unproved existence.

Added `Sheaf.AlgebraicGeometry.AffineKProjectiveHomComplex` and
`Sheaf.AlgebraicGeometry.KoszulChainRestrictionFormula`, with corresponding DAG nodes,
and updated the parent node's proof, proof_deps and proof_origin. Proof imports are
private to the module system. No other existing module is adapted.

The two intermediate statements are strictly separate parts of the argument. The first
is generic in every K-projective source complex and arbitrary module target, with no
Koszul system, open restriction or beta. The second concerns actual module chain maps
and their cycle classes; it does not assert any stage equivalence or transition
naturality for arbitrary derived morphisms. The Lean combination handles the affine
counit, target transport, tail projectivity, diagram transport, and reduction of an
arbitrary derived morphism to a chain representative.

Sources read: [Stacks 06Z0](https://stacks.math.columbia.edu/tag/06Z0),
[08DD](https://stacks.math.columbia.edu/tag/08DD),
[08D1](https://stacks.math.columbia.edu/tag/08D1), and
[08DC](https://stacks.math.columbia.edu/tag/08DC), plus Mathlib's HomComplex,
HomComplexCohomology, KProjective, module projectivity and affine tilde counit APIs.
The local literature checkout lacks perfect.tex, so these source pages were read online;
the upstream perfect.tex was also downloaded into the sandbox scratchpad and its exact
labels checked (lemma-affine-compare-bounded, lemma-alternating-cech-complex-complex,
equation-comparison and proposition-represent-cohomology-class-on-open).

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.koszulOpenHom_homology_comparison`
(node `lem-sc-koszul-open-hom-homology-comparison`). Its complete Lean proof compiles.

Added two holes, each exactly `:= by sorry` in its own module:

- `AlgebraicGeometry.affineKProjective_homComplex`
  (`lem-sc-affine-kprojective-hom-complex`).
- `AlgebraicGeometry.koszulChain_restriction_formula`
  (`lem-sc-koszul-chain-restriction-formula`).

This is a decomposition, not an unconditional proof or a net hole reduction: one upper
hole closed and two lower holes added. No sorry remains in the item's module, and no
sorry is added inside a definition or private helper. The source theories imported by
the intermediates retain their existing holes, unchanged.

The entire sandbox compiled cleanly with lcompile.py in dependency order.
The delivery dry run printed OK, including the axiom probes and static preflight;
only the independent second-reading section remains for the assigned second reader.
No delivery was pushed. Edge cases
were checked mathematically: the generic equivalence also covers the zero source and
zero ring; all Hom complexes and maps are zero there. For r=0 the tail and restriction
source groups vanish and U is empty. For r=1 the restriction formula is division by
f_0^(e+1) on D(f_0). F=0 and phi=0 give the zero cycle. No regularity or target
boundedness enters either intermediate statement.

## No longer needed

Removed these direct imports from the item's module:

- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore` (now a proof dependency of
  the generic intermediate).
- `Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology` (now a proof
  dependency of the chain formula).
- `Mathlib.Algebra.Homology.HomotopyCategory.KProjective` (already provided publicly by
  the generic intermediate; the K-projectivity theorem is still used).

No original mathematical dependency is pruned from the transitive route: affine core,
structure-sheaf hypercohomology and bounded-above projective K-projectivity remain
needed. No whole node or module is claimed pruned. The comparison-square module was
examined but not imported: its equivalences have neither additivity nor transition
naturality nor a prescribed value on chain representatives, so they cannot supply the
required canonical alpha.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies describe the ingredients but do not state the generic
canonical Hom-complex representative equivalence or the fraction/restriction identity
for an actual chain map. The latter is a genuine compatibility calculation, not a
consequence of the structure-sheaf Hom/hypercohomology equivalence alone. Both missing
interfaces are now explicit, with their source arguments in docstrings and nodes.
No existing statement was found false, and no target or definition was changed.
A complete DAG cycle check encountered 28 strongly connected components already in
the baseline, including the cycle through lem-weil-pbc-sheaf-algebraic-structures-objects.
Comparing the baseline and delivery graphs found no new cycle or enlarged component.
Those existing coordination faults are outside this item and were left unchanged.

The blueprint ancestor command returned None because stage-3 created.item fields name
modules rather than node ids. The existing parent record already names
lem-sc-finite-duality as ancestor; the new records inherit that ancestor and its via
chain, adding the parent node and giving the specific generic and chain-formula places.
Whole-blueprint searches for K-projective and Koszul found no duplicate. The unit's
realized route and all chapter/unit records remain untouched.

## New nodes

`lem-sc-affine-kprojective-hom-complex` in
`dag/nodes/sec-picard-framework/lem-sc-affine-kprojective-hom-complex.json` records
`Sheaf.AlgebraicGeometry.AffineKProjectiveHomComplex`. It isolates the affine derived
full-faithfulness and K-projective Hom quotient, with naturality and representatives.
LeanSearch was unavailable; LeanFinder returned generic Ext/resolution results, and
source grep found generic Hom-complex APIs. No exact combined affine statement exists.

`lem-sc-koszul-chain-restriction-formula` in
`dag/nodes/sec-picard-framework/lem-sc-koszul-chain-restriction-formula.json` records
`Sheaf.AlgebraicGeometry.KoszulChainRestrictionFormula`. It isolates the fraction and
sign calculation for a module chain representative, with canonical counit and cycle
hypotheses explicit. It uses the existing restricted-augmentation isomorphism node and
derived structure-sheaf Hom theorem. LeanSearch was unavailable; LeanFinder returned
only generic group-cohomology comparisons, and Mathlib grep had no restriction formula.
All searches are recorded in the sandbox search log. No change record is needed.

## Second reading by Y2

1. **Existing interface: pass.** Diffed the delivered parent module against the repository
   version. The existing theorem signature is byte-for-byte identical, as are its
   docstring, universes, namespace and public visibility. Only proof-local options,
   proof-only imports and the proof body change. Neither new module exists in the
   repository. The parent node changes only proof, proof_deps and proof_origin; there
   is no definition, target statement, existing signature or forced adaptation change.

2. **Proof and trust: pass as a decomposition.** Independently compiled all three
   modules with lcompile.py in import order (4.5, 10.4 and 25.5 seconds). Also compiled
   scratch copies with #print axioms for all three declarations: each reports only
   propext, Classical.choice, Quot.sound and sorryAx. The parent has no local sorry;
   the only two delivered holes are the two named public intermediate theorems listed
   above, each with an exact `by sorry` body. There are no forbidden declarations,
   hollow definitions, anonymous holes or data definitions choosing arbitrary witnesses.
   The existential equivalences and representatives are unpacked only inside the proof.

3. **Split statements: pass.** Read both complete signatures, docstrings and nodes,
   and checked Stacks Tags 06Z0, 08D1, 08DC and 08DD. The generic statement is the
   affine fully faithful tilde comparison composed with the K-projective homotopy
   quotient and the linear Hom-cycle quotient; its naturality uses precomposition,
   not an unspecified equivalence. The chain statement fixes the canonical counit,
   actual chain map, cycle and augmentation equation, isolating the signed fraction
   compatibility calculation. Neither is the parent statement under another name.
   Mathematically tested zero source/target, zero ring, empty cover, and the single
   generator case: for r=1 the augmentation is multiplication by f_0^(e+1), so its
   inverse gives precisely the displayed comparison fraction. When f_0=0 the open
   is empty. No extra regularity or boundedness assumption is needed. Independent
   LeanFinder searches using homotopy-class/linear-Hom and deleted-Koszul/augmentation
   wording found generic HomComplexCohomology and group-cohomology results only.
   Read Mathlib Qh_map_bijective, homAddEquiv and homologyAddEquiv; the latter is for
   additive Hom complexes and does not already state the combined affine module
   result. Searched the project's Koszul, affine and homology modules and the source
   checkout; no duplicate of either complete statement was found. Neither remaining
   hole is a few-minute closure: one needs the module/additive homology transport and
   natural quotient construction, the other the signed restriction calculation.

4. **Route and pruning: pass.** Read the proof from alpha downward. Its counit is an
   actual componentwise construction; exterior-power freeness and Mathlib's bounded
   projective instance give hL. The transition proof uses the specified diagram
   cochain formula, generic naturality and homology composition, and the zero proof
   uses the representative identity, cancellation of q, the chain formula with
   psi=0, and map_zero. All explicit imports supply signature material, proof APIs,
   required instances, or a stated dependency of an open intermediate. The two old
   direct node dependencies absent from the new parent proof_deps are
   new-affine-qcoh-derived-equivalence-core and
   lem-pc-derived-structure-sheaf-hom-hypercohomology: they are retained in the generic
   and chain nodes respectively, not pruned transitively. The third old dependency,
   lem-sc-bounded-above-projective-kprojective, remains directly used through its
   Mathlib match. No whole module is claimed pruned. The unit and chapter files are
   untouched, and this reduction does not bypass a unit step. The baseline unit
   sk-thm-picard-duality has empty realized statement/step arrays already; this review
   confirms preservation, not completion, of that existing coordination record.

5. **DAG agreement: pass.** For each of the three node records, compared the recorded
   Lean statement with the actual signature (exact match), and checked proof_deps
   equals the union of proof-step uses. Reviewed sources, blueprint ancestry, unit,
   chapter, creation metadata and search records of both new nodes. The parent steps
   describe the counit construction, K-projectivity, alpha transport, transition
   conjugation and zero-representative calculation actually present in Lean. The
   new nodes' proofs describe the arguments still to be formalized and do not claim
   those holes are closed.

**Second-reader changes:** appended this independent review and clarified the exact
old dependency disposition and the baseline's incomplete realized fields. No Lean,
node, statement, definition or import repair was necessary. The result remains one
existing hole closed and two strictly separate lower holes added, a decomposition
with net hole change -1, not an unconditional proof of the parent.
