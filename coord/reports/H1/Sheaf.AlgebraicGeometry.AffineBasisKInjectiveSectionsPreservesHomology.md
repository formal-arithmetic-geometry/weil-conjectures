## What changed

Replaced the sorry in `AlgebraicGeometry.affineBasisKInjectiveSections_preservesLeftHomology`
with a complete Lean reduction. Its signature and all three public imports are unchanged.
Added proof-only imports of `DerivedLowerTruncationCycleFormula`,
`LeftExactUpperTruncationComparison`, `AffineBasisDerivedSectionsLowerTailVanishing`
and the source right-derived triangulated functor module.

The new private, proved helper `preservesLeftHomology_of_lowerComparison` uses the
canonical cycle formula, K-injectivity of the derived unit, the mapped cycle-kernel
homology data and cokernel transport. It proves preservation of the actual homology
quotient, not existence of an unrelated homology isomorphism. The main proof applies
derived sections to the standard truncation triangle and uses two lower-tail vanishings
to provide the helper's truncation isomorphism.

The remaining unbounded geometric calculation is isolated in the new module
`Sheaf.AlgebraicGeometry.AffineBasisDerivedSectionsLowerTailVanishing`. This concerns
only derived sections of a strictly lower tail and has no K-injectivity assumption,
raw section homology or cycle-class quotient in its conclusion. It is the convergence
part of the original plan; the truncation triangle and canonical quotient argument
combining it with the existing lemmas are implemented here. Updated the original
node's proof, proof_deps and proof_origin to match this route.

Both modules compiled together through lcompile.py. The new statement was checked
against empty V, zero F, arbitrary negative cutoffs, the equality i=a, and a single
acyclic sheaf concentrated just below a. Its acyclicity hypothesis is on the actual
homology sheaves; no quasi-coherence or acyclicity of terms/cokernels was assumed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.affineBasisKInjectiveSections_preservesLeftHomology`
(node `lem-sc-affine-basis-kinjective-sections-preserves-homology`): no sorry remains
in the item's module. The private helper is fully proved.

Added one hole in
`AlgebraicGeometry.affineBasisDerivedSections_lowerTail_isZero`
(node `lem-sc-affine-basis-derived-sections-lower-tail-vanishing`), in its own new
module, with its complete source-based proof plan in the docstring and DAG.
Its proof is exactly `by sorry`. This delivery is a decomposition: one original
hole closed, one strictly smaller convergence statement added, net zero holes.
The existing cycle-formula and mapped cycle-kernel data modules are reused.

## No longer needed

No original import was removed. No entire planned dependency is claimed pruned.
The original four dependencies are
`lem-sc-derived-k-injective-restrict-open`,
`lem-pc-derived-limit-eventually-iso`,
`lem-pc-derived-limit-milnor-sequence`, and
`lem-sc-module-cohomology-source-comparison`. They
are no longer direct dependencies of the main proof, but remain dependencies of
the new lower-tail vanishing lemma. They therefore must not be counted as globally
pruned. Upper-truncation comparison itself is not invoked: only the already-defined
`Functor.mappedCyclesHomologyData` from that module is needed.

The quasi-coherent affine-derived-sections lemmas and the acyclic-cokernel section
homology theorem were inspected and are not imported: their extra hypotheses are
not present here. No unit realization is bypassed; the unit's realized statement
and steps are empty, and the finite-duality route above this node is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies alone do not expose a theorem providing the
basis-acyclic unbounded lower-tail vanishing. The Milnor and eventual-isomorphism
lemmas require an actual reconstruction triangle and stabilized cohomology systems;
they cannot be directly applied to the original homology-preservation goal.
The new node supplies precisely that unresolved geometric part, while the generic
canonical comparison and cokernel argument are proved here.

The existing quasi-coherent unbounded cohomological bound cannot be used directly:
no quasi-coherence is assumed. Nor does K-injectivity imply acyclicity of all
terms or differential cokernels; arbitrary contractible summands illustrate why
those hypotheses cannot be silently supplied.

Read the Stacks source cohomology.tex, labels lemma-K-injective (071B),
lemma-is-limit-dimension (0D64) and lemma-alternating-cech-complex-complex-ss (08C2),
from a source snapshot under scratchpad/. The neighboring lemma
cohomology-over-U-trivial (Tag 0BKT) directly gives the stronger derived-section
calculation; the new vanishing statement is its specialization to the strictly
lower tail, whose homology is zero in the requested degrees. The DAG has an
etale counterpart `lem-kun-0bkz`, but no Zariski/module declaration to apply here.
The 08C2 theorem itself has three
acyclicity conditions; its tower argument is adapted using the bounded-below
hypercohomology spectral sequence, rather than applying its theorem without its
term and cokernel hypotheses. The new node also cites the existing generic
truncation hypercohomology and derived-limit transport nodes as tools.

## New nodes

`lem-sc-affine-basis-derived-sections-lower-tail-vanishing`, module
`Sheaf.AlgebraicGeometry.AffineBasisDerivedSectionsLowerTailVanishing`, states
vanishing of H^i of derived evaluation on the strictly lower tail at a for i>=a,
under the parent's basis-acyclic homology hypothesis, without K-injectivity.
The node records the local-bound reconstruction, bounded-below spectral row
calculation and Milnor argument. LeanFinder, Loogle and grep searches were run with msearch.py and recorded
truthfully; no Mathlib match was found. LeanSearch was also called, returned an
Internal Server Error, and is recorded as unavailable. Searches of the DAG and all
blueprint nodes found the general quasi-coherent bound and the basis reconstruction
theorem, but no existing declaration with this conclusion under these hypotheses.
No statement or definition was changed, no forced adaptations, no change record.

## Second reading by H1

1. Interface: PASS. Compared both delivered modules against the read-only repository.
   The existing theorem's entire signature is byte for byte unchanged. The only
   existing-node fields changed are proof, proof_deps and proof_origin. There are
   no modified definitions, target statements, visibility changes or adaptations.
   The lower-tail module is new and declares one theorem, with no new data definition.
2. Proof: PASS as a decomposition. Both files compile together through lcompile.py
   (18.2 and 7.5 seconds). Read the cycle lift, homology-factor isomorphisms, derived
   unit, canonical truncation projection, and cokernel universal-property transport.
   The proof preserves the specified quotient, not merely its object's isomorphism
   class. A scratch copy with #print axioms shows the private helper uses only
   propext, Classical.choice and Quot.sound. The main theorem and the new lower-tail
   theorem use those axioms plus sorryAx, as expected from the single added hole.
   No forbidden declaration or sorry inside a definition is present. The choice
   of the cycle-formula isomorphism is existential elimination inside a proof;
   it does not define data from an arbitrary unproved existence statement.
3. Split statement: PASS. Independently read Stacks Tag 0BKT, both in the local
   cohomology.tex snapshot and at https://stacks.math.columbia.edu/tag/0BKT.
   Applied on V to tau_<a QF, its hypothesis follows because lower-tail homology
   agrees with F below a and is zero at and above a; affine subopens form a basis
   and include V. Its conclusion gives zero derived sections homology for i>=a.
   Checked i=a (H^(a-1) can be nonzero but stabilizes in the Milnor term), arbitrary
   negative cutoffs, empty V, zero F, and a single basis-acyclic sheaf in degree a-1.
   The docstring and matching node give the reconstruction, bounded-below spectral
   sequence, stabilized first derived limit, and module/abelian comparison argument.
   The statement isolates support vanishing without K-injectivity or a homology
   quotient comparison, so it is a strict part of the argument, not a renamed item.
   Independent msearch.py searches used LeanFinder's hypercohomology/support query,
   Loogle's rightDerivedFunctor/IsLE query, and grep's homology/rightDerived query;
   only support criteria and ordinary derived-functor interfaces were found.
   Searched the local library for basis-acyclic and cohomological-bound calculations,
   and read the existing acyclic-sections, truncation-reconstruction, derived-limit
   transport and hypercohomology modules. The acyclic-sections theorem requires
   cokernel acyclicity; quasi-coherent bounds require quasi-coherence. Neither is
   available here. Closing the remaining convergence calculation needs substantial
   formalization, not a few-minute application of an existing theorem.
4. Route and pruning: PASS. Each direct import supports a signature, the cycle
   formula, mappedCyclesHomologyData, lower-tail vanishing, or triangulated derived
   sections. The upper-truncation theorem is not invoked; its module supplies the
   actually constructed mapped cycle-kernel homology data. Added proof imports
   are plain imports. All four old proof dependencies are accounted for below;
   none is globally pruned. Read sk-thm-picard-duality.json: realized.statement
   and its realized step are empty. This local reduction keeps the finite-duality
   route and changes no unit record.
5. DAG: PASS. Checked all new-node fields, its exact Lean signature, source,
   creation record, chapter/unit and blueprint ancestry. Each proof_deps list is
   precisely the union of the proof steps' uses. The main node describes the
   actual triangle, canonical comparison and cokernel transport. The remaining
   node describes only the unresolved lower-tail calculation. No unsupported
   signature edit or change record is hidden in the delivery.

Second reading changed only this report: added the independent review and made
explicit the old direct dependencies transferred to the lower-tail node. No Lean
repair was needed. One original hole is closed and one hole is added: net zero,
with no module claimed globally pruned.
