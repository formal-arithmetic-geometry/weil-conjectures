## What changed

Reduced `ModuleCat.exists_baseTensorDerivedComparison` to the natural coefficient
comparison in the derived category before applying any homology degree. The
proof constructs the homology transformation by whiskering that comparison and
composing with the inverse exact-restriction homology isomorphism. It applies
homology to the representative chain equation and proves the localization and
counit calculation in Lean. The main module compiled locally without warnings;
the required delivery dry run checks all three modules and their axiom probes.

Added `Sheaf.Algebra.Homology.BaseTensorDerivedChainComparison` for the remaining
resolution construction. Added `Sheaf.Algebra.Homology.RestrictionCompositeHomology`
for the proved composition identity for restriction homology. Existing signatures,
definitions, visibility, and public imports are unchanged. Updated the parent node
proof and dependencies to match the reduction. No forced adaptations.

## Proved and sorry left

Hole closed: `ModuleCat.exists_baseTensorDerivedComparison`
(`lem-pc-base-tensor-derived-comparison`).

Hole added: `ModuleCat.exists_baseTensorDerivedChainComparison`
(`lem-pc-base-tensor-derived-chain-comparison`). This is a decomposition, not a
sorry-free proof of the derived comparison: one upper hole is replaced by one
lower hole. The remaining statement constructs a single natural transformation
in the derived category, before homology, and gives its chain-level counit
compatibility. The parent proves the separate homology and restriction calculation.

Proved with no holes: `ModuleCat.restrictionCompositeHomology`
(`lem-pc-restriction-composite-homology`) and its private helper
`ModuleCat.homologyIso_comp`.

## No longer needed

Removed the direct proof imports
`Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor` and
`Sheaf.Algebra.Homology.DerivedTensorActionNaturality` from the parent module.
Their nodes `lem-pc-derived-tensor-second-factor-functor` and
`lem-pc-derived-tensor-action-naturality` are retained as dependencies of the
new derived-chain construction’s proof plan. The unfinished construction module
does not import them merely for a future proof. They are not claimed as nodes
pruned from the DAG.
No other existing nodes or modules are pruned. No public imports are removed.

## Where the brief, the DAG or earlier work was wrong

Neither existing proof dependency directly states this natural coefficient
comparison. They provide tensor functoriality and scalar-action naturality; the
resolution comparison itself remains the first step to formalize. The original
DAG's second step also hid a composition identity for the two restriction
homology maps. That identity is now proved from exact-functor homology data.

The local checkout does not contain the untracked Stacks source files. The
source passages were read at [Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6),
[Section 06Y5](https://stacks.math.columbia.edu/tag/06Y5), and the construction
preceding [equation-bc](https://stacks.math.columbia.edu/tag/0DJ6), and the
[comparison-map construction](https://stacks.math.columbia.edu/tag/065Y).
The direct source for the resolution span is Tag 065Y/065Z, which the earlier
node referenced only indirectly through Tag 0DJ7.
LeanSearch returned HTTP 500; Loogle, LeanFinder and source grep were available.

## New nodes

`lem-pc-base-tensor-derived-chain-comparison`: the first construction step, in
`Sheaf.Algebra.Homology.BaseTensorDerivedChainComparison`, independent of i.
The statement requires no flatness, no invertible counit at P, and no chosen
cohomology model. Identity coefficient maps give the usual derived restriction
comparison; zero complexes and zero rings present no additional condition.

`lem-pc-restriction-composite-homology`: the canonical homology isomorphism for
two successive restrictions, in `Sheaf.Algebra.Homology.RestrictionCompositeHomology`.
Its proof compares cycles inclusions by monomorphism cancellation and homology
quotients by epimorphism cancellation, then cancels the intermediate isomorphisms.
It also applies to zero homology and zero coefficient rings. Both nodes remain
below the same unit; no unit statement or step is bypassed. No change records.

## Second reading by E4

1. **Interfaces: pass.** I diffed the parent module against the read-only
   repository. All three existing declaration signatures, both definition bodies,
   docstrings, visibility, and public imports are byte-for-byte unchanged. The
   differences are the theorem proof, its scoped elaboration option, and private
   proof imports. The other two delivered modules are new; no change record or
   forced adaptation is needed.

2. **Proofs: pass.** I read the complete three modules and compiled the set using
   `lcompile.py`. The parent constructs tau by whiskering eta with homology and
   the inverse exact-restriction homology isomorphism; its remaining proof really
   checks the localization, naturality, and composite restriction equation. The
   private short-complex helper cancels the cycles inclusion and the homology
   quotient, then cancels the intermediate homology isomorphisms. The sole sorry
   is `ModuleCat.exists_baseTensorDerivedChainComparison`, with its own node,
   source, and natural-language construction. There are no hollow definitions,
   arbitrary witness-based definitions, or forbidden trust mechanisms. I also
   compiled scratch copies with explicit `#print axioms` for the public
   declarations: the definitions and restriction-composition theorem use only
   `propext`, `Classical.choice`, and `Quot.sound`; the construction and parent
   theorem additionally use the reported `sorryAx`. The delivery dry run probes
   every declaration as well.

3. **New statements and search: pass.** The chain comparison is the resolution
   construction preceding [Stacks equation the project server, Tag 065Y/065Z](https://stacks.math.columbia.edu/tag/065Y). Restriction-composite homology is
   the canonical comparison of kernels modulo images, proved here rather than
   assumed. I checked zero complexes, zero coefficient rings, and identity
   coefficient maps: the statements demand no nonzero object or inverse of the
   counit at an arbitrary representative. The nonflat example R = k[x],
   A = B = D = k causes no problem: the comparison is not asserted invertible.
   The lower hole isolates the degree-independent derived construction; the
   parent separately proves passage to homology and the displayed two-stage
   restriction formula. Thus this is a real decomposition, with one hole closed
   and one added, net zero, not a completed derived comparison. Independent
   LeanFinder search using Kan-extension/localization terminology found generic
   right-derived comparison tools, not this left-derived coefficient map.
   Loogle search for composite `CategoryTheory.ShortComplex.mapHomologyIso`,
   and source grep across Mathlib, Sheaf, and WeilConjectures found no existing
   composition identity or specialized comparison. Two initially unqualified
   Loogle identifiers were unknown; those are not evidence of absence.

4. **Route and imports: pass.** The old two parent proof dependencies are fully
   accounted for under No longer needed and retained in the construction node's
   plan. No unit-level assertion or step is bypassed; the unit record
   `dag/units/sk-thm-picard-semicon.json` is unchanged. The new proof imports of
   the parent are private. I tested replacing the new construction's public
   cohomology-model import with narrower Mathlib imports; this loses the
   `extendScalars_additive` instance needed to elaborate its signatures. I
   restored the import. The restriction-composition module's public imports
   provide change of rings and the homology-comparison definition appearing in
   its signature. No further removable import was found.

5. **DAG: pass.** I compared all three node records with their Lean declarations:
   parent proof_deps are exactly the derived construction and the proved
   restriction identity; the remaining construction has its resolution proof
   plan and source; the restriction node has its complete elementary proof.
   New nodes have the required creation, blueprint, unit, chapter, searches,
   Lean attachment, and verbatim statement fields. Existing-node changes are
   confined to permitted proof fields. No node is claimed pruned from the DAG.

Second reading changed only this report: it records independent interface,
mathematical, import, compilation, and axiom checks. No final Lean or DAG repair
was necessary, and no additional hole was closed or added.
