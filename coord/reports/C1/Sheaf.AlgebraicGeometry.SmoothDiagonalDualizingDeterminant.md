## What changed

Replaced the sole sorry of `AlgebraicGeometry.smoothDiagonal_dualizing_determinant`
with a complete Lean reduction. Its signature and existing docstring are unchanged.
The proof constructs the local regularity witness from
`exists_isRegular_smooth_diagonal_generators`, converts regular lists to Koszul-regular
sequences, and handles the unit-ideal alternative by the Koszul-regular singleton 1.
Noetherianness is established from finite type and quasi-compactness using Mathlib.
It applies `koszulRegularImmersion_dualizing` at the literal structure single lifted
into the quasi-coherent full subcategory, then transports the supplied object through
`c` and composes the underlying derived isomorphisms. Internal Hom functoriality
provides the dual conormal isomorphism.

Two strictly smaller statements are split off into new modules:
`SmoothDiagonalIdealConormalRank` proves a sheaf-level comparison and stalk rank,
without any adjoint or derived category; `ConstantRankExteriorDerivedComparison`
identifies a constant-rank exterior complex for arbitrary isomorphic module sheaves,
without smoothness, properness, local freeness or an adjunction.

The main module adds proof-only imports of
`Sheaf.AlgebraicGeometry.SmoothDiagonalRegularGenerators`,
`Sheaf.RingTheory.RegularSequenceKoszulRegular`,
`Sheaf.AlgebraicGeometry.SmoothDiagonalIdealConormalRank`, and
`Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`.
The DAG proof and proof_deps now reflect this reduction. No definitions, existing
statements, public imports, target signatures or downstream interfaces changed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.smoothDiagonal_dualizing_determinant`
(node `lem-sc-smooth-diagonal-dualizing-determinant`). Its file now contains no sorry.
The private singleton-one helper is also proved, without a new hole.

Added exactly two holes, each an entire named public theorem proof:

- `AlgebraicGeometry.smoothDiagonal_idealConormal_iso_and_rank`, in
  `Sheaf.AlgebraicGeometry.SmoothDiagonalIdealConormalRank`, node
  `lem-sc-smooth-diagonal-ideal-conormal-rank`.
- `AlgebraicGeometry.Scheme.Modules.constantRankExterior_derived_iso`, in
  `Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`, node
  `lem-sc-constant-rank-exterior-derived-comparison`.

This is a decomposition, not a sorry-free proof of the target closure: one upper
hole closed and two smaller holes added, net -1 for these delivered declarations.
Existing dependency holes, including `koszulRegularImmersion_dualizing`,
`exists_isRegular_smooth_diagonal_generators`, and the regular-to-Koszul implications,
are unchanged. Each new statement has source, complete proof in words, and node.
All three modules compile cleanly through lcompile.py. The delivery dry run passed
its local compilation, axiom probe, and preflight except for the second reading,
which is intentionally reserved for the next worker; nothing was pushed.

## No longer needed

Removed four direct proof-only imports from the item's module:

- `Sheaf.AlgebraicGeometry.DiagonalConormalDifferentials`: its comparison is used in
  the plan of the new ideal-conormal statement and remains imported by that module;
  node `lem-sc-smooth-proper-diagonal-conormal-differentials` is still needed there.
- `Sheaf.AlgebraicGeometry.SmoothDiagonalKoszulRegular`: the stronger theorem
  `smooth_diagonal_koszul_regular_perfect_proper` is unnecessary. The proof uses
  `exists_isRegular_smooth_diagonal_generators` directly and needs neither the
  perfectness conclusion nor derived categories on every open subscheme.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: already available through the public
  imports of the existing statement interface and the new comparison module.
- `Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex`: already available through
  Koszul duality and the new comparison module.

An import-closure comparison before and after this delivery finds exactly one
module pruned from this item's closure:
`Sheaf.AlgebraicGeometry.SmoothDiagonalKoszulRegular`, corresponding to node
`lem-sc-smooth-proper-diagonal-koszul-regular`. All its other transitive dependencies
remain reachable by other retained imports, so none are claimed pruned. Global
pruning still depends on whether other target paths import this module.
The former direct proof dependency `lem-sc-smooth-omega-finite-locally-free` moves
under the new conormal-rank comparison and is still needed. The former direct dependencies `def-sc-locally-ranked-exterior-complex` and
`def-sc-sheaf-exterior-power` move under the new exterior-comparison node and remain
needed. `def-pc-derived-category` remains a direct dependency. None was eliminated.

## Where the brief, the DAG or earlier work was wrong

The smooth diagonal perfectness wrapper requires derived-category instances on
every open of the fibre product; the item's hypotheses give only the two global
instances. This is an interface mismatch, not a false statement. The lower regular
 generator theorem gives exactly the local input needed without those instances.

`diagonalConormal_iso_relativeDifferentials` uses the actual module-sheaf kernel,
whereas Koszul duality uses `i.ker.toModules`, the ideal sheaf presented through its
closed subscheme. They are isomorphic for a closed immersion, but the needed Lean
comparison and stalk-finrank bridge were absent. The new conormal theorem isolates
that missing sheaf-level argument, using the existing differential comparison and
finite-local-freeness theorem in its proof plan.

The exterior sheaf API has no functoriality theorem for its custom sheafification
construction, and the locally ranked complex API has no constant-rank comparison.
The new general exterior-complex statement isolates these parts of the final step.
The main proof itself performs the internal Hom and adjunction transport.

Edge cases checked mathematically: empty X makes the stalk assertion vacuous and
all sheaves and complexes zero; d=0 gives a zero conormal stalk and the zeroth exterior
power in degree zero. The general complex comparison works for arbitrary module
sheaves and does not assume a nontrivial global ring. Different derived universes
wX and wP are preserved. The unit `sk-thm-picard-duality` has no realized node that
this reduction bypasses; its route is unchanged.

The repository does not contain the downloaded Stacks .tex sources on this machine.
The current statements and proofs of Tags 0BR0, 08S2 and 02G1 were read on the Stacks
website. The new expanded implementation arguments are marked agent-origin in
the DAG, with their mathematical source tags stated explicitly. LeanSearch was
unavailable (Internal Server Error), recorded as unavailable; LeanFinder and Mathlib
grep searches ran and yielded no exact matching sheaf-level declarations. Blueprint
searches for constant-rank exterior, diagonal conormal, 0BR0 and 08S2 found no
existing blueprint statement replacing the new lemmas.

## New nodes

`lem-sc-smooth-diagonal-ideal-conormal-rank`, module
`Sheaf.AlgebraicGeometry.SmoothDiagonalIdealConormalRank`: compare the ideal-sheaf
conormal with relative differentials and transport local rank d to stalk finrank.
Source: Stacks Tags 08S2 and 02G1. Existing conormal and finite-local-freeness results
remain dependencies, with the representation comparison and stalk calculation
written in the natural-language proof. The lemma involves only ordinary sheaves.

`lem-sc-constant-rank-exterior-derived-comparison`, module
`Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`: the constant-rank
complex is the shifted single exterior sheaf, transported along a given sheaf
isomorphism. Source: the locally constant shift convention of Stacks Tag 0BR0.
The statement has no geometric or duality hypotheses and supplies just the final
complex comparison in the main argument.

No change records are required: no existing statement, definition or public import
was changed.


## Second reading by C1

1. **Interfaces: pass.** Compared the delivered main module with the repository
   using a textual diff and separately checked its theorem signature byte for byte.
   The signature, existing docstring, definitions, and public imports are unchanged.
   The only additional declaration there is a private proved helper. The other two
   modules are new; there are no adaptations or statement-change records to review.
2. **Proof and axioms: pass as a decomposition.** Independently compiled all three
   modules through `lcompile.py --all`, without errors or warnings. Scratch copies
   with `#print axioms` for the three public theorems showed only `propext`,
   `Classical.choice`, `Quot.sound`, and the expected `sorryAx`. The main proof has
   no sorry; each new module has exactly its reported whole named theorem hole.
   No forbidden declarations or hollow definitions were added. The proof transports
   OP along its given isomorphism; it constructs no arbitrary data from existence
   theorems. The existing exterior restriction choice is uniquely characterized.
3. **Split statements: pass.** Read both complete proof docstrings, their node
   records, and the definitions of diagonalConormal, idealSheaf.toModules, module
   stalks, exteriorSheaf, and locallyRankedExteriorComplex. Independently checked
   [Tag 08S2](https://stacks.math.columbia.edu/tag/08S2),
   [Tag 02G1](https://stacks.math.columbia.edu/tag/02G1), and
   [Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0).
   The conormal comparison uses closedness and smoothness precisely as stated;
   stalk rings at scheme points are nontrivial. The exterior comparison holds
   without freeness: it uses only the constant rank strata and exterior-power
   functoriality. Checked empty X, d=0, positive d, and arbitrary input module
   sheaves. Both statements are strictly smaller than the adjoint determinant
   theorem, and neither restates it. Independent LeanFinder searches for a complex
   supported in one degree and for stalk rank of locally free sheaves, a Loogle
   kernel-isomorphism search, Mathlib grep, and repository searches found the general
   tools `CochainComplex.exists_iso_single`, `kernel.mapIso`, and localization rank
   lemmas, but no existing full comparison that would eliminate either hole in a
   short proof. Those tools support the written plans; the sheaf comparisons still
   need formalization. Search queries and results are in searches.jsonl.
4. **Route and pruning: pass.** Read the local regular-generator and Koszul-duality
   statements and checked the main proof from the target downward. Noetherian
   instances come from Mathlib; regularity uses the existing lower generator theorem,
   and the unit ideal branch is handled by a proved singleton-one helper. The two
   new statements supply only the missing comparisons. Imports used solely by proofs
   are plain imports. The removed-dependency list is now explicit for every former
   direct dependency absent from the new proof_deps, distinguishing dependencies
   moved below a new comparison from the discarded perfectness wrapper. An independent
   import-closure traversal confirms that only SmoothDiagonalKoszulRegular is removed
   from this item's closure. Read sk-thm-picard-duality's realized map: its statement
   and step arrays are empty, and no recorded unit realization is bypassed.
5. **DAG: pass.** The existing node changes only proof, proof_deps, and proof_origin.
   Each delivered node's proof_deps is exactly the union of its proof steps' uses.
   The new nodes have source, statement dependencies, agent proof origin, search
   records, creation and blueprint ancestry, matching unit/chapter, and Lean records
   matching their declarations. The actual proof agrees with the updated route.

Second-reading changes: made the no-longer-needed list explicit for the exterior
complex and exterior-power definition nodes, and added this independent review.
No Lean proof, statement, definition, import, or node needed repair. One original
hole is closed by reduction and two smaller holes remain: this is a decomposition,
with net -1 holes closed minus added, not a completed target-closure proof.
