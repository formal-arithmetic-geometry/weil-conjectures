## What changed

Repaired the returned import cycle. The item no longer imports
`Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel`, which now imports and
uses this item. Replaced that circular application by two independent intermediate
statements in new modules `ExteriorTensorKernelRelations` and
`ExteriorSheafRankWedgeZero`, under `Sheaf.AlgebraicGeometry.Modules`.

The complete item proof obtains an epimorphism from `ExteriorTensorQuotient`,
identifies the supplied q using `ExteriorTensorLiftHomExt`, checks each quotient
relation using the prescribed formula for ψ and rank wedge vanishing, applies the
kernel relation criterion, and uses `Abelian.epiDesc` and `Abelian.comp_epiDesc`.
All four proof imports are private. Existing signatures, definitions and public
imports are unchanged; no other existing module is adapted. Updated the item's
proof, proof_deps and proof_origin and supplied matching nodes for the two new modules.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.determinant_wedge_quotient_factor`
(node `lem-sc-determinant-wedge-quotient-factor`). No hole remains in that module.

Added two holes, each the whole proof of a named public theorem in its own new module:

- `AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_eq_zero_of_relations`
  (node `new-j1-exterior-tensor-kernel-relations`, module
  `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations`). This is the general
  quotient relation criterion for an arbitrary first factor and arbitrary target,
  with no rank, local freeness, wedge value formula, or factorization conclusion.
- `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_rank_wedge_eq_zero`
  (node `new-j1-exterior-sheaf-rank-wedge-zero`, module
  `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero`). This asserts only
  vanishing of a specified wedge section, for any morphism from a rank-r locally free
  sheaf; no exact sequence, quotient morphism, or factorization is involved.

This is a decomposition: one upper hole closed and two lower holes added, net -1,
not an axiom-free proof of the import closure. Both lower statements are separate
parts of the original argument (quotient relations and rank vanishing); the item
combines them with independently proved epimorphy and categorical descent in Lean.
Neither new statement duplicates the factorization statement or chooses data.
All three delivered modules compile in dependency order through lcompile.py.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel`
and its direct node dependency `new-determinant-lift-wedge-kernel`. That module remains
used by other library modules; no claim of global pruning is made. The repaired proof
also eliminates the comparison of a constructed w with ψ: it kills the kernel of
ψ directly, so no wedge-map existence import or theorem is needed here.

Relative to the repository's original direct proof_deps:

- `def-sc-sheaf-exterior-power` is still needed by the statement and new relation
  criterion, but no longer a separate direct proof step of this item.
- `lem-sc-exterior-sheaf-map-exists` is replaced here by the proved tensor exterior
  quotient construction `new-exterior-tensor-quotient`.
- `lem-weil-pbc-exterior-power-free-basis` remains a dependency of the new rank
  vanishing node rather than a direct dependency of the item.

Retained `ExteriorTensorQuotient` and the explicit `ExteriorTensorLiftHomExt` proof
imports; the latter is not made visible by the former's private import. Added only
the two new independent proof imports. Removed the unused public import `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`
from the new rank-vanishing module during second reading. It remains needed in the
item and relation module, so this does not prune a module from the target closure.
No other imports or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery depended on `determinant_liftWedge_kernel_exists` as if it
were an independent lemma. Its current source proves that theorem using this
factorization item, creating the reported two-module cycle. The previous second
reading did not detect that source-level circularity. Removed the stale second
reading from this repaired report so an independent reader can assess the new proof.

The repair retains the original determinant argument: exterior quotient relations,
vanishing after r+1 first-term factors, and categorical descent. The unit
`sk-thm-picard-rr` and all its steps and realized records are unchanged. Rank zero,
second degree zero, arbitrary noninjective f in the rank lemma, empty schemes,
empty opens, and zero rings are covered by the new theorem docstrings. In particular,
for second degree zero the relation test is vacuous and the quotient is the identity;
for rank zero the additional image factor is zero. Kernel relations are interpreted
locally or stalkwise, never by assuming that short exactness is surjectivity on every
open's section module.

Searches found ordinary-module exterior presentation and basis infrastructure,
but no independent sheaf-level relation criterion or full-rank wedge vanishing lemma.
The leansearch service was unavailable and is recorded as such. No source library,
existing statement, target signature, or definition has been changed. There are no
forced adaptations and no interface change record is required.

## New nodes

`new-j1-exterior-tensor-kernel-relations` records the quotient relations step of the
original item's proof: after tensoring, the kernel is locally generated by wedge
relations with an argument in the image of the first map. Its docstring gives the
complete stalkwise presentation argument and explains the degree-zero case.

`new-j1-exterior-sheaf-rank-wedge-zero` records the rank vanishing step: trivialize,
expand r+1 first-term entries in r basis vectors, use alternation, and glue by
separatedness. It cites the existing exterior free basis node. Each new node has
its own one-theorem module, unchanged source and unit ancestry, recorded searches,
and a complete proof in words. No change records are added.


## Second reading by J1

1. **Interfaces: PASS.** Read the complete diff of the item against the repository.
   Its sole existing theorem signature is byte-for-byte identical, including all
   hypotheses, universes, conclusion and visibility. Only four private proof imports
   and the proof body differ. There are no existing definitions changed, forced
   adaptations, or interface change records. The two other delivered modules are new.
2. **Proof and axioms: PASS as a decomposition.** Compiled all three modules in import
   order locally. Scratch copies with `#print axioms` for each delivered theorem
   compile and report exactly `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
   The item has no sorry; the only two delivery sorries are the named theorems listed
   above, each with a source, complete proof docstring and matching node. No axiom,
   unsafe, opaque, implemented_by, extern, data definition, or hidden proof hole is
   added. The proof identifies q by pure-generator extensionality, transports Epi,
   kills the kernel using the two separate relations/rank arguments, and applies
   categorical descent. The temporary q witness is uniquely determined by its pure
   wedge formula; no arbitrary data is defined from an unproved existence theorem.
3. **Split statements: PASS.** The relations lemma is valid without a flat first
   tensor factor: right exactness gives the quotient by the image of the relation
   submodule, and does not assert that tensoring preserves its injection. Stalks and
   common neighborhoods justify the section tests; exactness is never interpreted
   as surjectivity on all opens. Degree s=0 gives an isomorphism with zero kernel
   despite the vacuous relation test, and r=0 gives the unit first factor. The rank
   lemma needs no injectivity of f, field, reducedness, or nonzero ring: on a free
   chart expand the r+1 source entries, and alternation kills each basis term.
   Rank r=0 forces d=0 locally; s=0 has no j. Empty schemes/opens are harmless.
   Both statements are proper components, not renamings of the factorization.
   Repeated searches using different words (LeanFinder, Loogle, targeted Mathlib rg,
   and repository rg) found repeated-entry vanishing, basis extensionality and
   exterior spanning/presentation infrastructure, but no independent sheaf-level
   statement closing either hole in a few minutes. The domain/torsion-free
   hypotheses of `AlternatingMap.map_linearDependent` prevent its use here.
4. **Route and pruning: PASS.** Read the upstream quotient construction and lift
   extensionality, the circular lift-wedge-kernel module and the unit record.
   The item does not import that circular module: the current latter module imports
   this item, so using it in reverse would be invalid. All four private item imports
   are actually used. The old direct proof dependencies and their replacements are
   completely listed under No longer needed. The existing unit realization record
   is unchanged (its statement and step arrays are empty); no unit or chapter step
   is bypassed by the relations, rank-vanishing and descent route. No globally
   unreachable module is claimed.
5. **DAG: PASS after metadata repair.** The existing node changes only proof,
   proof_deps and proof_origin. Its four proof dependencies match the four private
   imports and actual calls. Each node's proof_deps equals its step-use union.
   New nodes have source, ancestry, chapter/unit, creation, searches, status and
   matching Lean declaration records. Replaced their whitespace-normalized Lean
   statement records by verbatim signatures, and corrected the rank node's copied
   quotient-search evidence with the independently run rank/basis searches.

Second reading changed only the unused public TensorSection import in the new
rank module, verbatim signature metadata, search metadata and this report. It
retained the correct Lean reduction and both true, strictly smaller open lemmas.
The first dry run required a separate LeanSearch entry for the rank node. Ran it,
recorded its Internal Server Error without a mathematical verdict, and retained
the independent Loogle/LeanFinder and grep evidence.
The delivery closes one upper hole and adds two lower holes: decomposition, net -1.
