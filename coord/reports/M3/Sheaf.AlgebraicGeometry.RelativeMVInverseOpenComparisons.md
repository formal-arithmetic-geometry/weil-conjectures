## What changed

Replaced the sorry in `AlgebraicGeometry.relativeMV_inverse_open_comparisons`
with the explicit family `relativeMVInverseOpenIso g' f' W K'`. The proof supplies
its unit and restriction equations from proved lemmas and its remaining
base-change equation from a named fixed-comparison mate lemma.

Added `Sheaf.AlgebraicGeometry.RelativeMVInverseOpenIso`: all definitions are
actual compositions of isomorphisms, using `pullbackRestrictIsoRestrict`, the
invertible unit for pullback along a scheme isomorphism, and uniqueness of
adjoints. Proved `relativeMVIsoPullbackUnit_isIso`,
`relativeMVInverseOpenIso_unit`, and `relativeMVInverseOpenIso_restriction`.
The restriction proof is first carried out for an arbitrary typed scheme
factorization, then specialized to `relativeMVOpenLift`; this keeps kernel
checking within the per-file limit.

Added `Sheaf.AlgebraicGeometry.RelativeMVInverseOpenMate`, with one named sorry
for the pasted-mate identity of the explicitly constructed comparison. The
item imports this module privately. Existing signatures and public imports
are unchanged; no other existing module is adapted.

Validation: `lcompile.py --all` compiled all three modules in import order.
Read the Stacks sources online at Tags 08HY and 08HZ, since the local clone
contains citation tables but no downloaded cohomology.tex. Read the corresponding
Mathlib adjunction and open fibre-product constructions and the library's
pinned composition, adjunction, and exact-open comparison declarations.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.relativeMV_inverse_open_comparisons`
(node `lem-pc-relative-mv-inverse-open-comparisons`). Its body contains no sorry.

New hole added: `AlgebraicGeometry.relativeMVInverseOpenIso_mate`
(node `lem-pc-relative-mv-inverse-open-mate`), in the new module
`Sheaf.AlgebraicGeometry.RelativeMVInverseOpenMate`. Its proof is exactly
`:= by sorry`. This is the only sorry in the delivery.

This is a decomposition, not a proof eliminating all transitive holes: one upper
hole is closed and one strictly smaller mate-compatibility hole is added. The
comparison's construction and both its unit and nested restriction identities
are now proved, rather than postponed. No definition chooses arbitrary data
from an unproved existence theorem. The chosen composition comparisons and
adjunctions are the existing canonical, uniquely pinned library data.

The new mate statement was checked on empty and top opens, equality inclusions,
zero objects, and zero coefficient maps. All comparisons are specified natural
isomorphisms, and each base-change factor is a counit mate, so these cases use
exactly the same identities. It does not quantify over an arbitrary comparison
isomorphism, and therefore does not admit the automorphism twist in the earlier
rejected attempt.

## No longer needed

None. No existing import, module, or mathematical dependency is pruned.
The old node's direct proof-dependency list is replaced by the two new nodes;
the original geometric and adjunction dependencies remain needed beneath them.
No unnecessary import of `SingleComplexOpenTop`,
`DerivedBaseChangeMayerVietorisSquares`, or an unrelated supported-open theorem
was added. The sandbox's earlier submission remains in scratchpad only and
is excluded from the delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier submission left existence/unit/restriction as a core hole and
claimed the base-change formula for arbitrary isomorphisms e. That statement
was false because twisting e changes its hom. This attempt constructs e from
pinned adjunction comparisons and proves its unit and restriction equations;
the remaining lemma explicitly uses that construction.

The original node's plan is valid but its cited declarations do not themselves
state the remaining pasted-mate equality. That equality is now a separate
smaller item with its precise type, source, and complete proof plan.
The blueprint unit has no realized statement or step in either the original
node or the new ones; no unit route is bypassed. No target statement, hypothesis,
conclusion, universe, or definition used by a target was changed.

## New nodes

`lem-pc-relative-mv-inverse-open-iso`, module
`Sheaf.AlgebraicGeometry.RelativeMVInverseOpenIso`: the actual comparison
construction and its proved unit and restriction identities. Its source is
Tags 01JR, 08HZ, and 08HY and adjunction uniqueness. It has no direct sorry.

`lem-pc-relative-mv-inverse-open-mate`, module
`Sheaf.AlgebraicGeometry.RelativeMVInverseOpenMate`: only the pasted-mate
identity for the specified comparison, with the adjoint-counit expansion and
coherence calculation described in its docstring and node. This is the sole
new unproved statement. Both nodes are beneath the inverse-open step of the
Tag 0DJ9 induction diagram of `lem-pc-rf-perfect-base-change`.

There are no change records because no existing interface changed.

## Second reading by M3

1. **Unchanged declarations: pass.** I compared the delivered existing module
with the repository version. Its theorem signature and all existing declarations
are unchanged; the only existing-file change is the proof import and proof body.
The two supporting modules are new, and no target statement or definition was
modified.

2. **Proof checking: pass with the reported residual hole.** I compiled all
three delivered modules with `lcompile.py --all` and compiled the target file
individually. The only textual `sorry` is the named public theorem
`relativeMVInverseOpenIso_mate`; there are no forbidden declarations or hollow
definitions. The target proof itself contains no `sorry`.

3. **Split statement: pass as a decomposition.** The mate theorem is a fixed
comparison identity for the explicitly constructed `relativeMVInverseOpenIso`.
It is strictly smaller than the original existence theorem and does not merely
rename it. Its statement covers empty and top opens, identity inclusions, zero
objects, and zero coefficient maps without extra hypotheses. Its docstring gives
the adjunction-mate calculation and its DAG node records the same signature.

4. **Route and pruning: pass.** The construction uses actual canonical
isomorphism compositions, then proves the unit and restriction equations via
adjunction uniqueness and fully faithful open direct image. The target's third
conjunct is isolated exactly as the remaining mate node. No imported module was
unused or pruned, and the stated inverse-open route is retained.

5. **DAG agreement: pass.** The proof and `proof_deps` of the original node
match the delivered imports and theorem applications. The two new nodes contain
their required source, proof plan, searches, creation metadata, unit and verbatim
Lean declarations. No unit record or existing interface was changed.

Changes made in this reading: none to Lean or DAG files; this report section was
added after the independent compile and diff checks.
