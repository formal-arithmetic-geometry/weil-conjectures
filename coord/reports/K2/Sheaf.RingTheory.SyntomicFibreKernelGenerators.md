## What changed

Closed the original hole in `Algebra.exists_bounded_fibre_kernel_generators` without changing
its statement, universes, visibility, public imports, or existing docstring. The proof uses
`Ideal.exists_basis_cotangent_localization_of_completeIntersection` and two new, fully proved
modules: `Sheaf.RingTheory.SyntomicPolynomialFibreComparison` and
`Sheaf.RingTheory.LocalizedIdealConormalGeneratorBound`. Their imports in the item are private
proof imports. No other existing module is adapted and no interface change record is needed.

The comparison constructs the multivariate fibre quotient equivalence using explicit tensor
and polynomial universal properties, transports the CI chart and prime, and obtains the natural
localization quotient equivalence with its element formula. The generic finite-ideal theorem
clears conormal denominators and proves the Nakayama generator bound. The item's proved private
helper selects a minimal finite generating set in a quotient of a localization, lifts it back
to the original ideal by clearing unit denominators, and takes the inverse image of the quotient
ideal equality. It never assumes that the original presentation kernel is finitely generated.

All three modules compile cleanly through `lcompile.py`; the complete set compiled in import
order with no errors or warnings, each file well within the 60-second limit. The zero-generator
case needs no special exclusion: empty conormal span plus Nakayama yields the zero local ideal,
and the finite generating set and its `Fin 0` enumeration are handled by the same Lean proofs.
The comparison works with zero variables, arbitrary base rings and different universes for R
and S. A given prime excludes the zero local fibre. No data is selected from an unproved
existence theorem in any definition.

## Proved and sorry left

Closed: `Algebra.exists_bounded_fibre_kernel_generators`
(`lem-weil-pbc-syntomic-fibre-kernel-generators`), the item's only original hole.

Also fully proved, with no new holes:

- `Ideal.spanFinrank_localized_ideal_le_of_conormal_generators`
  (`lem-weil-pbc-localized-ideal-conormal-generator-bound`).
- `Algebra.exists_syntomic_polynomial_fibre_comparison`
  (`lem-weil-pbc-syntomic-polynomial-fibre-comparison`).

Every private helper is fully proved, including the constructed fibre algebra equivalence.
Sorries left in delivered files: none. Holes closed: 1. Holes added: 0. This is a proof, not a
decomposition into new sorries. The existing conormal-rank theorem and its original dependencies
remain in the route; this report does not claim to have closed their transitive proof obligations.

## No longer needed

The old node `lem-weil-pbc-tensor-quotient-base-change` is not used by this proof: the
multivariate fibre quotient comparison is constructed directly from the universal properties.
The old node `lem-weil-pbc-fibre-ring-local-ring-iso` is replaced by the existing stronger natural
comparison `lem-weil-pbc-fibre-ring-local-ring-natural-iso`, because its element formula is needed
to transport the presentation ideal. These two old planned dependencies are removed from the
item's DAG route. No assertion is made that other targets no longer use them.

Polynomial scalar extension, fibre-prime correspondence, and Nakayama are retained through the
new proved comparison and bound modules. The conormal-rank node remains a direct dependency.
The unit `sk-thm-p1` and every node in its realized statement and proof steps are untouched.

No original public import was removed. Removed redundant trial proof imports:
`Mathlib.Algebra.Module.SpanRank`, `Mathlib.RingTheory.Localization.Ideal`, and
`Mathlib.Data.Fintype.EquivFin` from the item; `Mathlib.RingTheory.LocalRing.Basic` from the bound
module; and the `import all` declarations for `Mathlib.Data.Finsupp.Defs` and
`Mathlib.Algebra.MonoidAlgebra.Defs` from the comparison. The required APIs are already visible
through its retained imports. There is no additional unused Sheaf proof-dependency import.

## Where the brief, the DAG or earlier work was wrong

The original theorem and argument are correct, but the five planned dependencies did not
alone expose the precise comparison and conormal-to-ideal generator interfaces. The delivery
fills both gaps with complete proofs rather than postponing them. The new generic bound only
requires the specified ideal finite; it does not require its ambient ring Noetherian. In the
item it is used for the coefficient-field polynomial ideal, which is finite by Noetherianity.

The local Stacks `.tex` file recorded by the old node was absent on this machine, so the source
was read at the canonical Stacks pages: Tag 00SY (3) implies (2), first two proof paragraphs;
Tag 00SC, first paragraph and the conormal-rank implication; and Tag 00DV for Nakayama.
The comparison's natural local fibre formula is supplied by the existing proved
`Ideal.Fiber.localRingHom_surjective_ker_quotientEquiv` (Tag 0H9M).

The blueprint ancestor helper returns `None` because the item's `created.item` is a module name,
not a node id. The new nodes preserve the ancestor already explicitly recorded on the item's
`blueprint.from`: `thm-weil-pbc-finite-etale-lifting`, through the same syntomic/Popescu chain.
Whole-blueprint searches for fibre kernel, conormal generators, polynomial fibre, fibre
comparison, finite ideal, 00SC, and 00SY found no matching blueprint node. Existing DAG nodes
and Lean signatures were read before adding the two missing assertions. LeanSearch returned
HTTP Internal Server Error; this is recorded as unavailable, not as a negative match.

## New nodes

`lem-weil-pbc-localized-ideal-conormal-generator-bound` records the fully proved finite-ideal
Nakayama step, with no CI hypothesis, coefficient field, polynomial presentation, or base-change
assertion. It is strictly the conormal-to-ideal part of the original argument. Its module is
`lean/Sheaf/RingTheory/LocalizedIdealConormalGeneratorBound.lean`.

`lem-weil-pbc-syntomic-polynomial-fibre-comparison` records the fully proved base-change and
localization comparison with ideal compatibility and transported CI neighbourhood. It has no
rank or generator-count conclusion. Its module is
`lean/Sheaf/RingTheory/SyntomicPolynomialFibreComparison.lean`.

Both nodes contain self-contained statements, proof steps, exact Lean signatures, actual
three-kind search records, source places, and blueprint ancestry. The original node's proof,
proof_deps, and proof_origin now follow the compiled Lean proof. No changes to any statement or
existing definition are made; no change records or forced adaptations are needed.

## Second reading by K2

1. Compared the item module and its node with the read-only repository by `diff`.
   The existing theorem signature is byte-for-byte identical, as are its docstring,
   universes, visibility, definitions and public imports. Only private helpers,
   proof imports and the proof were added. The existing node changes exactly `proof`,
   `proof_deps` and `proof_origin`. The other two modules and nodes are new. Verdict: pass.
2. Read all three modules completely and compiled the delivery in dependency order through
   `lcompile.py`: clean, approximately 3.2, 19.7 and 6.9 seconds. There are no textual
   sorries, prohibited declarations, or hollow definitions. The private fibre equivalence
   constructs both maps by universal properties; its use of surjectivity descends a map
   uniquely and does not select arbitrary data from an unproved existence theorem.
   Explicit axiom probes for all three public theorems were compiled in scratch copies;
   the delivery tool additionally probes every declaration. Both new theorems use only
   `propext`, `Classical.choice` and `Quot.sound`. The item also uses `sorryAx` through
   the existing conormal-rank import closure, whose open obligations are not claimed
   closed. No delivered declaration introduces a new hole. Verdict: pass.
3. No statements were split off with sorry. Read the two new proved statements and their
   full proofs: the comparison asserts only the fibre/localization identification and
   transported CI chart, while the generic bound asserts only the finite-ideal Nakayama
   step. Checked the empty-family case (Nakayama gives the zero ideal), I=0, zero
   variables, arbitrary base rings and differing universes. A prime excludes the
   degenerate zero fibre. Independent LeanFinder search used "finite ideal localized at
   prime generated by lifts of spanning conormal module"; grep used
   `Cotangent.*spanFinrank|spanFinrank.*Cotangent|fiberEquivQuotient`.
   The maximal-ideal cotangent-space formula is more specialized, and Mathlib's
   `Polynomial.fiberEquivQuotient` is univariate. Repository searches also found
   `conormal_generators_global_complete_intersection`, whose conclusion is a CI chart,
   not this generator bound. No existing exact replacement was found. Verdict: pass.
4. Checked the top-down route: existing conormal rank, proved comparison, finite-ideal
   Nakayama bound, and explicit lifting of minimal fibre generators by unit denominators.
   The proof never assumes finite generation of the original kernel. The old tensor
   quotient and non-natural local fibre nodes are unused; polynomial scalar extension
   and Nakayama remain through the new proved modules as stated under No longer needed.
   All original dependencies removed from the direct list are thus accounted for.
   Read `dag/units/sk-thm-p1.json`: no realized statement or proof-step node is bypassed
   or changed. The public imports provide statement types; added proof imports are private.
   Verdict: pass after the redundant-import removal below.
5. Checked every node's Lean signature, chapter, unit, ancestry, source and search records.
   Every proof_deps list is exactly the union of its proof steps' uses. The existing
   node follows the actual three-step proof; new nodes record the two strictly smaller,
   fully proved parts. Read the cited Stacks Tags 00SC, 00SY and 00DV to check the
   conormal/Nakayama argument against the source. Verdict: pass.

Second-reading changes: removed redundant private
`Mathlib.RingTheory.Localization.Ideal` from
`LocalizedIdealConormalGeneratorBound.lean`, since its public
`Mathlib.RingTheory.Localization.AtPrime.Basic` already publicly imports that module.
Recompiled the changed file cleanly (4.7 seconds). No mathematical proof or statement
needed repair; no holes were added. Pruned nodes remain the two identified above;
this import cleanup does not claim an additional module pruned from target closure.
