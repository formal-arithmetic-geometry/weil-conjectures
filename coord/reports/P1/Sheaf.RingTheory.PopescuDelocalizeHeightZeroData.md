## What changed

In `Sheaf.RingTheory.PopescuDelocalizeHeightZeroData`, replaced the proof of
`Algebra.exists_popescu_resolution_data_of_local_height_zero` with a complete Lean assembly:

1. Obtain finite generators of the singular ideal using Noetherianity of A.
2. Use dimension-zero local nilpotence in Mathlib and localization's zero criterion to
   obtain an exponent and an annihilator outside q for each generator individually.
3. Apply the existing weak delocalization declaration, then extract a singular element
   of C whose image escapes q using the ideal map/comap adjunction.
4. Apply the new auxiliary-witness construction statement.
5. Prove radical ideal containment from the generator-power witnesses, and noncontainment
   from the product witness and primality of q.

Added proof imports of `Mathlib.RingTheory.KrullDimension.Zero` and
`Sheaf.RingTheory.PopescuHeightZeroAuxiliaryWitnesses`. The existing public import and all
existing declaration signatures and visibility are unchanged. No definitions were added.
Both modules compile together through lcompile.py without warnings.

The new theorem isolates the explicit polynomial quotient, its evaluation map, and the
singular elements obtained from its two localizations. It has no prime, height, minimality,
or local-resolution hypotheses; it does not assert resolution or ideal containment.
The original theorem genuinely proves those clauses from its witness equations.

## Proved and sorry left

Closed the original hole in
`Algebra.exists_popescu_resolution_data_of_local_height_zero`
(node `lem-weil-pbc-popescu-delocalize-height-zero-data`). There is no sorry in the assigned
module.

Added one hole:
`Algebra.exists_popescu_height_zero_auxiliary_witnesses`
(node `lem-weil-pbc-popescu-height-zero-auxiliary-witnesses`), in the new module
`Sheaf.RingTheory.PopescuHeightZeroAuxiliaryWitnesses`. Its proof is exactly `by sorry`;
its docstring and node give the explicit quotient construction and smoothness arguments.

This is a decomposition, closing one hole and adding one, with net zero holes removed.
The existing weak-delocalization theorem is imported with its existing sorry; this delivery
does not add that hole or attempt to prove work belonging to its module.

## No longer needed

No Lean imports were removed; the assigned module originally had only its public import
of `Sheaf.RingTheory.PopescuDelocalizeWeak`, which is used.

Removed `lem-weil-pbc-popescu-delocalize-height-zero` from the assigned node's proof_deps.
Its module `Sheaf.RingTheory.PopescuDelocalizeHeightZero` already imports the assigned
module and applies its theorem, so using that recorded dependency would be circular.
This removes a circular proof edge, not that caller module from the targets' import closure.
No complete module is claimed to have been pruned. The auxiliary-localization nodes and
smoothness tools remain needed for the new construction statement.

A common exponent and an Artinian assertion about Lambda_q are unnecessary: the proof
keeps separate exponents and separate annihilators, and the construction uses their product.

## Where the brief, the DAG or earlier work was wrong

The assigned node's sole recorded proof dependency was its already-proved caller,
`lem-weil-pbc-popescu-delocalize-height-zero`. That is not usable as a proof route.
The updated node records weak delocalization, the auxiliary witnesses, and the direct
Mathlib/ideal arguments actually used.

The local Stacks TeX file is absent on this machine. Read the source online at
[Stacks 07FA](https://stacks.math.columbia.edu/tag/07FA). The parent node already corrects
three issues in the printed proof: dimension zero without Noetherianity does not imply
Artinianity; B_z has t variables rather than y variables; B_z is smooth over C, and one
must invert c' as well to obtain a smooth R-algebra. The new statement retains those
corrections. No statement of the original module, a target, a unit, or a chapter changed.

Mathlib searches found the exact dimension-zero nilpotence theorem
`Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal`, which is used directly. Searches for the
auxiliary witness theorem found no match. LeanSearch returned Internal Server Error and
is recorded as unavailable. Loogle does not index `Algebra.singularIdeal`; its unknown-name
result is not evidence of a theorem match. LeanFinder and Mathlib grep gave no matching
auxiliary construction. Repository search found only the existing localization interfaces.

`tools/blueprint_refs.py ancestor` returns None for the assigned node because its created.item
is a module name rather than a node id. The new node uses the explicit ancestor and route
recorded on the original height-zero node, without altering fields outside stage-3 ownership.

## New nodes

`lem-weil-pbc-popescu-height-zero-auxiliary-witnesses`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-height-zero-auxiliary-witnesses.json`,
records `Algebra.exists_popescu_height_zero_auxiliary_witnesses` in
`lean/Sheaf/RingTheory/PopescuHeightZeroAuxiliaryWitnesses.lean`.
It covers construction and smooth-localization steps 4-6 of the parent's proof, with
individual exponents in place of a uniform exponent. It is strictly a subargument: it
assumes a given intermediate factorization and explicit annihilation equations, and returns
singular-element witnesses, leaving the prime geometry and ideal-containment proof to the
assigned theorem. Empty generator sets are allowed (B=C[z], empty product one); zero
exponents force the corresponding annihilator to zero and do not invalidate the construction.
Zero rings and zero variables/relations require no nontriviality hypothesis in this lemma.
No arbitrary witness is used as data of a definition. No change record is needed because
existing interfaces are unchanged.

## Second reading by P1

1. **Statements and interfaces.** Compared the delivered height-zero data module with the repository version. The existing target theorem signature is byte-for-byte unchanged; only proof imports and proof text changed. The auxiliary theorem is a new, explicitly stated subargument and does not alter existing interfaces.

2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The target theorem uses the auxiliary theorem, whose proof remains the documented split-off `sorry`; no `sorry` occurs inside a definition, and no forbidden declaration forms were added.

3. **New statement review.** The auxiliary witness statement is strictly weaker than the parent target: it assumes a factorization and annihilation equations and returns only singular-element witnesses plus finite presentation. Its explicit polynomial quotient construction handles empty finite sets and zero exponents, and its docstring gives the source and proof argument. Repository and Mathlib searches found no existing declaration matching it.

4. **Pruning and dependencies.** The assigned proof follows the unit route through weak delocalization, generator-wise localization nilpotence, and the auxiliary witness construction. The former dependency on the caller height-zero theorem was removed as circular. Plain proof-only imports remain non-public; the weak-delocalization import remains public.

5. **DAG agreement.** Updated proof steps, proof dependencies, and proof origin match the Lean proof. The new node records its theorem, source, route, searches, and split status. The unit `sk-thm-p1` route is preserved.

**Changes made:** no mathematical repair was needed after review; added this second-reading record only. Dry-run delivery validation is the remaining check.
