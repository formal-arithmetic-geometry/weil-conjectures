## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.alternatingCechRestrictionHomotopy_map`
with a compiled proof, without changing its signature. Its only new import is the
proof-only import `Sheaf.AlgebraicGeometry.SignedCechExtension`.

The new module constructs `signedCechExtensionValue` explicitly: sort an injective
tuple, multiply by the permutation sign, and apply the presheaf restriction along
`S.indexMap`; repeated tuples receive zero. `signedCechExtension` bundles this
construction as a group homomorphism. `signedCechExtension_increasing` proves that
its increasing coordinates recover the input. None of these constructions depends
on an unproved existence theorem.

The main proof composes this extension with each `e p`. It proves the degreewise
section identities using `hr` and cancellation of `e p`. Applying the chain-map
equation for `r` to these explicit lifts identifies the increasing coordinates of
their differential. Differential stability of signed extension then gives the
commutation equations, and `CochainComplex.ofHom` assembles the section.

Sources read: [Stacks Section 01FG](https://stacks.math.columbia.edu/tag/01FG),
including the signed-extension formula following Definition 01FI, and
[Lemma 01FJ](https://stacks.math.columbia.edu/tag/01FJ) and
[Lemma 01FK](https://stacks.math.columbia.edu/tag/01FK).
The source omits the differential calculation; its explicit argument is written
in the new theorem's docstring and node. No covering hypothesis is needed by that
calculation, so the arbitrary-family hypothesis of this item is retained.

Both delivered modules compile through `lcompile.py --all`, without warnings.
The independent formal-coefficient check in `scratchpad/check_signs.py` passed
6,674 tuples for index cardinalities 0 through 4 and cochain degrees 0 through 4.
It compares each ordered-face coefficient separately, including nonconsecutive
repeated pairs, triple repetitions and two repeated pairs. The empty-index case
is vacuous because every tuple type has positive length; no inhabited-index
hypothesis is introduced. The sign check validates finite cases; the universal
Lean differential calculation remains the named hole listed below.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.alternatingCechRestrictionHomotopy_map`
(node `lem-pc-alternating-cech-section`). No sorry remains in the item's module.

Also proved additivity of the explicit construction and
`AlgebraicGeometry.Scheme.signedCechExtension_increasing`.

Added exactly one hole, with proof exactly `:= by sorry`:
`AlgebraicGeometry.Scheme.signedCechExtension_differential`
(node `lem-pc-signed-cech-extension-differential`, module
`Sheaf.AlgebraicGeometry.SignedCechExtension`). It says that the differential of
an explicit signed extension is recovered by signed extension of its increasing
coordinates. It contains no abstract complex `A`, no isomorphisms `e`, no map `r`,
and no existential section conclusion. It is the differential-compatibility
part of the argument, rather than a renamed section-existence statement.

This delivery is a decomposition: one original hole closed and one lower hole
added, for net zero holes. It does not claim an axiom-free proof of the original
statement while the lower differential lemma is unfinished.

## No longer needed

No import, node, or module was pruned. The two original public imports are needed
by the unchanged statement. The new module's imports supply the scheme, chosen
Čech intersections, tuple sorting, and permutation sign used by its actual data.

The planned preliminary extension by zero and its separate surjectivity argument
are unnecessary: the signed extension itself supplies the degreewise lifts. No
existing dependency module corresponding to this discarded step was imported.

## Where the brief, the DAG or earlier work was wrong

The original node had a single large proof step combining construction, sign
calculation, and transport through `e`; its only proof dependency was the Čech
complex definition. That definition does not state the sorting-sign differential
calculation. The delivery makes the construction and the transport actual Lean,
and names only the remaining differential-stability calculation as a new item.

The blueprint ancestor command returns None for this module because the older
created records name modules. Reading the node chain explicitly identifies
`lem-pc-projective-space-cohomology-bound` as the imported blueprint ancestor,
through the alternating-comparison nodes. The new node records that chain.
The unit `sk-thm-picard-pn` and its route are unchanged.

LeanSearch was unavailable (HTTP internal-server error), recorded as unavailable.
LeanFinder returned standard-complex and Dold–Kan lemmas but no signed extension
for ordered Čech tuples. Loogle supplied the permutation-sign API. The logged
Mathlib grep found no signed Čech or sign/succAbove result. Blueprint and DAG
searches found the existing alternating-comparison nodes, which do not state
this explicit degreewise differential-stability lemma.

## New nodes

`lem-pc-signed-cech-extension-differential` is a single new statement node in
`sec-picard-framework`, with a new module
`lean/Sheaf/AlgebraicGeometry/SignedCechExtension.lean`. It isolates stability of
the explicitly constructed signed-extension image under the full Čech
differential. Its docstring and node give the deletion-sign identity for
distinct tuples and the repeated-pair cancellation argument. The node contains
the actual three kinds of search, with the failed service marked unavailable.
The item's node now records the compiled assembly proof and this dependency.
No statements or definitions of existing modules changed, no change record was
needed, and there are no forced adaptations.

## Second reading by K2

1. **Unchanged interface: PASS.** Diffed both delivered modules against the
   repository: SignedCechExtension is new; AlternatingCechSection changes only its
   proof, proof docstring, and a plain proof-only import. Independently extracted
   the original theorem signature through `:= by` and checked byte-for-byte
   equality. No existing definition, visibility, hypothesis, or conclusion changes;
   no change record or forced adaptation is needed.

2. **Proof and construction: PASS, conditional on the reported lower hole.**
   Recompiled both modules through `lcompile.py --all` with no errors or warnings.
   Read the componentwise section proof, the use of `r.comm`, the ordered-coordinate
   equality, and the assembly with `CochainComplex.ofHom`. There is no sorry in the
   item's module and exactly one named theorem with `:= by sorry` in the new module.
   Inspected every declaration for forbidden trust mechanisms and hollow data.
   A scratch-copy `#print axioms` check gives only `propext`, `Classical.choice`,
   and `Quot.sound` for signedCechExtensionValue, signedCechExtension, and
   signedCechExtension_increasing. The original theorem and the differential lemma
   additionally use `sorryAx`, exactly as reported. The extension chooses no witness
   from a postponed existence theorem: its tuple, sign, and restriction are explicit.

3. **Split statement: PASS.** The differential lemma is precisely stability of the
   explicit extension image; it does not restate existence of a section of an
   arbitrary complex map. Its distinct-tuple deletion-sign identity and repeated-pair
   cancellation prove the claimed statement for arbitrary presheaves and families.
   Read its full docstring proof and node, and checked the restriction direction
   against SiteCechComplex.differentialValue. Compared the source formula and
   stability assertion in [Stacks 01FG](https://stacks.math.columbia.edu/tag/01FG)
   with [01FJ](https://stacks.math.columbia.edu/tag/01FJ) and
   [01FK](https://stacks.math.columbia.edu/tag/01FK).
   Independently reran the 6,674 formal-face coefficient tests, then expanded the
   range to cardinalities 0 through 6 and degrees 0 through 4: all 82,179 tuples
   passed, including fully distinct six-entry tuples, nonadjacent equal pairs,
   triple repetitions, and multiple pairs. Empty index types are vacuous because
   tuple lengths are positive; singleton types and degree zero also pass.
   New LeanFinder, Loogle, and Mathlib grep searches used alternating cochains,
   repeated entries, and removeNth cancellation rather than the first reader's
   signed-extension query. The closest result,
   AlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq, assumes an
   alternating multilinear map on a module with a fixed coefficient group. It is
   not a direct replacement for arbitrary ordered indices and varying presheaf
   coefficient groups. Searches of lean/ and the upstream algebraic-geometry
   library found no existing public declaration of this stability assertion.
   Closing the universal sorting/sign calculation is not a short local repair;
   the named source-backed lower hole is retained.

4. **Route and pruning: PASS.** The main proof uses direct signed extension rather
   than an unnecessary preliminary extension by zero. Each import of the new module
   supplies public construction data: scheme, chosen intersections, tuple sorting,
   or permutation sign. The main module's new import is proof-only. The original
   proof_deps contained only def-weil-pbc-site-cech-complex, which is retained, so
   no old dependency is omitted from `No longer needed`. No shorter applicable
   library result was found. The unit sk-thm-picard-pn and its realized record are
   untouched; its existing empty realized placeholders are inherited project state,
   not a bypass introduced here. The alternating-comparison ancestor chain remains.

5. **DAG agreement: PASS.** Diffed the existing node: its only changed fields are
   proof, proof_deps, and proof_origin. These describe the explicit extension,
   degreewise identity, chain-map transport, and cochain-map assembly used in Lean.
   The new node's dependencies are the union of its proof-step uses; its statement
   matches the Lean differential lemma, including ambient variables. It has source,
   complete proof steps, three successful search kinds plus the unavailable service,
   split status, creation record, blueprint ancestry, chapter, unit, and Lean record.

Second reading changed only this report: added independent interface, compilation,
axiom, source, search, edge-case, pruning, and node checks. No Lean proof, statement,
definition, import, or node needed repair. The delivery remains a decomposition:
one original hole closed, one strictly lower hole added, net zero holes, no pruned
modules; no unconditional axiom-free proof of the original theorem is claimed.
