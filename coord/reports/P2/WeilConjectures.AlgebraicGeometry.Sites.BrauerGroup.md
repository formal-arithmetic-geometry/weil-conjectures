## What changed

Replaced the sole sorry in `WeilConjectures.AlgebraicGeometry.Sites.BrauerGroup` by composition of two equivalences through `Field.GaloisUnitsH2`. Its original statement and both existing public imports are unchanged. Added proof-only imports of `Sheaf.FieldTheory.BrauerGaloisComparison` and `Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison`.

The new module `Sheaf.FieldTheory.GaloisUnitsCohomology` constructs the natural action on the discrete separable-closure unit group and uses Mathlib's continuous homogeneous cohomology model. Its data and representation laws are fully proved. The Galois group has the Krull topology; the coefficient group is discrete. Thus this intermediate object uses continuous, rather than abstract, absolute-Galois cohomology.

## Proved and sorry left

`AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalBrauerGroup` is proved from two strictly separate comparison theorems by `Equiv.trans`. Its new node is `lem-sc-field-brauer-comparison`. The existing `IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup` remains proved from this theorem and algebraic Brauer vanishing.

Two sorries remain, each the entire proof of a named public theorem in its own new module:

- `Field.nonempty_equiv_brauerGroup_galoisUnitsH2`, node `lem-sc-brauer-galois-units-comparison`.
- `AlgebraicGeometry.Scheme.nonempty_equiv_galoisUnitsH2_cohomologicalBrauerGroup`, node `lem-sc-etale-galois-units-comparison`.

All four modules compile together through lcompile.py. The target module has no direct sorry; its transitive axioms still include sorryAx from these two comparisons. This is a reduction, not an axiom-free completion.

## No longer needed

None. Both original public imports are used. Both new proof imports are used. The original two-step Galois-cohomology route is retained, so no nodes or modules are pruned. No curve proof dependency is bypassed.

## Where the brief, the DAG or earlier work was wrong

The two nodes found by searching the module name mention the theorem only in their historical lean_audit.open lists; their actual lean.module records are curve modules. Neither supplies a DAG node for the field comparison. The new `lem-sc-field-brauer-comparison` records the source theorem and its proof dependencies without rewriting unrelated curve nodes.

The source theorem's sketch identifies both sides with Galois cohomology, but those comparisons were absent as Lean declarations. The existing `Rep.discreteContinuousCohomologyFunctor` requires a finite coefficient ring, so it cannot encode the integer module of units. Mathlib's `continuousCohomology` already provides the homogeneous continuous-cochain model over the integers; this delivery reuses it. Mathlib's ordinary `groupCohomology.H2` would be the wrong object for an infinite absolute Galois group.

Searches: LeanFinder found only the BrauerGroup definition and degree-one Hilbert 90; Loogle BrauerGroup returned only its definition. LeanSearch returned Internal Server Error. Grep across Mathlib, WeilConjectures and Sheaf found no comparison, and `blueprint_refs.py search 'Brauer Galois'` found no blueprint duplicate. The source is Stacks Project, Tags 03R7, 03QU, 03QV, 04JQ and Section 0DVG.

Edge cases checked in the mathematical statements: separably closed fields have trivial Galois group and degree-two classes vanish; imperfect fields use separable-closure units, since the etale stalk does not see purely inseparable elements; no finite-dimensional hypothesis is imposed on the unit group. Universe u=0 is permitted, and the comparison to the lifted etale cohomology lives across the two universes exactly as the original theorem does.

## New nodes

`def-sc-galois-units-cohomology`: the discrete unit coefficient representation and second continuous Galois cohomology; source Example 03QV (2), Tags 04JP/04JR and Section 0DVG. It reuses Mathlib continuousCohomology and has no sorry.

`lem-sc-brauer-galois-units-comparison`: the central-simple-algebra classification by continuous degree-two classes; source Theorem 03R7. Its docstring and node describe scalar defects, injectivity by matrix Hilbert 90, and surjectivity by crossed products.

`lem-sc-etale-galois-units-comparison`: transport of degree-two cohomology along the stalk equivalence and the continuous-cochain comparison; source Lemmas 04JQ/03QU and Example 03QV (2), Section 0DVG.

`lem-sc-field-brauer-comparison`: the previously unrecorded original field theorem, now proved by composing the preceding two equivalences. The natural-language and Lean routes agree. All three kinds of search are recorded for each new node; LeanSearch's unavailability is explicit.


## Second reading by P2

1. Compared the delivered target module with the read-only repository by diff and the
   declaration parser. Both existing signatures and the existing proof of quasi-algebraic
   Brauer vanishing are byte-for-byte unchanged. Only the comparison proof and two plain
   proof imports change. All other delivered Lean modules are new. No existing definition,
   target statement, or public import changes; no change record is required.
2. Compiled all four modules locally and compiled scratch copies with `#print axioms` for
   both definitions and all four theorems. The definitions use only `propext`,
   `Classical.choice`, and `Quot.sound`. The comparisons and existing theorems use those
   and `sorryAx`, exactly as reported. There are exactly two direct sorries, both whole
   proofs of public named comparison theorems. No forbidden declaration or hollow
   definition occurs. Scratch copies were removed before delivery.
3. Read both split statements and their docstring proofs, and checked their sources.
   Both are true for arbitrary fields: a separably closed field gives a trivial Galois
   group and zero degree-two classes; imperfect fields correctly use separable-closure
   units. The two comparisons are different parts of the original argument, not a
   renamed copy of the target. The discrete coefficient group retains the natural action;
   the group topology is Krull. Compact Hausdorff exponential laws identify Mathlib's
   iterated continuous maps with jointly continuous cochains, and TopModuleCat homology
   has underlying algebraic kernel modulo image. Independent LeanFinder search for
   classification by continuous 2-cocycles, Loogle search for continuousCohomology, grep
   for crossed products and Brauer equivalences, and repository searches found no existing
   comparison to reuse. Closing either comparison requires substantial algebraic or
   cohomological infrastructure, not a short omitted argument.
4. The proof follows the original sketch from the top downward: algebraic Brauer classes
   to continuous Galois H2, then continuous Galois H2 to etale H2. All imports supply names
   in signatures or exposed definitions, except the two correctly plain proof imports.
   No original proof dependency or import is removed. The unit sk-thm-br still follows
   Brauer injection and Tsen; this field comparison supports that route. Its realized
   record currently has empty lists and is not changed by this delivery.
5. Read all four new nodes and the original curve nodes mentioning the theorem in audit
   lists. The new field-comparison node records exactly the two equivalences composed by
   the Lean proof. The intermediate definition and two split comparisons have matching
   Lean records, sources, search records, chapter/unit metadata, and proof dependencies.
   The etale comparison plan retains the existing abelian-sheaf/G-module equivalence
   node. No unrelated existing node is changed.

Changes made in this second reading: corrected every mistaken reference to Example
03QR (2) to Example 03QV (2), in new modules, nodes, and this report. Expanded the
comparison proof sketches and corresponding DAG steps to justify the iterated
continuous-cochain model and the underlying algebraic homology. Expanded the crossed
product sketch to explain finite-Galois factorization of a continuous cocycle, and the
coefficient-action documentation to explain joint continuity via open fixing subgroups.
No Lean statement, definition body, or proof body was changed.

Source checks: [Brauer classification](https://stacks.math.columbia.edu/tag/03R7),
[etale/Galois comparison](https://stacks.math.columbia.edu/tag/03QU),
[multiplicative coefficient example](https://stacks.math.columbia.edu/tag/03QV), and
[continuous cochains](https://stacks.math.columbia.edu/tag/0DVG).
