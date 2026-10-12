## What changed

Closed the proof of
`AlgebraicGeometry.Scheme.nonempty_embedding_cohomologicalBrauerGroup_galoisUnitsH2`
in `Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding`, preserving its signature and
its public imports. The proof chooses the canonical algebraic closure of K, obtains
the existing abelian geometric stalk equivalence and action formula, identifies the
units coefficient representation, and composes the existing additive Ext-to-derived
terminal evaluation comparison with the general continuous-cohomology comparison.
The final embedding is the underlying embedding of this composite equivalence.

Added three modules, one public theorem per module:

- `Sheaf.AlgebraicGeometry.EtaleFieldSectionsInvariants`: a proved natural isomorphism
  between terminal evaluation and Galois invariants. Its 150-line proof uses
  `fieldSections_stalkInvariants` on the underlying sheaf of sets, proves that its
  action agrees with the action specified by i on every germ, specializes to the
  bottom intermediate field, and packages the additive germ bijections naturally.
- `Sheaf.AlgebraicGeometry.EtaleUnitsStalkRepresentation`: the remaining degree-zero
  equivariant integer-linear identification of the units stalk with separable-closure
  units; no cohomology is mentioned in this obligation.
- `Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison`: the remaining
  general homological comparison, conditional on an equivalence of abelian categories,
  a natural invariants/sections isomorphism, and an equivariant coefficient equivalence.
  It applies to arbitrary discrete integer modules and permits a coefficient universe
  change. Its representation universe is at least the group universe, ensuring that
  continuous coinduction stays in the same category; it mentions neither fields nor etale sheaves nor the Brauer group.

The new proof imports are private. Added the profinite-Galois import to supply compactness.
All four modules compile together cleanly through lcompile.py, in import order. No
existing definitions or statements were changed. The main node now records the actual
composition and its five proof dependencies. The unit sk-thm-br has no realized nodes
among the removed dependencies; its route is unchanged.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.nonempty_embedding_cohomologicalBrauerGroup_galoisUnitsH2`
(node `lem-sc-etale-units-h2-reverse-embedding`). The item's module has no sorry left.
Also proved the new theorem
`AlgebraicGeometry.Scheme.nonempty_iso_etaleFieldSections_invariants`
(node `lem-sc-etale-field-sections-invariants`). It uses already stated lemmas whose
own proofs are separate work items.

Added exactly two public theorem holes, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.exists_etaleUnits_stalk_linearEquiv`
  (node `lem-sc-etale-units-stalk-representation`).
- `Rep.nonempty_equiv_rightDerived_continuousCohomology`
  (node `lem-sc-discrete-invariants-continuous-comparison`).

This is a decomposition, not a complete axiom-free proof of the comparison: one
existing hole closed and two holes added, for a raw delivery net of minus one.
There are no holes in definitions, private declarations, or unfinished proof bodies.
All objects used by the main proof are obtained inside a propositional proof;
there is no arbitrary-witness-based definition.

Edge cases checked in the statements and proof sketches: a separably closed field
has trivial Galois action and the degree-zero comparison is ordinary evaluation;
imperfect positive-characteristic fields use separable-closure units, not all units
of the algebraic closure; the zero representation is permitted; degree zero of the
generic theorem is invariants; the units equivalence and generic comparison explicitly
allow the u+1/u coefficient universe difference. The generic comparison requires the representation universe to contain the group
universe, as needed for the locally constant coinduced object. The proved sections theorem assumes
Omega algebraic over K to use the existing fieldSections_stalkInvariants interface;
this is satisfied by the canonical algebraic closure chosen in the main proof.

## No longer needed

No imports from the original module were removed, and no original dependency modules
are pruned. The units cohomology and Brauer definitions remain necessary for the
statement. Their nodes are statement dependencies rather than independent proof steps
in the updated node.

The proof does not import the circular alternatives
`Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison`,
`Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison`, or
`Sheaf.FieldTheory.BrauerGaloisComparison`. It needs no explicit two-cocycle quotient or
Schroeder-Bernstein argument. These were not original imports, so they are not claimed
as pruned modules.

Removed a redundant AlgebraicClosure proof import added during development, since the
existing public imports already provide that construction.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt left the original theorem unchanged. Its saved searches
were inspected and supplemented by actual Mathlib, source-library and blueprint
searches. LeanSearch returned an Internal Server Error and is recorded as unavailable,
not as a negative mathematical verdict. The actual services' queries are in searches.jsonl.

The existing degree-two equivalence cannot prove this item: import_direction.py reports
that it already reaches this module. Importing it would close a cycle. The supplied
one-step proof plan also has no stated integer-coefficient derived-invariants comparison:
`continuousCochains_derived_invariants` and `discreteContinuousCohomologyFunctor` require
`Finite A`, which cannot be instantiated with A = Z. The general remaining comparison
states the required integer case without changing any existing interface.

The existing sections/stalk and Galois-point-action lemmas, and the derived-evaluation
and universal-delta-functor lemmas, are used as generic tools from their existing
units. No other unit route is substituted for sk-thm-br.

The existing fieldSections_stalkInvariants theorem already supplies the sections/stalk
bijection, so that part has been proved from it rather than left as another hole.
The natural-isomorphism formulation is new glue, with the underlying canonical action
explicitly checked, not a duplicate unproved sections theorem.

Read Stacks etale-cohomology.tex from the available read-only literature copy:
lemma-global-sections-point, lemma-equivalence-abelian-sheaves-point,
lemma-compare-cohomology-point, example-sheaves-point (2), and
section-continuous-group-cohomology. The global-sections lemma is Tag 04JM;
Tag 03QW describes the action on stalks. The generic theorem's insertion contraction
and homogeneous change of variables are explicitly written out in its docstring and
node; the source's final profinite comparison itself leaves a future-reference gap.

## New nodes

`lem-sc-etale-field-sections-invariants` records the proved natural sections/invariants
comparison. Its Lean proof depends on the existing sections/stalk, Galois-point-action,
and automorphism-extension theorems. It is distinct from the set-valued sections theorem
because it identifies the additive functors for the particular supplied E and i.

`lem-sc-etale-units-stalk-representation` records the remaining equivariant units
coefficient identification. Its proof evaluates germs on finite separable field
neighbourhoods, constructs the inverse germs from a unit and its inverse, and checks
the Galois action by the supplied action-on-germs formula.

`lem-sc-discrete-invariants-continuous-comparison` records the remaining generic
homological calculation: transport injective resolutions, establish effaceability of
continuous cochains using locally constant coinduction, identify universal delta-functors,
and change homogeneous/inhomogeneous coordinates and coefficient universes. The
finite-ring comparison in the current library is not used as if it applied to Z.

Each new node has its source, complete proof sketch, three actual kinds of Mathlib
search (including the service outage), canonical blueprint ancestry, and exact Lean
signature. No change records or forced adaptations are needed.

## Second reading by K3

1. **Statements and signatures.** Compared each delivered module with the repository
version. The existing target statement is unchanged; the three added theorem statements
are new declarations and the node JSON signatures match them. Verdict: unchanged target
and consistent new interfaces.

2. **Proof and axioms.** Compiled all four modules with `lcompile.py --all`; the item
has no remaining sorry, while the two intentionally split comparison theorems each have
exactly `:= by sorry`. No definitions contain sorry, and no forbidden declarations were
introduced. Verdict: clean compilation and permitted split holes.

3. **Truth and strength of split statements.** Read the docstrings, checked the degree-zero,
separably closed, imperfect-field, and zero-coefficient edge cases recorded above, and
verified that each split theorem is strictly lower-level than the item. Searches found no
existing declaration duplicating any of the three statements. Verdict: the split statements
are needed, true as stated, and not restatements of the target.

4. **Shortest route and pruning.** The main proof uses the existing abelian equivalence,
the sections/invariants and stalk/unit comparisons, and the existing derived evaluation
comparison. The generic comparison is isolated because the finite-ring theorem cannot
instantiate integer coefficients. Imports are retained only when used; no original proof
dependency was incorrectly pruned. Verdict: route and import choices are justified.

5. **DAG and unit route.** Updated proof steps, proof dependencies, and proof origin in
the target node follow the Lean composition. New node metadata, declarations, and blueprint
ancestry agree with the modules. The unit `sk-thm-br` route remains represented by its
existing realized steps. Verdict: DAG and unit records agree.

Changed during second reading: added this review section only; no Lean statements,
definitions, or proof bodies required repair.
