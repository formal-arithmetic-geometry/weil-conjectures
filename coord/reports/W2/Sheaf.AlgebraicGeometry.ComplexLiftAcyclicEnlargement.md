## What changed

Proved `AlgebraicGeometry.exists_complex_lift_acyclic_enlargement` without changing
its signature or existing public imports. Added three proof-only imports:
`Sheaf.AlgebraicGeometry.ComplexLiftConeProperties`,
`Sheaf.AlgebraicGeometry.ComplexLiftStrictMap`, and
`Sheaf.AlgebraicGeometry.ComplexLiftConeCokernel`.
Also added the proof-only upstream import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective`
to reuse `CochainComplex.IsKProjective.exists_Q_map_eq`.
All three new modules are fully proved. The actual mapping cone and the actual
cokernel sequence are used, with no arbitrary objects chosen from unproved existence.
Private helpers prove the chain representative of a derived isomorphism,
projectivity after extension of scalars, boundedness of a cokernel, and surjectivity
of the quotient adjunction unit. The DAG follows this route.

The strict lifting argument is shorter than the plan: reduced K is K-projective,
so the map into the acyclic cone has a null-homotopy. Lift that homotopy termwise
through the quotient unit by projectivity and take its boundary. No homotopy-category
lift through a quasi-isomorphism or correction of a preliminary chain map is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_complex_lift_acyclic_enlargement`
(`lem-sc-complex-lift-acyclic-enlargement`). Added zero holes; none remain.

Also proved the new declarations:
- `AlgebraicGeometry.complex_lift_cone_properties`
  (`lem-sc-complex-lift-cone-properties`).
- `AlgebraicGeometry.exists_complex_lift_strict_map`
  (`lem-sc-complex-lift-strict-map`).
- `AlgebraicGeometry.complex_lift_cone_cokernel`
  (`lem-sc-complex-lift-cone-cokernel`).

All four modules compile locally without errors or warnings. The delivery dry run
checks the axioms of every declaration against the three permitted axioms.

## No longer needed

Replaced the direct proof-only import
`Mathlib.Algebra.Homology.DerivedCategory.KProjective` with the upstream
representative module, which publicly imports it. No proof-dependency node is removed. The existing
`lem-pc-ring-derived-map-representative` remains needed to obtain the initial
quasi-isomorphism. The proved upstream derived-map representative module is additionally used;
its proof uses the existing Mathlib representative dependency.
The old plan's lift through a surjective quasi-isomorphism and correcting-homotopy
step are unnecessary; the direct null-homotopy argument replaces them. The new
strict-map lemma needs no acyclicity or boundedness hypothesis on A.
No unit statement or realized step is bypassed, and no module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The cone-cokernel part called elementary in the old DAG
requires cokernel preservation, comparison isomorphisms, and transport of splittings;
these have now all been written in Lean. The Stacks TeX source is absent on this
machine, so Tag 0BCA was read at https://stacks.math.columbia.edu/tag/0BCA.
LeanSearch returned Internal Server Error; successful LeanFinder, Loogle and source
searches are recorded in searches.jsonl. Blueprint searches for acyclic cone,
strict lift, mapping cone, cokernel cone, and lift map projective found no duplicates.

Edge cases: the cone-properties lemma uses a maximum bound, including zero
complexes; the strict-map proof only uses acyclicity of C; the cone-cokernel lemma
works for any delta, without requiring a quasi-isomorphism. Its proof never assumes
that the original map f is injective. The quotient-unit proof also works for I=0
and I=R. No signatures or definitions of existing modules are changed.

## New nodes

`lem-sc-complex-lift-cone-properties` records the fully proved cone bound,
acyclicity and reduced class terms in `ComplexLiftConeProperties.lean`.

`lem-sc-complex-lift-strict-map` records the fully proved strict lifting statement
in `ComplexLiftStrictMap.lean`, with A arbitrary and C acyclic.

`lem-sc-complex-lift-cone-cokernel` records the fully proved reduced cokernel
isomorphism and degreewise splitting in `ComplexLiftConeCokernel.lean`.
There are no interface change records or forced adaptations.

## Second reading by W2

1. Compared the existing module against the repository with diff: its sole public
   theorem signature, docstring, universes and public imports are byte for byte
   unchanged. Only proof bodies, private helpers and proof-only imports change.
   The other three modules and nodes are new; no definitions or interfaces of
   existing declarations change, so no change record is required. PASS.
2. Read all four proofs and compiled each locally in import order, without
   errors or warnings. No sorry or forbidden declaration occurs in the delivered
   Lean files. The cone and cokernel are actual Mathlib constructions; witnesses
   and homotopies are obtained only from proved results. Explicit axiom checks
   and the delivery probe check the permitted axioms. PASS.
3. No statements are split off with sorry: the three new public intermediate
   lemmas are completely proved, strictly parts of the argument, and have source
   docstrings and matching nodes. Checked the cone bound including zero complexes;
   the quotient unit argument for I=0 and I=R; the strict lift with A arbitrary;
   and the cokernel comparison for arbitrary delta, without injectivity over R.
   Independent LeanFinder and Loogle queries and source searches found the APIs
   used and no exact replacement for these three lemmas. PASS.
4. Read top downward and checked the old dependencies and unit realized record.
   The existing representative dependency remains used by the upstream lemma's
   proof. The unit has no realized nodes here and its route is unchanged.
   No modules are claimed pruned. Found the upstream proved
   `CochainComplex.IsKProjective.exists_Q_map_eq` and replaced the duplicate
   homotopy-category representative argument with it, removing the redundant
   direct Mathlib proof import. All new imports needed only for proofs are plain
   imports; mapping-cone imports in new signatures are public. PASS.
5. Compared each node's statement, proof steps, dependency union, proof origin,
   Lean record, source, searches, creation and blueprint fields with its module.
   New nodes supply the required fields and have no open proof. Updated the
   original node's first proof step to record reuse of the upstream representative
   lemma. No statement or unit metadata is changed. PASS.

Second reading changed only the derived-map helper proof, its proof-only imports,
the corresponding DAG proof text, and this report. One original hole closed,
zero holes added; the three new intermediate lemmas are fully proved.
