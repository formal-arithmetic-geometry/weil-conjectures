## What changed

Replaced the sole sorry in `Sheaf.CategoryTheory.RightDerivedCanonicalSingleUnitShift`
with a compiling composition of the two steps of its existing proof plan. All existing
statements, definitions, universes and visibility are unchanged. Added proof-only imports
of `RightDerivedSingleUnitShiftTransport` and `MappedSingleCyclesShiftComparison`.

The new `mappedSingle_cycles_shift_comparison` is proved in Lean: cancel the degree-zero
single homology comparison; apply the generic single homology shift equation; identify
the mapped-single isomorphism as Q of a complex map; apply quotient homology naturality;
expand the degree-n single homology comparison; use cycles naturality and the coefficient
formula for `singleMapHomologicalComplex`; cancel the coefficient isomorphism.

Two strictly smaller equations remain in their own modules. The unit transport equation
has no cycles projection or homology quotient. The generic single homology shift equation
concerns one category and one object, with no additive functor, derived unit, or enough
injectives. Neither is the original statement renamed or repackaged. No arbitrary data
are chosen from an unproved existence theorem. The source cycles lemma does not assume
enough injectives or a derived category on B.

Updated the original node's proof route and added a node for each new module. Compiled
all four modules in dependency order, with no compiler errors or warnings. Edge cases
were checked against the explicit constructions: degree zero uses the shift unit laws;
for a zero object the same maps apply; the shift signs act only on zero outer terms of
the single-complex short complex. The generic shift comparison is stated for every integer.

## Proved and sorry left

Closed `CategoryTheory.Functor.rightDerivedFunctorPlusUnit_canonical_single_shift`
(node `lem-pc-right-derived-canonical-single-unit-shift`): 1 of 1 original holes closed.
This is a decomposition, not a sorry-free proof: two lower holes were added.

Also proved the new `CategoryTheory.Functor.mappedSingle_cycles_shift_comparison`
(node `lem-pc-mapped-single-cycles-shift-comparison`), from the generic shift equation
and the existing quotient homology and single-complex lemmas.

Every sorry left in the delivery:

- `CategoryTheory.Functor.rightDerivedPlusSingleUnit_shift_transport`, in
  `Sheaf.CategoryTheory.RightDerivedSingleUnitShiftTransport`, node
  `lem-pc-right-derived-single-unit-shift-transport`.
- `singleFunctor_homology_shift_comparison`, in
  `Sheaf.CategoryTheory.SingleHomologyShiftComparison`, node
  `lem-pc-single-homology-shift-comparison`.

The item's module and `MappedSingleCyclesShiftComparison` contain no sorry. Each remaining
hole is exactly the whole proof of a named public theorem, with its source and proof in
words. Existing dependencies' holes were not changed.

## No longer needed

No existing module or import is pruned. The original public import of
`Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison` is needed for the
statement's unit homology definition. Both added proof imports are used. The generic
shift module imports only the single homology comparison interface it needs; the mapped
cycles module imports the quotient homology interface and the single homology interface.

Removed `def-weil-abstract-derived-category` as a direct proof dependency of the original
node: its only proof is now composition of the two named calculations and unfolding the
unit homology definition. It remains a statement dependency and a dependency of the lower
calculations; it is not an unreached node or pruned module. The classical augmentation
comparison theorem is not invoked anywhere in this proof, although the original module
is still required for its definitions. No unit statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the original hole untouched. The existing DAG names the general
derived category and the degree-zero unit definition, but those declarations do not
state the specialized shift transport equations. The delivery supplies the missing
intermediate statements and proves the cycles calculation rather than stopping there.
LeanSearch was unavailable; LeanFinder, Loogle, grep, and source inspection were used.

The original node's `blueprint.from.node` points to its created parent rather than the
imported blueprint ancestor. The new nodes follow the parent's recorded imported ancestor
`lem-pc-euler-characteristic-well-defined`, with the intervening nodes listed in `via`.
The original blueprint fields are outside this delivery's owned fields and were not edited.

## New nodes

`lem-pc-right-derived-single-unit-shift-transport`: the unit's naturality and CommShift
calculation after applying homology, before precomposing any cycles projection. New module
`Sheaf.CategoryTheory.RightDerivedSingleUnitShiftTransport`; one named sorry.

`lem-pc-single-homology-shift-comparison`: generic compatibility of the canonical
single-object homology isomorphism with transport to degree zero. New module
`Sheaf.CategoryTheory.SingleHomologyShiftComparison`; one named sorry.

`lem-pc-mapped-single-cycles-shift-comparison`: the source-side calculation from cycles of
the mapped single complex to degree-zero single homology. New module
`Sheaf.CategoryTheory.MappedSingleCyclesShiftComparison`; proved from the preceding generic
shift comparison and existing homology naturality lemmas.

All three nodes inherit the original chapter and unit and preserve the parent's two-step
route. The unit's `realized` record is unchanged and has no entries naming this parent
or its dependencies. No change record or forced adaptation is needed.

## Second reading by E1

1. Compared the existing module and node against the repository with `diff -u`.
   Verdict: the existing declaration, universes, hypotheses, conclusion, definitions,
   docstring and visibility are unchanged byte for byte. Only its proof and two plain
   proof imports changed. No interface change or change record is required.
2. Independently compiled all four delivered modules in dependency order using
   `lcompile.py --all`, and compiled scratch copies with `#print axioms` for all four
   theorems. Verdict: no errors; the only axioms are `propext`, `Classical.choice`,
   `Quot.sound` and `sorryAx`. The only two literal sorries are the complete proofs
   of the two public named theorems listed above. No forbidden declarations or
   hollow definitions occur; no data are chosen from an unproved existence theorem.
3. Read both open equations, their docstrings and nodes against the actual
   single-functor, short-complex shift, homology shift and derived-unit CommShift
   constructions. Verdict: both are true, needed components of the original
   argument. The generic comparison has arbitrary integer degree and only one
   category/object; the unit equation removes the cycles calculation. Neither
   simply renames the parent theorem. Checked degree zero, zero objects and the
   sign at odd degree: the shift short-complex middle map is the coefficient
   identification, while its signed outer maps act on zero terms. Independent
   LeanFinder (stalk-complex homology transport), Loogle and grep searches, including
   the upstream DerivedCategory and Sheaf sources, found constituent comparisons
   but no existing specialized equation. Closing either remaining hole requires
   further quotient/shift coherence calculations, rather than a short missing
   lemma application.
4. Read the parent proof from its first rewrite through the cycles calculation and
   final unfolding. Verdict: it follows the original two calculations without
   invoking the classical augmentation comparison. Every import is used by a
   signature or proof. The sole old proof dependency removed directly from the
   parent is listed under No longer needed; it remains below the new lemmas.
   No module is pruned. Inspected `dag/units/sk-thm-picard-rr.json`: its realized
   entries are empty and unchanged, and no chapter or unit step is bypassed.
5. Matched all four node records to the declarations, actual proof steps and
   imports, including the union of each proof's uses and its proof_deps, source,
   proof_origin, searches, creation, blueprint, chapter, unit and Lean records.
   Verdict: the nodes describe the delivered proofs and the two remaining holes.

Second-reading changes: clarified the report's claim about the unit's realized
record; appended this review. No Lean proof or interface repair was necessary.
The result remains a decomposition: one original hole closed, two holes added,
so the local hole-count net is minus one, with no pruned modules.
