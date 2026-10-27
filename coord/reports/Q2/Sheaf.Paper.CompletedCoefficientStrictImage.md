## What changed

Replaced the hole in
`WeilConjectures.CompletedCoefficientPushforward.strictImage_exists` with a complete
Lean assembly from an ordinary strict-system comparison and one acyclicity assertion.
The original theorem signature and `StrictImageData` are unchanged.

The assembly transfers Grothendieck abelianness to the actual `CoefficientSystem`
category, constructs its additive direct image's normalized total right derived
functor with the existing `totalDerivedData`, and applies the proved generic
`derivedCoefficientComparison`. It then proves the required `Square.normalization`
by composing that theorem's unit equation with the two exact factor isomorphisms
and cancelling their inverses. This calculation is proved in the generic private
`normalizedSquare_exists` helper, so kernel checking does not repeatedly expand the
concrete coefficient categories. It retains the supplied `towerImage` and all ordinary
section identities.

Added `CompletedCoefficientOrdinaryStrictImage`, whose real structure records only
ordinary functors and natural isomorphisms, and
`CompletedCoefficientSystemRestrictionAcyclic`, whose theorem concerns only the
invertibility of a supplied derived unit on restricted K-injective complexes. The
new statements are independent parts of the argument: the former contains no derived
data; the latter constructs no system pushforward or comparison square. Neither
repackages the full original existence statement.

All new imports in the item are proof imports. No existing module besides the item
is changed. The DAG now records the actual derived assembly and the two remaining
ordinary/acyclicity arguments.

Validation: all three modules compiled individually through `lcompile.py`: the
ordinary module in 23.0 s, the acyclicity module in 14.7 s, and the final item in
15.0 s, with no compiler warnings in the final sources. Profiling identified
repeated kernel checking of the concrete normalization proof as the earlier
bottleneck; the generic private helper removes it. All profiling options have
been removed. A source check confirms that the original theorem signature and
the entire `StrictImageData` declaration are byte-for-byte unchanged, all Lean
lines fit within 100 characters, and the updated dependency graph is acyclic.

## Proved and sorry left

Decomposition, not an unconditional proof or net hole reduction:

- Removed the original hole in
  `WeilConjectures.CompletedCoefficientPushforward.strictImage_exists`
  (`lem-pur-completed-coefficient-strict-image`). Its Lean proof is complete and its
  signature is unchanged.
- Added one hole in
  `WeilConjectures.CompletedCoefficientPushforward.ordinaryStrictImage_exists`
  (`lem-pur-completed-coefficient-ordinary-strict-image`). It asks only for the
  ordinary additive system functor, finite evaluation isomorphisms, and ordinary
  completed-tower comparison, with identity sections.
- Added one hole in
  `WeilConjectures.CompletedCoefficientPushforward.systemRestriction_push_acyclic`
  (`lem-pur-completed-coefficient-system-restriction-acyclic`). It asserts only
  acyclicity for tower direct image after source system restriction.

Thus one old hole is removed and two strictly smaller holes remain. There are no
holes in definitions or private helpers, and no hole remains in the item module.
The private proof of Grothendieck abelianness is also complete.

## No longer needed

No existing module is withdrawn and no public import is removed. The sole original
public import, `Sheaf.Paper.CompletedCoefficientPushforwardModels`, is retained.
The full theorem `SheafOfModules.coefficientSystemDerivedComparison` is no longer a
direct proof dependency of the item: only its ordinary construction is relevant to
the ordinary leaf, through `coefficientSystemOrdinaryImage_exists`. Its module is
still publicly imported by the unchanged models, so this is not a claim to have
pruned that module from the library.

The item uses the proved generic `derivedCoefficientComparison` helper owned by
`lem-pur-diagram-ring-restriction-pushforward`, rather than instantiating that node's
entire small-site theorem directly. The general ringed-topos composition theorem
remains needed for the acyclicity leaf, but is not invoked again by the parent.
No inverse-limit comparison, tower evaluation comparison, boundedness, regularity,
completeness, or normalization of the input systems is used by this assembly.

## Where the brief, the DAG or earlier work was wrong

The original node's prose correctly describes the mathematical route, but its
stated general dependencies do not directly express the transport from the concrete
`SystemRestrictionData` and coefficient presentation to the small ringed sequence
site. The new leaves isolate this ordinary transport and its separate acyclicity
consequence. The derived comparison and universal-unit normalization themselves
already have a complete generic proof and have now been implemented in the parent.

Edge cases checked mathematically before stating the leaves: identity scheme maps,
the zero complex, level zero (the first positive quotient), arbitrary noncartesian
transitions, and independent site/coefficient universes. Exact restriction need not
preserve K-injectives; the acyclicity statement deliberately makes no such claim.
The ordinary construction imposes no derived or limit hypotheses. The unit route
and target statements are unchanged.

## New nodes

`def-pur-completed-coefficient-ordinary-strict-image-data` records the ordinary
fields extracted from `StrictImageData`, with no derived fields. Its data are actual
structure fields, never `sorry` or a choice from an unproved mere-existence theorem.

`lem-pur-completed-coefficient-ordinary-strict-image` is the ordinary levelwise
pushforward construction and its section-normalized transport. Source: Zheng,
Construction 4.1; Stacks 03DA and 0D6E. Its docstring gives the construction on
objects, transitions and morphisms, and the generator and naturality checks.

`lem-pur-completed-coefficient-system-restriction-acyclic` is the acyclicity step
of Stacks 0D6E for restriction along the completed projection diagram followed by
tower direct image. Its docstring describes the sequence-site realization and the
cancellation of the normalized composition units, followed by uniqueness for the
supplied derived model.

Searches: LeanSearch returned ordinary pushforward/restriction APIs; LeanFinder
returned scalar-restriction formulas and unrelated local-cohomology diagrams;
Loogle did not recognize the local `rightDerivedUnique` name. Local Mathlib,
WeilConjectures and Sheaf searches found the generic derived comparison and derived
image construction, which the parent reuses, but no completed-presentation instance
of either remaining obligation. The searches are recorded in the new nodes.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
