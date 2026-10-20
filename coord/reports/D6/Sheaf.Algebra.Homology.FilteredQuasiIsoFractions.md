## What changed

The statement and public imports of `Sheaf.Algebra.Homology.FilteredQuasiIsoFractions`
are unchanged. Its proof now constructs `HasRightCalculusOfFractions` from identities,
composition, an Ore square, and cancellation, and pairs it with two-out-of-three.
Three new modules isolate those mathematical parts. All four modules compile cleanly
with the project compile server (`lcompile.py --all`). No existing definition or
statement was changed, and no consumer adaptation or change record is required.

`FilteredQuasiIsoTwoOutOfThree` is completely proved. It restricts filtered homotopies
to steps, descends their components through the degreewise cokernels, and constructs
associated-graded functors on the homotopy quotient with values in the ordinary
derived category. The representative-based definition of a filtered quasi-isomorphism
is equivalent to being sent to an isomorphism in every grade. Identities and all three
two-out-of-three implications follow from this equivalence.

The two remaining, separate source results are the right MS2 (Ore) and right MS3
(cancellation) assertions from the original proof. Each has its own module, node,
unchanged relevant hypotheses, and a complete cone-construction proof in words. These
are separate parts of the fraction theorem, not renamings of its whole conclusion.
The parent node now records precisely the Lean combination of those parts.

## Proved and sorry left

Original item: one hole, `CochainComplex.finiteFilteredModuleQuasiIso_fractions`.
That declaration now has a complete proof from the two separate fraction axioms and
the proved identity and two-out-of-three results. Its module has zero remaining holes.
This is a decomposition, not a claim to have proved the whole fraction theorem without
new assumptions: one original hole is replaced by two named holes (net minus one).

The following new declarations are fully proved, with no `sorry`:

- `CochainComplex.finiteFilteredModuleQuasiIso_id`.
- `CochainComplex.finiteFilteredModuleQuasiIso_twoOutOfThree`.

Exactly two holes are added and remain in the delivery:

- `CochainComplex.finiteFilteredModuleQuasiIso_rightOre`, in
  `Sheaf.Algebra.Homology.FilteredQuasiIsoRightOre`, node
  `lem-kun-filtered-quasi-isomorphism-right-ore`.
- `CochainComplex.finiteFilteredModuleQuasiIso_rightCancellation`, in
  `Sheaf.Algebra.Homology.FilteredQuasiIsoRightCancellation`, node
  `lem-kun-filtered-quasi-isomorphism-right-cancellation`.

The constructions have been checked on zero inputs and vanishing graded pieces.
Neither assertion requires cochain boundedness: all finite bounds concern only the
filtration index. The Ore denominator is projection from the filtered homotopy fibre
of `(f,-s)`; the cancellation denominator is projection from the filtered homotopy fibre
of the map to the shifted cone of `s`. The signs in both homotopy identities are
specified in the docstrings and nodes. No arbitrary data are chosen from these holed
existence statements in a definition: the main theorem only eliminates them in Prop.

## No longer needed

The parent proof no longer imports these modules directly:

- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`.

The three new proof-only imports replace them. The subquotient and filtration
definitions remain available through the existing public homotopy-category import;
the two-out-of-three proof uses those definitions directly. The ordinary cone
criterion `lem-pur-quasi-iso-cone-acyclic` is unnecessary for the parent's class
assembly and the proved two-out-of-three result, but is still needed in the two
remaining cone proofs. Consequently none of the original mathematical dependency
nodes is claimed globally pruned, and no module is withdrawn. The public imports of
the parent are preserved to avoid changing the interface seen by consumers.

Searches in Mathlib and both library roots found ordinary unfiltered fractions and
triangulated-category fraction theorems; none supplies the filtered homotopy category
and graded cone compatibility needed here. Thus neither ordinary fractions nor
bounded-cochain specializations are imported as a purported shortcut.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was found. The original proof treats filtered
cone/shift/sum compatibility and the cycle calculation as elementary steps; their
stated dependencies expose the definitions and the ordinary cone criterion, rather
than a ready-made filtered Ore or cancellation interface. Those two separate source
axioms are now explicit remaining nodes. The graded homotopy descent and all the
multiplicative/two-out-of-three glue have been implemented rather than assumed.
The unit route is preserved: its `realized` list imposes no additional intermediate
statement that this reduction bypasses.

## New nodes

`lem-kun-filtered-quasi-isomorphism-fractions-two-out-of-three` records the proved
identity and two-out-of-three assertions in
`Sheaf.Algebra.Homology.FilteredQuasiIsoTwoOutOfThree`. Its Lean proof includes the
restriction and cokernel descent of homotopies, quotient functor descent, and the
representative-independent isomorphism criterion.

`lem-kun-filtered-quasi-isomorphism-right-ore` records the right MS2 assertion in
`Sheaf.Algebra.Homology.FilteredQuasiIsoRightOre`. It retains the original source's
homotopy-fibre construction, graded acyclic kernel argument, and global finite bounds.

`lem-kun-filtered-quasi-isomorphism-right-cancellation` records the right MS3 assertion
in `Sheaf.Algebra.Homology.FilteredQuasiIsoRightCancellation`. It retains the original
source's two successive shifted cone constructions, filtered null-homotopy, and
graded acyclic kernel argument. Both new holed assertions are strictly parts of the
original conclusion and are used by its complete Lean proof.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
