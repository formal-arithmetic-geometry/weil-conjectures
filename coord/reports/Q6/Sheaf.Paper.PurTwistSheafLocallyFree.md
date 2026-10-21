## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.purTwistIntegralAction_existsUnique`
by a complete proof from a separate coefficient calculation and the fully proved
`CategoryTheory.tensorPushoutAction_existsUnique`.

The generic theorem constructs the tensor action through endomorphism rings, proves
restriction compatibility by tensor induction, descends through the actual abelian
sheafification unit, checks both scalar normalizations, and proves uniqueness on local
pure tensors. It works on arbitrary sites with independent site and coefficient
universes; it assumes no finite freeness or nonzero section ring.

Extracted 23 existing coefficient declarations, unchanged, into
`Sheaf.Paper.PurTwistCoefficientRings`, publicly reexported by their original owner.
This avoids a circular import: the coefficient-only comparison must precede the
integral action and line. The only proof edit in the extracted block supplies the
constant-sheaf adjunction explicitly in its private quotient-epimorphism proof.
No public definition body or signature changes.

`Sheaf.Paper.PurTwistCoefficientTensor` isolates the genuinely separate coefficient
calculation of original proof step 6. Its statement concerns only the four concrete
ring sheaves, their specified scalar inclusions and their sectionwise ring tensor;
it mentions neither the root limit nor an action on the integral Tate line.
The map `purTwistCoefficientTensorMap` is an actual algebraic tensor lift,
constructed from the already proved scalar square. The new lemma asserts only
its bijectivity. The action proof obtains a ring equivalence using
`RingEquiv.ofBijective`; its pure-tensor normalization is definitional. No
arbitrary witness is chosen from mere existence.

The coefficient module also proves six private parts of its remaining argument:
`integral_basis`, `coefficient_section_basis`, `finiteFreeCompletionTensor`,
`prime_uniformizer_power`, `coefficient_filtrations`, and `cofinal_power_subsequence`.
They establish finite integral bases and compatible section bases, the algebraic
completion/tensor comparison without Noetherian section-ring hypotheses, and
cofinality with its normalized inverse-limit projection formula. The remaining
public coefficient hole is the identification of the actual finite-quotient diagrams
and their limits with those algebraic completions, including the specified scalar map.

Compiled all four delivery modules together. Also compiled the three unchanged
consumers `CoefficientTwistsDetailed`, `IntegralLineTensorCompleteness` and
`SignedLineTensorEquivalence` against them. All were under the per-file limit.
The generic action theorem and the six coefficient helper axiom audits are exactly
`propext`, `Classical.choice`,
`Quot.sound`. The integral action audit includes `sorryAx` through the explicitly
reported open coefficient lemma. The existing `purTwistZlAction_existsUnique`
remains proved and was not counted as work of this delivery.

## Proved and sorry left

Original item: two holes. Closed one upper hole and added one separate coefficient
hole. This is a decomposition with net zero holes closed, not a complete proof of
the integral action from the three permitted axioms.

Closed:

- `AlgebraicGeometry.Scheme.purTwistIntegralAction_existsUnique`
  (`lem-pur-twist-sheaf-locally-free`): its combining proof is complete.

New, fully proved:

- `CategoryTheory.tensorPushoutAction_existsUnique`
  (`lem-pur-tensor-pushout-action`): no holes and only the permitted axioms.

Every remaining hole in the packet:

- `AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free`
  (`lem-pur-twist-sheaf-locally-free`): the original four-part theorem is untouched.
- `AlgebraicGeometry.Scheme.purTwistCoefficientTensor`
  (`lem-pur-twist-coefficient-tensor`): the one added hole; its proof is exactly
  `by sorry`, with its source and full finite-basis/cofinal-limit argument in the
  docstring and node. It is strictly the scalar-ring calculation needed before
  constructing an action on arbitrary balanced module tensors. Its conclusion is
  bijectivity of the explicitly constructed canonical ring homomorphism.

There are two holes in total: one in the item and one in the new coefficient module.
There are no holes in definitions, in private helpers, or in the extracted coefficient
constructions.

## No longer needed

The integral action proof needs no extra geometry or derived-category hypotheses:
the completed scalar comparison and generic tensor/sheafification argument suffice.
No nodes or modules are withdrawn. The other dependencies in the unfinished main
theorem's proof plan are retained; the current absence of an import is not a claim
that its future proof will not need that dependency. No source-library declaration
is removed, weakened or replaced by a hole.

Removed the following proof imports from the owning item. Its proved declarations
compile with the two new proof imports. The existing unit-route imports
`ProEtaleSiteComparison` and `IntrinsicFiniteTorsionConstructibility` are retained
for the unfinished main theorem. The extracted coefficient module
retains the ring-limit and constant-to-completion imports it actually uses.

- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
- `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Mathlib.Algebra.Category.Ring.Limits`
- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Paper.IntegralDerivedReduction`
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`
- `Sheaf.Paper.DerivedComplete`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The scalar comparison was only a prose part of step 6;
there was no separate coefficient-only declaration usable before the action in its
owning module. Importing a proof of that step without extracting the coefficient
constructions would create an import cycle. The extraction changes no mathematical
object or target meaning.

A direct use of Mathlib's finite-Noetherian completion tensor theorem is insufficient:
constant-sheaf section rings need not be Noetherian. One must use the finite basis
and identify the specified quotient limits, including the cofinal relation between
l-power and uniformizer-power ideals. The existing constant finite-free section-basis
theorem supplies the discrete part. The private helpers prove the finite-basis, algebraic-completion and cofinality
parts; the public coefficient proof still needs the concrete quotient-diagram
identifications. It does not assume Noetherian site section rings.
The proof plan and docstring state the calculation explicitly, including empty
objects and zero section rings.

## New nodes

`def-pur-twist-coefficient-rings` records the unchanged discrete/completed scalar
square in its acyclic module. Its Lean attachment lists all 23 moved declarations;
they were removed from the old module's attachment and remain publicly reexported.

`lem-pur-tensor-pushout-action` records the complete generic construction and
uniqueness proof on a sheafified balanced tensor. It is a genuine module-theoretic
part of step 6, independent of p-adic arithmetic and of Tate roots.

`lem-pur-twist-coefficient-tensor` records the remaining coefficient-only
finite-basis/completion calculation. The main node's step 6 now calls this lemma
and the generic action theorem. Its other proof steps and the unit route are retained.
All three new nodes carry actual three-kind Mathlib search records.

Change record: `coord/changes/Q6-tate-coefficient-extraction.md`.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
