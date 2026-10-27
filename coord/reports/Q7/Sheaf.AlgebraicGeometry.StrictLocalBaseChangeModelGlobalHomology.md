## What changed

Completed the retirement repair, which starts with zero holes. Withdrew
Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology through deleted.txt.
Preserved its exact original-model statement in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeModelGlobalHomology as
AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_baseChange_modelGlobalHomology.
All binders, universes, hypotheses and the conclusion agree after renaming; this
was checked against the live source signature.

Replaced 5 private helpers and the repeated derived-pasting proof by a direct
transport from the adopted theorem. Compose eA with Spec of the inverse canonical
small-to-full colimit comparison. The existing structural-map compatibility gives
the same bottom morphism; equality elimination before supplying the cartesian
witness transports the adopted conclusion to the original square. There is no
new choice of data and no changed definition.

Updated the existing node's Lean attachment and actual proof dependencies. The
closed-stalk parent still cites that same node, with its unchanged original-model
statement. Its current Lean file is a withdrawn stub, so there is no live call
site to modify. The adopted closed-stalk consumer and all adopted source files
are untouched. No unit statement or realized step is bypassed.

Validation: the replacement compiles in 9.2 seconds with no warnings. Its printed
axioms are exactly propext, Classical.choice and Quot.sound. A temporary full
original-model closed-stalk consumer checks the renamed theorem and the unchanged
hypotheses. It compiles in 5.6 seconds, and its axioms and those of both model
theorems are exactly propext, Classical.choice and Quot.sound. That source is
excluded from the delivery. The delivery tool additionally
runs its required compile, axiom and preflight checks.

## Proved and sorry left

The item's original module has 0 sorry; the delivered replacement has 0 sorry.
Holes closed: none (0 of 0). Holes added: none. Split-off holes: 0.

AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_baseChange_modelGlobalHomology
has a complete new transport proof. The exact original small-model proposition
is preserved, while the adopted
AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_modelGlobalHomology
keeps its distinct strictLocalization interface and its existing complete proof.
The attached source node adds no Lean declaration and no sorry.

## No longer needed

Retired module:
Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology.
Its obsolete colliding declaration and its five private helpers are removed;
the distinct original-model assertion remains available through its existing
node and the new smallModel_ name.

The replacement proof no longer imports any of these old private proof imports:

- Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeGlobalHomology
- WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
- WeilConjectures.SixFunctors.BaseChange.DerivedComparison
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- WeilConjectures.SixFunctors.BaseChange.Square

Some of the adopted modules remain transitively needed by the adopted theorem;
none is deleted and no adopted proof is replaced. The small-model canonical
continuity chain is no longer needed by this model theorem. In its former
proof_deps, lem-weil-pbc-strict-local-base-change-global-homology,
lemma-weil-pbc-derived-exchange-replacement,
lemma-weil-pbc-derived-exchange-coherence,
def-weil-pbc-derived-inverse-image and def-weil-pbc-cartesian-square are no longer
direct proof steps: the transport uses the already proved adopted model theorem
and the existing small/full structural-map comparison instead. Statement
dependencies stay intact, and those nodes remain for every other user that needs
them. The unit route and all source-library declarations are preserved.

## Where the brief, the DAG or earlier work was wrong

This dispatch is a retirement repair from coord/retire-items.tsv, rather than an
unproved theorem: the live source already contains a complete proof and zero
holes. The similarly named adopted theorem is not textually the same proposition:
it uses strictLocalization and strictLocalizationToBase, whereas the item and
its parent node use strictHenselizationScheme and strictHenselizationStructuralMap.
Deleting the assertion or pointing its unchanged Lean record directly at the
adopted signature would lose the required interface. The 2026-10-21 restoration
preserved that interface but also restored the colliding unprefixed name.

The current retirement row's consumer list is historical: downstream.py reports
zero actual direct and transitive importers, and the listed Sheaf closed-stalk
file is an existing withdrawn stub. Its DAG dependency is still real and is
preserved by the renamed theorem. There is no rework/quarantine row for the item.
No target or mathematical statement is weakened.

## New nodes

src-weil-pbc-strict-localization-model-global-homology attaches the exact already
proved adopted strictLocalization theorem, for which no existing node had that
Lean attachment. It records its full signature and the existing complete proof;
it introduces no module or unproved obligation. The original node now uses this
source theorem and lem-weil-pbc-strict-henselization-small-closed-fiber-comparison.

Change record: coord/changes/Q7-retire-model-global-homology.md.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
