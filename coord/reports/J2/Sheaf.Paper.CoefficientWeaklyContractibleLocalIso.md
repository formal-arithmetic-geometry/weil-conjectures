## What changed

Proved `AlgebraicGeometry.Scheme.coefficient_weaklyContractible_local_iso` with its
statement unchanged. A finite affine refinement of the covering sieve gives a
coproduct cover. The stated slice weak-contractibility hypothesis splits that
cover, and the preimages of its components give a finite disjoint refinement in
the coefficient-sized site.

Added `Sheaf.CategoryTheory.RingedDerivedDisjointIso`, proving the general
finite-disjoint-cover gluing theorem for unbounded derived module sheaves.
K-injective representatives let local derived isomorphisms be represented by
homotopy equivalences. The sheaf Hom glues their maps, inverse maps, and inverse
homotopies degreewise. Separatedness verifies all equations. Both proofs include
the empty-cover case without a nonemptiness assumption.

The item's public import and declaration signature are unchanged. All added
proof imports are private. No existing module other than the item was changed.

Both modules compile cleanly through `lcompile.py`: the generic gluing module
in 55.8 seconds and the item in 3.9 seconds, within the 60-second per-file limit.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.coefficient_weaklyContractible_local_iso`.
Also proved the new theorem `CategoryTheory.ringedDerived_disjoint_iso` and all
its private helpers. Holes closed: 1 of 1; holes added: 0; holes remaining in the
delivery: 0. This is a proof, not a decomposition into new unproved obligations.

## No longer needed

The previous planned dependencies
`lem-sfb-wcontractible-etale-constant-models`
(`Sheaf.SixFunctors.WeaklyContractibleEtaleConstantModels`) and
`lem-weil-proetale-weakly-etale-localization`
(`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`) are not used by this
proof. It works directly with actual coefficient-sized ringed slices and glues
on a disjoint refinement of U, so it needs neither fixed etale constant models
nor an extra weakly etale localization equivalence.

The planned dependency `sk-def-pe-weak-contractible` is also unnecessary here:
the proof applies the statement's explicit slice-terminal surjectivity
hypothesis directly. The existing module originally had only its public
statement import, so none of these unused planned dependencies was imported in
the first place. No source-library declaration or module is withdrawn, and
these nodes may still be needed by other parents.

## Where the brief, the DAG or earlier work was wrong

The old proof plan assigned the derived gluing step to an etale constant-model
lemma whose signature does not cover arbitrary objects of the ringed derived
category in this statement. Instead, the delivery proves the required general
disjoint-cover result. Pulling the coproduct partition back along its section
first also avoids constructing a derived isomorphism on the coproduct and then
transporting it along the section. The unit's statement and realized route are
preserved.

## New nodes

`lem-sfb-ringed-derived-disjoint-iso` records the proved general gluing theorem
in `Sheaf.CategoryTheory.RingedDerivedDisjointIso`. It assumes a finite disjoint
cover, with no weak-contractibility or scheme hypothesis. Its proof is fully
formalized, including lifting local isomorphisms through the K-injective
homotopy-category localization and gluing both inverse homotopies.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
