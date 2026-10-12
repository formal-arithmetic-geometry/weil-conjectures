## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian` with a complete Lean
reduction. The statement, binders, universes and all existing public imports are unchanged.

The proof forms `V ×_U S` for each integral Noetherian affine immersion `S → U`, proves
constructibility of the abelian pullback using a new finite-stalk pullback statement,
and applies the existing `exists_dense_open_lisse_finite_directImage`. It explicitly
constructs the finite exchange isomorphism, compares abelian inverse image with set
inverse image using `etaleInverseImageAlgebraicStructures`, forgets the exchange
isomorphism, and pulls it back to the dense open. A proved private helper
`lisse_of_iso` transports both the trivializing cover and finiteness of geometric stalks.
A second new statement performs the Noetherian induction that converts these dense
lisse restrictions into a finite stratification.

Added proof imports for the two new modules and
`Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`. Removed the direct proof
import of `WeilConjectures.ConstructibleSheaf.Pullback`. Updated the item's node's
`proof`, `proof_deps` and `proof_origin` to describe this exact reduction. No definition
or existing statement changed, and no change record is needed.

Validation: all three sandbox modules compile cleanly through `lcompile.py --all`,
without warnings. Checked node dependency ids, equality of proof dependencies with the
union of step dependencies, and the 100-character Lean line limit. The delivery dry run
provides the final local/server compilation and preflight checks.

## Proved and sorry left

The original declaration
`AlgebraicGeometry.Scheme.isConstructibleEtaleSheafOfSets_lowerStar_of_isNoetherian`
now has a complete proof with no sorry in its body: 1 of the item's 1 sorries reduced.
The private helper `AlgebraicGeometry.Scheme.lisse_of_iso` is also fully proved.
This is a reduction, not a claim that every transitive dependency is sorry-free.

Exactly two new public theorem sorries remain in the delivery:

- `AlgebraicGeometry.Scheme.isConstructibleEtaleSheafOfSets_upperStar`, in
  `Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback`, node
  `lem-weil-pbc-constructible-etale-set-pullback`.
- `AlgebraicGeometry.Scheme.isConstructibleEtaleSheafOfSets_of_generic_lisse`, in
  `Sheaf.AlgebraicGeometry.ConstructibleEtaleNoetherianCriterion`, node
  `lem-weil-pbc-constructible-etale-noetherian-criterion`.

Each is one theorem in its own new module, with proof exactly `:= by sorry`, its source,
and a complete natural-language proof in its docstring and node. The first statement
contains no finite direct image. The second concerns an arbitrary set sheaf and assumes
only generic lissity on integral affine immersions; it contains no morphism h or abelian
source E. The main proof supplies its hypothesis by base change and the existing generic
finite-direct-image statement, rather than handing the original conclusion to a renamed
copy.

Edge cases checked mathematically: an empty source/base and an empty pulled-back stratum
use the empty partition and vacuous conditions; identity pullback keeps a stratification;
arbitrary non-Noetherian pullback still has constructible preimage strata and unchanged
geometric stalks. For the criterion, the empty closed subset has the empty partition,
reducible subsets are handled by finitely many proper components, and a dense open in a
nonempty affine open of a reduced irreducible closed subset is dense in that closed
subset. Nonreduced bases are covered by composing the reduced stratum immersions directly
into the original base. No finite-dimensional hypothesis is used.

Existing imported sorries, including the generic finite-pushforward theorem and the
inverse-image algebraic-structures theorem, were not edited and retain their own nodes.

## No longer needed

Removed the item's direct proof import `WeilConjectures.ConstructibleSheaf.Pullback`.
The old direct dependency `prop-constructible-pullback` is replaced by the specialized
finite-stalk pullback node. Its abelian `IsConstructibleSheaf.upperStar` declaration
is not applied by this proof.

That module is still imported by the new pullback module for the existing
`Stratification.pullback` declaration, node `lemma-constructible-pullback-stratification`.
It therefore cannot be claimed as a globally pruned module.

The original finite-components node and constructible-subset node remain needed through
the new Noetherian criterion, so they are relocated dependencies, not pruned work.
`Sheaf.AlgebraicGeometry.GenericFinitePushforward` and
`WeilConjectures.SixFunctors.Finite.BaseChange` remain explicitly used. No other original
import or original node is eliminated, and no entire module is claimed to have left the
targets' closure.

## Where the brief, the DAG or earlier work was wrong

The old proof plan says Noetherianity makes the constructibility notions agree.
Noetherianity addresses constructibility of locally closed strata, but does not identify
finite geometric underlying sets with finitely generated abelian stalks. The source
`IsConstructibleSheaf`/`IsFiniteSheaf` interface uses finite generation. The new pullback
statement explicitly preserves the finite geometric set stalks in this item's interface;
no false comparison or weakening is used.

Also examined `Sheaf.AlgebraicGeometry.ConstructibleClosedGenericCriterion` and its node
`lem-weil-pbc-constructible-closed-generic-criterion`. That theorem is for module sheaves
with finite-generation constructibility and assumes generic lissity on every closed
subscheme, whereas the present generic theorem only gives it over integral affine bases.
It is therefore not an exact instance for our arbitrary set sheaf and finite set stalks.
The new criterion isolates the corresponding set-sheaf induction with the exact testing
hypothesis the main proof supplies.

The original unit `sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps`.
Its record is unchanged. The finite base-change, generic-lisse-open and Noetherian
induction route of the item's original three steps is retained. The algebraic-structures
comparison and the set inverse-image composition, restriction, constant and stalk
statements are tools from other units; they supply compatibility of the actual set and
abelian inverse-image constructions, not a replacement of the unit's route.

The blueprint and Stacks source files named by the original node are absent in this
machine's read-only literature mirror. The supplied node's complete numbered proof is
the source for the split, and the new proof origins are marked `agent`. Stacks Tags 095R
and 095E were also read online. Tag 095R proves a more general finite finitely presented
result by a different splitting/descent argument, so its proof should not itself be
labelled the Noetherian induction written in the blueprint. No source text was downloaded
into the repository.

## New nodes

`lem-weil-pbc-constructible-etale-set-pullback` states preservation of constructibility
of the underlying set sheaf by abelian inverse image along an arbitrary scheme morphism.
It serves step 1 of the original node. Its proof pulls back the stratification, the etale
trivializations, and the finite geometric stalks, then uses the algebraic-structures
comparison. Existing source declarations were searched by predicate, type and concept;
Mathlib searches were run with LeanFinder, grep and LeanSearch (the last returned HTTP
500, recorded as unavailable). The finite-generation source pullback is recorded as
related rather than falsely marked an exact match.

`lem-weil-pbc-constructible-etale-noetherian-criterion` states constructibility of an
arbitrary set sheaf from dense lisse restrictions on every integral Noetherian affine
locally closed subscheme. It serves steps 2 and 3 of the original node. Its proof covers
the empty, reducible and integral cases of well-founded induction on closed subsets,
then constructs the finite constructible stratification. The related existing module
criterion was inspected and does not have this signature. LeanFinder and grep found
only adjacent constructible-subset results; LeanSearch was run and recorded unavailable.
Both nodes cite existing dependencies, carry their exact Lean signatures and have the
same chapter and unit as the item. No new node is the original finite-pushforward
statement under another name.

## Second reading by G2

1. Compared the delivered item module with the repository version. The theorem signature
   and all existing declarations are byte-for-byte unchanged; only proof imports, the
   proof, and the documented DAG route differ.
2. Compiled all three sandbox modules with `lcompile.py --all`. They compile without
   errors or warnings. The item theorem is proved; the two explicitly split public
   theorems are the only remaining sorries, each documented and represented by a node.
   No definitions contain sorry, and the proof introduces no forbidden axioms or
   declarations. Scratch copies with `#print axioms` for all three public theorems
   report exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, the last
   from the documented open dependencies.
3. Checked both split statements against the edge cases described above and against the
   available library declarations. They are strictly intermediate reductions: the
   pullback result has no Noetherian or finite-direct-image hypothesis, and the criterion
   has only the generic-lisse testing hypothesis. Neither duplicates the item's target.
   Repeated LeanFinder searches using "finite partition", "irreducible closed subsets",
   and "finite locally constant" rather than the first reader's theorem wording;
   results were topological component and profinite locally constant function lemmas,
   not these sheaf statements. Repository `rg` searches found the module-sheaf
   pullback and closed-generic criterion, whose finite-generation predicates differ.
   Both splits require substantial set-sheaf compatibility or stratification work;
   neither has a short direct proof using an existing exact library result.
4. Followed the proof downward from the target: finite pullback constructibility,
   generic finite pushforward, finite exchange and algebraic-structures comparison,
   then the Noetherian criterion. The old pullback import is removed from the item and
   retained where the new pullback module needs its stratification operation.
5. Compared the DAG proof steps and dependencies with the Lean proof and checked the
   unit record. The unit route remains the finite base-change, generic-lisse-open and
   Noetherian-induction route; the new nodes realize only intermediate set-sheaf steps.
   All dependency ids resolve, each `proof_deps` equals its proof-step dependency
   union, and the existing node changes only `proof`, `proof_deps`, `proof_origin`.

Changed during second reading: added this review record; no Lean statements or proofs
required repair after compilation and signature comparison.
