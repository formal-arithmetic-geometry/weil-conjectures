## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.adicResidue_stalk_tower_family`, preserving
its signature. The proof transports the completed complex through the constant-completion
equivalence, identifies its residue, applies `adic_constructible_finite_reductions`, and
uses the resulting finite etale quotient system. It builds every algebraic tower field
explicitly: the scalar extensions and adjunctions are the canonical existing ones, and
the transitions are adjoint transposes of the step isomorphisms. Normalization follows
from the inverse hom-equivalence identity.

Added `Sheaf.Paper.LisseCoefficientConstructible`. Its theorem proves the conversion
between the slice-module definition of finite local constancy and the fixed-scalar
constructibility interface. The proof compares the constant constructions using the
actual sheafification unit, transports local models to fixed scalars, and uses the
one-stratum stratification on each affine open. No hole is added by this conversion.

Added `Sheaf.Paper.AdicEtaleStalkLevels` for the remaining geometric step, about a supplied
finite etale quotient system. Its hypotheses and conclusion contain no completed
complex, completeness, or reconstruction. It returns algebraic levels and step
isomorphisms; the original theorem supplies the tower adjunctions, transitions,
normalization, and comparison with the actual local reductions of M.

The original module also proves a private scalar-extension/slice comparison for arbitrary
complexes: take a K-flat resolution, restrict it to the slice, and compose the two
universal derived-extension comparisons with the ordinary change-of-scalars/slice
isomorphism. The latter is an existing proved private helper from
`AdicPerfectModelCompleteReduction`, accessed by a proof-only `import all`. Its main
perfect-model theorem is not applied.

All imports added to the existing module are proof imports. No existing public
signature, definition, target, source-library declaration, or unit route changes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.adicResidue_stalk_tower_family`
(node `lem-sfb-adic-residue-stalk-tower-family`).

Proved `AlgebraicGeometry.Scheme.lisseCoefficient_constructible`
(node `lem-sfb-lisse-coefficient-constructible`) and the private slice/scalar comparison.

Added one hole, exactly the whole named theorem
`AlgebraicGeometry.Scheme.adicEtale_stalk_levels`
(node `lem-sfb-adic-etale-stalk-levels`). There are no other sorries in this packet.
The original module has zero holes. One original hole closed and one smaller hole added
is a decomposition, with net hole count zero; it is not claimed as a net proof gain.
Existing imported declarations that still have holes are used as the stage permits.

## No longer needed

No existing import was removed: the item originally had only its statement import.
The revised proof does not restrict M to connected affine charts before applying the
finite-reduction theorem. It therefore removes these direct proof dependencies and the
original node's step about transporting the quotient Roos completion triangle:

- `lem-weil-derived-countable-products-core`;
- `lem-weil-proetale-countable-products-exact`;
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`.

These nodes may remain needed by other modules, including the existing completion API;
this packet withdraws no module and claims no global pruning for them. The geometric
dependencies (Noetherian charts, nilpotent lissity, connected perfect constancy, exact
stalks, tensor pullback, localization and affine weakly contractible covering) remain
needed by the new finite-etale geometric node. The ordinary derived-change-of-rings
route is replaced at the combining step by the existing canonical module-derived
adjunctions (`def-sfb-module-derived-scalar-comparisons`). No finite-quotient-set
perfect-tower lemma is used: A/J^n is not assumed to be a finite set.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and is not disputed. The original plan's second
step repeated the finite-reduction construction after restricting a completed complex.
It is unnecessary: perform the construction globally, then restrict only the finite
complexes. This avoids any additional argument about local preservation of completion.

The lisse and constructible coefficient APIs use different presentations of the same
local models. The original proof plan treated their conversion as immediate. The new
proved module supplies the sheafification and slice comparisons explicitly, including
the empty-affine edge case. The cohomological boundedness input does not order its two
bounds; replacing the lower bound c by min(c,d) gives the ordered interval required by
the constructibility API without strengthening a hypothesis.

## New nodes

`lem-sfb-lisse-coefficient-constructible`: proved finite-local-constancy to constructibility
conversion, including the fixed-scalar/constant-sheaf comparison. It uses the existing
finite-local-system pullback theorem. No new unproved statement is hidden in a definition.

`lem-sfb-adic-etale-stalk-levels`: the finite-etale geometric step of Stacks Tag 09C6.
Its complete proof in words retains the original geometric route. Unlike the assigned
statement, it starts with finite quotient complexes and asks for only their algebraic
levels and step isomorphisms. Completion transport, creation of those finite complexes,
actual slice reduction comparison, and tower assembly are proved in the original module.
The assigned node's proof and dependencies now record that division. No change record
is needed because no existing statement or definition changes.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
