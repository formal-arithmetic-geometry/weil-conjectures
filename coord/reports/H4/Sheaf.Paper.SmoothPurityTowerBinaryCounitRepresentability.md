## What changed

The original theorem binary_counit_representability is proved by a substantive decomposition
along its existing eight-step argument. The actual Lean proof constructs the unique overlap
isomorphism from the two restricted representing bijections, proves the two inverse identities
by injectivity, proves uniqueness, and applies Mathlib's additive-group five lemma to the
exact signed Hom rows. The private central_bijective helper packages each row arrow with
Preadditive.leftComp and each vertical map with rightComp composed with F.mapAddHom; all four
squares follow from map_comp and associativity, including the connecting and negative shifted
arrows. Functoriality also proves the separately requested naturality clause for every arrow.

Three strictly partial geometric steps remain in separate modules: restriction of one local
representing pair; lift and signed factorization of two compatible counits; and local
transpose equations with exact rows and outer bijections. Neither lift nor comparison
asserts global representability. The comparison has a specified lift as an input and supplies
only the four outer bijections; the central one is actually proved in the item.

The seventeen old helper definitions move unchanged to
SmoothPurityTowerBinaryCounitPredicates to avoid cycles between the item and its proof steps.
The item publicly reexports them. Main statement and definition-block byte comparisons both
pass. Existing callers need no adaptation. The change record is
coord/changes/H4-binary-counit-definition-relocation.md.

## Proved and sorry left

Closed the original named hole:
AlgebraicGeometry.ProEtale.SpTowerBinaryCounit.binary_counit_representability.
There are zero holes in the item and zero in the shared definition module.

Added three named holes, each exactly a theorem proof `by sorry`:

- AlgebraicGeometry.ProEtale.SpTowerBinaryCounit.restricted_representing_pair
  (lem-sp-tower-restricted-representing-pair).
- AlgebraicGeometry.ProEtale.SpTowerBinaryCounit.compatible_counit_lift
  (lem-sp-tower-compatible-counit-lift).
- AlgebraicGeometry.ProEtale.SpTowerBinaryCounit.open_hom_comparison
  (lem-sp-tower-open-hom-comparison).

This is a decomposition, not an outright closure of the original mathematics: one upper
hole closed and three strictly partial holes added, net minus two before any unrelated
closure changes. The private generic uniqueness and central five-lemma helpers are complete.
No data definition contains sorry or selects an arbitrary witness from an unproved theorem.

## No longer needed

Removed direct proof imports from the item: CoefficientTowerShriekCalculus,
SequenceSiteOpenExtension, RingedToposBinaryDescent, Mathlib.CategoryTheory.Triangulated.
Pretriangulated, Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four, and
Mathlib.Algebra.Exact.Basic. The generic definitions retain their public Mathlib dependencies
in the shared definition module. The geometric steps retain the calculus, open localization,
and ringed-topos descent proof plan; their corresponding DAG nodes are still needed.
The item uses Mathlib.Algebra.FiveLemma directly instead of the categorical abelian-groups
construction from DiagramLemmas.Four. The five-lemma node remains the mathematical dependency;
its additive-group specialization is used directly.

No module or DAG node is withdrawn or globally pruned. The binary ctf fibre declaration is
not called to construct G: the original statement quantifies over every compatible G and its
restriction isomorphisms, and retains its existing interface dependency. No unit route is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The stated calculus theorem supplies some coherent b,o,q existentially; it is not directly
an API of preservation and all nested-open equations for the arbitrary b,o,q parameters of
the item. The open-localization and ringed-topos binary descent declarations use different
site presentations, so applying them requires the genuine sequence-site transport step.
These are geometric proof obligations, not missing declarations or unsupported dependencies;
the three new nodes isolate them faithfully using the existing stated results.

The original naturality conjunct is elementary functoriality and does not need a separate
statement or hole. The generic additive five lemma was found by the required searches and
avoids the larger categorical encoding. No false statement or changed hypothesis was found.
The empty-open, equal-open, zero-object, first positive coefficient level and arbitrary-shift
edge cases remain valid: the split steps keep the existing exact operations and signs, and
the generic uniqueness/five-lemma proofs have no nonzero or nonempty assumption.

## New nodes

lem-sp-tower-restricted-representing-pair: the parent's step 1 for one local pair and every
smaller open, with precisely the existing nested restricted counit. Its source and full
argument are in the theorem docstring and node.

lem-sp-tower-compatible-counit-lift: the parent's steps 3 and 4 for a supplied compatible
overlap isomorphism and gluing, producing a lift, signed cancellation and every-lift
factorization; no representability assertion.

lem-sp-tower-open-hom-comparison: the parent's steps 3,5,6 for a supplied lift, giving the
three local transpose equations, the signed distinguished triangles, goodness, the two exact
rows and four outer bijections; central bijectivity is omitted and proved in the parent.

def-sp-tower-binary-open-counit-data: ownership for the fourteen existing geometric
helper definitions relocated verbatim. The existing def-sp-tower-binary-counit-predicates
continues to own the other three definitions and is reattached to the same new module.
The parent theorem node keeps its exact statement and updates its proof and proof dependencies.

Required semantic/type/grep searches and blueprint duplicate searches are recorded on all
new nodes. Change record: coord/changes/H4-binary-counit-definition-relocation.md.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
