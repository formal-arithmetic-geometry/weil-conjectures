## What changed

Replaced the sole sorry in
`CategoryTheory.CondensedBar.OrderedCup.internal_bar_ordered_cup` by a full Lean
assembly of the declared homogeneous resolution, character lifts, character-roof
cup theorem, and three smaller interface lemmas. The assembly chooses the universal
sign before every coefficient, group, model and character input, proves it is ±1
and is 1 in degrees zero and one, takes the actual product cocycle from Lifts,
checks its generalized-section formula at the unit, and combines the two signed
arrow equalities using bilinearity of composition.

Factored the fourteen fixed definitions verbatim into the new
`Sheaf.CategoryTheory.InternalBarOrderedCupCore`, publicly reexported by the item,
to avoid a circular import with the statement-only bridge modules. No statement,
definition body, instance or original public import is changed. Updated the item's
proof route and Lean declaration inventory and added the four matching DAG nodes.
Change record: `coord/changes/G1-internal-bar-ordered-cup-definitions.md`.

Validation: all five modules compiled through lcompile.py. The final item compiled
without warnings in 23.8 seconds, with profiling and debugging options removed.
The core and the three bridge modules passed the all-files compile in 39.8--45.6
seconds per file. There are no existing Lean importers of the item to adapt.
The theorem signature, fourteen extracted definition bodies and original public
imports were checked against the current source; all are unchanged.

## Proved and sorry left

Original hole closed, by a decomposition:
`CategoryTheory.CondensedBar.OrderedCup.internal_bar_ordered_cup`
(`lem-sfb-internal-bar-ordered-cup`). One original hole, zero holes left in the
item. Three holes added, each a strict portion of the original argument:

- `CategoryTheory.CondensedBar.OrderedCup.exists_equivariant_character_lifts`
  (`lem-sfb-internal-bar-equivariant-character-lifts`): equivariant chain maps and
  their augmented components, with neither cup nor total comparison.
- `CategoryTheory.CondensedBar.OrderedCup.small_hom_bar_roof_comparison`
  (`lem-sfb-internal-bar-small-hom-comparison`): generic homogeneous cocycles and
  their normalized total comparison, with no character or cup hypothesis.
- `CategoryTheory.CondensedBar.OrderedCup.ordered_character_cup_eq`
  (`lem-sfb-internal-bar-cup-bracketing`): agreement of the two fixed cup
  bracketings, with neither homogeneous bar nor injective resolution data.

Each remaining proof is exactly `by sorry`, in its own public theorem module,
with a source, complete proof in words and node. This is a decomposition,
not a net reduction in sorry count: one hole closed and three added. The new
core and the private sign lemmas have no holes. No data are chosen from a new
unproved existence theorem inside any definition.

## No longer needed

No mathematical dependency or existing public import is pruned. The four original
proof dependencies remain used, either directly by the assembly or through the
new bridges. In particular the internal-bar-roof-adjunction dependency is retained
by the small-Hom comparison; it is not withdrawn. All DAG parents and the unit
route remain intact. No module is deleted. The direct proof edge to roof adjunction is replaced by
the small-Hom bridge, which retains roof adjunction as its proof dependency.

## Where the brief, the DAG or earlier work was wrong

The natural-language assembly is sound, but the Lean interfaces do not directly
match: character lifts use underlying internal-module complexes, roof/cup uses
equivariant complexes; roof adjunction quantifies over a compatible Model in the
larger Hom universe while the item allows every specified compatible bar and uses
the smaller localization; the roof/cup left fold differs definitionally from the
item's right-associated tensor formula. The three bridges isolate exactly these
unformalized identifications rather than replacing the item by an equivalent
existence assertion.

The original theorem docstring's last step says epsilon_q=s_q T_q; the current
reviewed DAG already includes the missing (-1)^q. The written proof uses
s_q (-1)^q T_q, so epsilon_1=(-1)(-1)=1. Existing declaration docstrings were
preserved, and this discrepancy is recorded here explicitly.

Edge cases checked in the new statements and their proof explanations: empty
list, one character, zero ring, trivial group, characteristic two and every
profinite base change. No projectivity of homogeneous terms, acyclicity of the
underived bar, or invertibility of the row-zero map is introduced.

## New nodes

`def-sfb-internal-bar-ordered-cup-core` attaches the fourteen unchanged fixed
constructions to their new independent module. It creates no new mathematical
notion and supplies no unproved data.

`lem-sfb-internal-bar-equivariant-character-lifts` states the passage from the
componentwise equivariant underlying Lifts to equivariant shifted complexes,
including exact augmentation and the ordered augmented-component equality. Its
`augmentedRoofComponent` is an actual composite of the supplied maps, not a
choice from any existence theorem.

`lem-sfb-internal-bar-small-hom-comparison` states the generic normalized roof
comparison after transporting compatible models and derived localizations.

`lem-sfb-internal-bar-cup-bracketing` states the coherence identifying the
left-fold cup with the fixed right-associated shifted-source cup.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
