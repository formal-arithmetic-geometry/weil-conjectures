## What changed

Proved `AlgebraicGeometry.finite_pushforward_set_stalk_map_bijective_of_finite`
in `Sheaf.AlgebraicGeometry.FinitePushforwardSetStalkAux`, keeping its signature unchanged.
The existing abelian-coefficient stalk formula cannot be instantiated with `Type`, but its
split-neighbourhood geometry and section-product isomorphism are coefficient-independent.
The proof uses those existing declarations with Mathlib's preservation of finite limits
by filtered colimits of sets. It checks the composite on colimit coprojections and product
projections, using the pointed piece inclusion and `colimit.w`, so the resulting bijection
is exactly the restriction map in the statement.

Added proof-only imports of `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`
and `Mathlib.CategoryTheory.Limits.Types.Products`. Kept the existing public import and
all existing visibility. Updated the item's node to the implemented route. Recorded three
already proved source-library tools as nodes, with no new Lean declaration or module.

The module compiles without warnings through `lcompile.py`. The empty geometric fibre is
covered by the same categorical product and colimit comparisons: no nonempty-index argument
is used. No target or intermediate signature, definition, or existing docstring changed.
The item does not realize a unit statement or unit proof step in `dag/units/sk-thm-iff.json`;
this change is below that unit and preserves its route.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.finite_pushforward_set_stalk_map_bijective_of_finite`
(node `lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective`).
No `sorry` remains in the item. Added 0 holes and split off 0 theorems.
All three newly recorded geometric tools are existing proved declarations; they introduce
no assumptions or unproved data constructions.

## No longer needed

Removed these eight proof-only imports from this item:

- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`
- `Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk`
- `Sheaf.Paper.StrictHenselizationFunctoriality`
- `Sheaf.RingTheory.FiniteOverHenselianLocalProduct`
- `WeilConjectures.Mathlib.RingTheory.Henselian`

The old direct proof dependency `lem-weil-pbc-sets-finite-pushforward-set-stalk`
is not used. Its id does not exist in this checkout. In particular, this item no longer
needs the parent's strict-henselization proof route or its auxiliary nodes:
`lem-weil-pbc-sets-etale-inverse-image-composition-units`,
`lem-weil-pbc-sets-etale-inverse-image-stalk-germ`,
`lem-weil-pbc-sets-pushforward-stalk-strict-henselization`,
`def-weil-pbc-strict-henselization-limit`,
`lem-weil-pbc-sets-strictly-henselian-open-sections-stalk`,
`lem-weil-pbc-strict-henselization-functoriality`,
`lem-weil-pbc-finite-over-henselian-local-product`,
`def-weil-pbc-henselian-terminology`,
`lem-weil-pbc-sepclosed-finite-extension-unique-embedding`,
`lem-weil-pbc-spec-clopen-idempotent`, and the other geometric assembly dependencies
of `lem-weil-pbc-sets-finite-pushforward-stalk`. This is pruning from this proof;
other targets may independently need them. The preserved public source import can still
transitively expose some proved ring-theoretic infrastructure.

## Where the brief, the DAG or earlier work was wrong

The auxiliary node's only old proof dependency has no node in this checkout and its
single step did not supply the promised detailed plan. The original parent node
`lem-weil-pbc-sets-finite-pushforward-stalk` does contain the ten-step strict-henselization
plan. A shorter argument is available in the existing library: the geometric statements
in `Finite.SplitExists`, `Finite.PieceSection`, and `Finite.PieceSections` are already
proved and work with sheaves of sets, although the assembled stalk formula in
`SixFunctors.Finite.Stalk` has abelian coefficient hypotheses. Replacing that coefficient
step with Mathlib's filtered-colimit finite-limit theorem resolves the item directly.

LeanSearch returned HTTP 500 for both new-tool searches; this is recorded as unavailable,
not as evidence of no match. Loogle and Mathlib grep were run. Repository and blueprint
searches found the existing abelian stalk formula and finite splitting statement, but
no nodes for the three exact source-library tools recorded below.

## New nodes

`lem-weil-pbc-finite-split-neighbourhoods-cofinal` records the already proved
`AlgebraicGeometry.Scheme.Hom.SplitNbhd.initial_forget` and `isCofiltered`
in `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitExists`.

`lem-weil-pbc-finite-split-pieces-cofinal` records the already proved
`AlgebraicGeometry.Scheme.Hom.SplitNbhd.initial_pieceFunctor`
in `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceSection`.

`lem-weil-pbc-finite-split-sections-product` records the already constructed
`AlgebraicGeometry.Scheme.Hom.SplitNbhd.sectionsIsoPi`
in `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceSections`.

These are reusable tools underlying the source library's existing proof, not new
remaining proof obligations. There are no change records or forced adaptations.

## Second reading by H2

1. Compared the delivered module with the repository version. The theorem signature and all
   existing declarations are byte-for-byte unchanged; only the proof and proof-only imports
   differ. Verdict: pass.

2. Compiled the module with `lcompile.py`; it is clean, contains no `sorry`, and introduces no
   forbidden declarations or hollow definitions. Verdict: pass.

3. Checked the three recorded source-library tools and the target statement against existing
   declarations. They are already proved declarations, and no split-off theorem or duplicate
   statement was added. The finite-limit argument covers an empty fibre. Verdict: pass.

4. Reviewed the proof from the target downward. It uses the split-neighbourhood and piece
   comparison isomorphisms, then Mathlib's finite-limit preservation, and removes the old
   strict-henselization route and its proof-only imports. Verdict: pass.

5. Checked the target node's proof, dependencies, and origin against the Lean proof, and checked
   that the unit route remains recorded in `sk-thm-iff.json`. Verdict: pass.

Changed only the proof, proof-only imports, corresponding node route/dependencies, and this
second-reading report; no statement, definition, or unit statement was changed.
