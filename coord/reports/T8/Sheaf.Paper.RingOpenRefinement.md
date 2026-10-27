## What changed

The original signature of `exists_ring_open_refinement` and both existing word definitions
are unchanged. The theorem now constructs the natural isomorphism from a specified ambient
map, proves its literal open-transpose normalization, and proves shift compatibility of the
actual proper/open component word. Coefficient composition is proved by constant-section
coherence at finite stages and `completedPull_comp` at integral stages.

`Sheaf.Paper.RefinementOpenRestriction` defines the natural restriction transformation and
its inverse-transpose open map. It proves the normalization by the adjunction Hom equivalence,
and proves shifts of the inverse transpose and both geometric compositors. Restriction
naturality, invertibility and shifts are extracted from the lower geometric theorem.
`Sheaf.Paper.RingOpenMapInvertibility` isolates pointwise invertibility on finite-Tor inputs.
The adjunction calculation is proved generically in the categorical variables and then
specialized; the new map definitions are irreducible to keep elaboration small.
The restriction transformation stores the original restriction formula directly as its component;
the lower geometric theorem supplies naturality, invertibility and shifts of precisely those
components. The definition stores the component formula itself, and only its proof field uses
that theorem. No transformation is selected as definition data from an existential statement.
The parent obtains the natural isomorphism with `asIso` after whiskering with the inclusion.
The proper/open word is proved equal to a composite of whiskered isomorphisms and
associators, so its inherited shifts follow from the individual factors.

Validation: all three modules compiled with `lcompile.py`. The final parent style warning
was corrected using the compiler recommendation; `deliver3.py` performs the final compile
and preflight again.

This is a decomposition with two geometric obligations, not a completed geometric proof.
The supplied unit route is retained. No existing interface or target is changed.

## Proved and sorry left

Original holes: one, `WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_open_refinement`
(node `lem-sf-ring-open-refinement`). Its proof body is now complete.

Added holes: two, each the entire proof of its named public theorem:

- `WeilConjectures.PurCompactSupport.exists_refinementRestriction`
  (`lem-sf-refinement-open-restriction`): the canonical counit restriction to the clopen
  section is a natural invertible map compatible with shifts. Its literal components determine
  the map uniquely. It has arbitrary ring-sheaf coefficients and no finite-Tor condition;
  it does not assert invertibility of the ambient open map.
- `WeilConjectures.ConstructibleExceptionalCoefficients.ringOpenMap_isIso`
  (`lem-sf-ring-open-map-invertibility`): a component of the explicitly constructed open map
  is invertible on a finite-Tor input. It asserts neither a natural-isomorphism choice nor
  shifts, normalization, or the proper pushforward comparison.

Thus one upper hole is replaced by two strictly smaller geometric steps; net holes +1.
The open-transpose normalization and its shift lemma, and both geometric compositor shift
lemmas, have complete proofs. Naturality and shifts of restriction are part of the lower step.
Every inverse in a definition is of a specified map proved invertible, so the theorem determines it uniquely;
no arbitrary witness of an unproved mere existence statement is chosen.

## No longer needed

No existing public import is removed. The parent now imports the canonical-map invertibility
module privately, and its proof uses the public constant-section composition theorem through
`import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`.

The parent's original direct proof dependencies are routed as follows:
`lem-sf-exceptional-finite-operations`, `prop-compactification-coherence-detailed`,
`lem-sp-refinement-coefficient-mate`, `lem-sf-integral-compactification-system-realization`, and
`lem-sf-exceptional-system-transport` remain in the proof plan of the pointwise geometric
invertibility step. They are not globally pruned or proved here.

`lem-pur-diagram-open-clopen-shift-models` / `Sheaf.Paper.DiagramOpenClopenShiftModels` is not
needed on this proof route: the ambient open map is built directly from canonical ordinary
adjunctions. Its shifts follow from exact localization and the canonical right-derived
adjunction, without totalizer shift models. This does not claim the module has no other users.

## Where the brief, the DAG or earlier work was wrong

The integral `PurCompactSupport.refinementProperOpen_existsUnique` API requires X and Y
separated over the base field. The assigned statement deliberately has only relative
separatedness of f, so that theorem cannot be applied with these hypotheses.

The rework table contains an old quarantine row mentioning a false-tail import. The current
item source is present and was copied as supplied; no quarantine archive is deleted and no
empty replacement or withdrawal is attempted. The delivery changes only this item's proof,
new modules and their nodes, and the item's proof-route fields.

## New nodes

`lem-sf-refinement-open-restriction` records the arbitrary-coefficient clopen restriction
calculation from Stacks 0F7B/0F7I, with the canonical map definition, adjunction normalization,
and proved ordinary shift calculus in `Sheaf.Paper.RefinementOpenRestriction`.

`lem-sf-ring-open-map-invertibility` records only pointwise invertibility of that constructed
map, by finite proper base change and then actual normalized-system transport to integral
coefficients. It is in `Sheaf.Paper.RingOpenMapInvertibility`. Searches found general
adjunction tools but no existing theorem in the required ring-sheaf encoding under exactly
the relative-separatedness hypotheses.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
