## Worker report

The existing project declaration `WeilConjectures.TrfCohomologicalCorrespondence.fixedScheme`
and its companion declarations in `Sheaf.Paper.TraceFixedScheme` state the node. The module
constructs the fixed scheme as the scheme pullback of the geometric correspondence along the
Mathlib diagonal, with `fixedInclusion` and `fixedProjection`. The theorem
`fixedScheme_relations` records the pullback relation and both projection identities.
`trfFixedGraphMap` and `trfEndomorphismFixedScheme` implement the over-base graph case;
`trfEndomorphismFixedScheme_equalizer` gives the test-scheme equalizer characterization.
`HasFiniteClopenConnectedComponents`, the full-structure-sheaf open component construction,
and `clopenConnectedComponentsIso` implement the finite clopen component convention and
coproduct identification. The three theorem proofs are intentionally `sorry`, as required
for stage 2; all definition data is constructive.

The correspondence hypotheses are rendered by the recorded
`TrfCohomologicalCorrespondence` structure: finite-field datum, coefficient conventions,
prime and finite-dimensional coefficient assumptions, a separated finite-type scheme over
`Spec k`, and its correspondence object. The fixed-scheme clause is
`pullback c.toProduct (pullback.diagonal X.hom)`, with projections `pullback.fst` and
`pullback.snd`; `fixedScheme_relations` renders `c i_F = Delta d` and
`c_1 i_F = d = c_2 i_F`. The graph clause uses an endomorphism `h : X ⟶ X` in the over
category, so `h ≫ a_X = a_X` is included by its type, and uses the graph `(id,h)`. The
component clause uses all fibres of `ConnectedComponents`, requires finiteness and clopenness,
and retains the complete restricted structure sheaf. The coproduct map is `Sigma.desc` and
its inverse is the canonical `asIso`, including the empty scheme/index case.

Dependency declarations read and used: `def-trf-coefficient-conventions` and
`def-trf-correspondence` through `Sheaf.Paper.TraceCohomologicalCorrespondence`;
`def-weil-finite-field-fiber` and `def-weil-scheme-morphism-properties` through the same
record; `def-pc-fibre-product` through Mathlib's scheme pullback API;
`def-weil-connected-scheme` through Mathlib `ConnectedComponents`;
`def-weil-open-immersion` through `Scheme.Opens.toScheme`;
`lem-weil-pbc-scheme-coproduct-family` through `Sigma.desc`; and
`lem-weil-pbc-scheme-morphism-gluing` through the stated coproduct isomorphism theorem.
The existing module was checked in full, including every declaration and docstring, and its
recorded declarations are on the current `newtargets-dag` base.

Edge cases checked: an empty fixed scheme gives an empty component type and initial
coproduct; `h = id` gives the diagonal fixed scheme; a translation endomorphism can give an
empty equalizer; nonreduced schemes retain nilpotents because component subschemes use the
restricted structure sheaf without reduction; and the equalizer statement quantifies over
all test schemes, including empty and nonreduced ones.

Searches made: `msearch.py` LeanFinder query “fixed scheme correspondence pullback diagonal
equalizer scheme finite connected components” (no whole-item declaration); Loogle query
`CategoryTheory.Limits.pullback, CategoryTheory.Limits.equalizer` (only generic categorical
lemmas); grep of Mathlib `AlgebraicGeometry` for `fixedScheme`, `diagonal`, and
`connectedComponents` (constituent APIs only); LeanFinder query for the fixed scheme as a
pullback along the diagonal (generic pullback declarations only); and `rg` over
`WeilConjectures` and `lean/Sheaf` (the exact project declaration above was found). Thus no
second definition is introduced; the existing declaration is reused verbatim.

No statement correction or `STATEMENT-DISPUTED` applies.

## Second reading by NP

I independently reread `def-trf-fixed-scheme.json`, all nine statement dependencies, and
`Sheaf.Paper.TraceFixedScheme.lean`. Every displayed object and relation in the node has a
corresponding declaration: the actual fibre product, both projections, the diagonal relation,
the over-base graph/equalizer, all connected components, full open subschemes, and the
canonical finite coproduct isomorphism. The empty, nonreduced, and identity cases remain
included. No hypothesis is added or omitted, and no coefficient map is used in the geometric
fixed-scheme construction.
