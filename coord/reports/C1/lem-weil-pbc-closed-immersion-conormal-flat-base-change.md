# Stage 1 delivery: `lem-weil-pbc-closed-immersion-conormal-flat-base-change`

## Worker report

Expanded the retained split of Stacks 0473. The affine ideal-cotangent node
is a Mathlib leaf, and a new Mathlib leaf records the affine criterion for a
flat scheme morphism. The proof now cites the base-changed ideal calculation
and the required sheaf-locality facts. No Lean attachment or WANTED source.

## Review by C1

I read `literature/stacks-project/morphisms.tex` at Lemma 0473 and its proof,
and `schemes.tex` at Lemma 01JU for the ideal of a base-changed closed
immersion. The item's cartesian-square and flatness hypotheses match 0473;
its affine parenthetical is exactly the ring calculation used there. The
affine-flatness child states the equivalence of (1) and (2) of Stacks 01U5
for all affine pairs U,V, not just one selected chart. Its objects and flat
ring-map condition are explicit. No existing DAG node states that criterion;
I searched by 01U5, affine flatness, and the Mathlib declaration.

I read Mathlib v4.33.1 `RingTheory/Ideal/CotangentBaseChange.lean` at lines
34-45, 58-66, 87, and 112-116. With R=S=A and T=B, the unconditional
`Ideal.tensorCotangentHom_surjective` gives the first clause of the affine
node, and `Ideal.tensorCotangentEquiv` gives the second with `[Module.Flat A B]`.
The tensor-unit and symmetry equivalences identify its map with the displayed
map on I/I². I also read `AlgebraicGeometry/Morphisms/Flat.lean` at lines
41-45 and 106-107: `flat_iff` uses every affine pair, and the stalk-map
equivalence matches the flat-morphism definition. Both leaves include source
file, line, and specialization in their match records. The ring node's
statement cites the existing flat-ring-map definition; the new scheme node
has no proof steps because it is a Mathlib leaf.

Step 1 cites the existing functorial conormal map. Step 2 restricts the
cartesian square to affine charts, using the open-preimage and square-pasting
nodes, then uses the 01JU node to get I=I'R. The affine pullback-sections node
identifies the source and the functorial conormal node identifies the map.
Step 3 applies the checked ring leaf; under flat g the affine criterion gives
flat R'→R. The cited quasi-coherent cokernel and affine-tilde nodes make
surjectivity and bijectivity local on this cover, while the sheaf-on-basis
node glues the isomorphism. I checked each cited statement, including the
base-changed ideal's affine formula and the cokernel's affine-section clause.
For I'=0 both maps are maps of zero modules; for the empty fibre product the
local assertions are vacuous. No nonzero-ideal or Noetherian hypothesis was
introduced. The worker supplied the missing locality dependencies; I
requested no further correction. `review_split.py` passes; `check_dag.py`
has no cycles and only unrelated reachability warnings.
