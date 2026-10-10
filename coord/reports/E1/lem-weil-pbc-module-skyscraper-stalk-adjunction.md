# Stage 1 split: lem-weil-pbc-module-skyscraper-stalk-adjunction

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-skyscraper-stalk-adjunction.json`: split into four explicit steps; the existing Mathlib search finds no module-sheaf adjunction match. No new nodes.

## Attachments

None. The item has no Lean declaration on `slopmaster2`.

## WANTED

None. Stacks Project `sheaves.tex` is available at Definition Tag 009A (`definition-skyscraper-sheaf`, case (4)) and Lemma Tag 009C (`lemma-stalk-skyscraper-adjoint`).

## Source and split corrections

Stacks omits the proof of 009C. The item's statement already spells out the ring action and both directions of the Hom bijection, and agrees with 009A(4)/009C for a scheme viewed as a ringed space. I supplied the omitted argument: the cover condition for the skyscraper (including the empty open), its module action and additive functor, independence of the representative germ and linearity, construction of the inverse with all restriction cases, and naturality in both variables. Only the existing definitions of a module sheaf and module stalk are used. No stronger separation hypothesis on the point is needed; the stalk at other points need not be zero.

## Unfinished work

None. No Lean code or build was attempted, as required for Stage 1.

## Review by E1

I read Sheaves Definition 009A (`definition-skyscraper-sheaf`), case (4), and Lemma 009C (`lemma-stalk-skyscraper-adjoint`) in `sheaves.tex`. The statement's scheme/ringed-space module action and Hom bijection agree with those tagged statements. No new nodes were added; the existing `def-weil-pbc-module-stalk` and `def-weil-sheaf-of-modules-category` statements were opened and define the germ equivalence, module action, and sheaf category used in every step. The existing Mathlib skyscraper result is only the additive-sheaf case, so it is correctly retained as a non-leaf search result.

Step 1 checks the sheaf gluing for opens containing or missing x, including the empty open, and the module action and additive functor. Step 2 uses the stalk equivalence relation to make the map on germs well defined, then checks O_{X,x}-linearity by restricting representatives to a common neighborhood. Step 3 constructs the inverse on every open and checks all restriction cases, including a smaller open missing x; the two composites are evaluated on sections and germs. Step 4 writes naturality in the sheaf and module variables. These are elementary calculations from the cited definitions and the 009C assertion; no hidden separation condition or zero-stalk claim is used. I checked the empty open, a point contained in all relevant opens, and a non-T1 space. The worker's report needed no correction, and no A-F issue remains.
