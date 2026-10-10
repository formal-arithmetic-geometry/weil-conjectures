# Stage 1 delivery: `lem-weil-pbc-closed-immersion-conormal-functorial`

## Worker report

The retained split was refined at the ideal-containment and affine-section
steps. Added the unsplit node `lem-weil-pbc-affine-conormal-sections` for the
affine calculation in Stacks 01R3. An unused duplicate factorization node was
excluded because the current DAG already has a reviewed node for it. No Lean
attachment or WANTED source.

## Review by C1

I read `literature/stacks-project/morphisms.tex` at Definition 01R2 and
Lemmas 01R3 (lines 6185-6210) and 01R4 (lines 6240-6268), including the
details 01R4 omits. The item states the closed-immersion case of 01R4 with
the same commutative-square hypothesis. The new child states only the affine
sections and quasi-coherence calculation of 01R3, for an arbitrary closed
immersion; its ideal-square meaning is explicit, it is unsplit with no proof
steps, and its three Mathlib searches have no exact scheme-level match. I
searched current DAG nodes by 01R3, conormal, and affine sections; no existing
node states that calculation. The excluded factorization node repeated the
existing 01HP node and is absent from this delivery.

Step 1 uses the ideal-sheaf kernel and the commutative square: a local section
of I' vanishes on Z', hence its image vanishes on Z. The stalk argument supplies
the ideal containment directly. Step 2 takes the resulting O_X-linear map,
pulls it along i, and uses the cited pullback-composition definition to get
the canonical conormal map; multiplication sends the square ideal into the
square ideal. Step 3 checks well-definedness of the affine quotient map from
g-sharp(I') contained in I. Step 4 uses the new 01R3 child for sections, the
closed-immersion affine-cover node for charts around every z, and the affine
pullback-sections node to show the classes a tensor 1 generate, so the formula
uniquely characterizes the sheaf map. I checked these three node statements
and the pullback definition against each application. The hypotheses hold for
the empty closed subscheme and for a zero ideal as well as nonzero ideals.

The worker removed a duplicate helper and supplied the missing local
uniqueness argument; I restored the parent's pre-existing `created.item` field
while assembling the delivery. `review_split.py` passes, and `check_dag.py`
has no cycles and only unrelated reachability warnings.
