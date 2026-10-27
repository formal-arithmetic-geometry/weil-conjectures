## What changed

In `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, prove `specialization_pairs`
and `specialization_transport`. Two proved private lemmas perform equality induction
on arbitrary stage systems. After identifying the systems, the equivalence is the
identity, and the assumed heterogeneous equality identifies finite representative maps.
The transport proof explicitly presents both operations as `StageSystem.tr` before
applying the abstract lemma. Local opacity of scalar-extension and triangulation
constructions avoids unnecessary reductions. All existing public statements,
definitions, attributes, and imports are preserved. The item's node records this route.

## Proved and sorry left

Closed 2 of the item's 11 holes; added 0 holes and split off 0 unfinished statements.
The closed declarations, in namespace
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients`, are:

- `specialization_pairs`
- `specialization_transport`

The nine remaining holes in that namespace are:

- `transitionCommShift_existsUnique`
- `transitionExact`
- `associator_cocycle`
- `shift_existsUnique`
- `transitionIso_commShift`
- `specialization_comparisons`
- `specialization_homCoordinates`
- `specialization_commShift_existsUnique`
- `specialization_distinguished`

Every remaining hole has its existing source and natural-language proof in its docstring
and belongs to node `def-weil-algebraically-closed-coefficients`. No other modules,
nodes, or holes are added. The completed proofs use the already stated equality of
normalized stage systems; its outstanding dependencies remain project obligations.

## No longer needed

None. No imports, library modules, or declared dependency nodes are removed. The other
nine obligations retain their existing dependencies. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

Equality induction is performed in abstract helpers because the two concrete chosen
systems cannot simply be substituted as variables. No statement repair is needed.
Directly comparing the expanded tensor-localization interfaces is unnecessarily slow;
keeping the scalar functors opaque and explicitly presenting transport as `StageSystem.tr`
made the two completed proofs compile within the per-file limit.

An additional proof of `specialization_comparisons` type-checked, but exceeded the
per-file delivery limit even after abstract normalization, explicit instances, and
an attempted helper-module extraction. That proof and its unlanded helper are omitted;
the original named hole and its specification are preserved. No limits were raised.
Profiling options and diagnostic commands are removed from the delivery.

A dependency audit also encountered the existing cycle
`lem-pc-ring-hom-extension-differential` →
`lem-pc-ring-hom-extension-differential-adjacent` → the first node. Those nodes are
untouched; this delivery adds no dependency edges to them.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
