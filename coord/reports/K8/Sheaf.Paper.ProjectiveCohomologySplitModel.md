## What changed

Completed the three proofs in `Sheaf.Paper.ProjectiveCohomologySplitModel`, keeping all
public theorem statements and definition bodies unchanged. `sfSplitRings` is now an ordinary
`def` with the identical type and body, preventing eager unfolding of the ring-sheaf
composition throughout category and derived-category elaboration. Private helpers establish projectivity of
free sheaves from the evaluation hypothesis, identify their maps with generator sections,
and compute derived maps from projective single complexes by the canonical truncation
triangle. The split chain map uses inverses of the actual cell-component isomorphisms,
so its composition with each prescribed cell is the chosen representative chain map.
A private assembly definition and its proved cell equation keep the construction from
being repeatedly unfolded during later elaboration.
The projective-source truncation argument is an all-universe specialization of the
proved private calculation in `Sheaf.Paper.ModuleCupHomologyEvaluationBijective`, copied as a proved private helper
because it is not public. Added proof-only imports for projective-source vanishing and
the source-library shifted-heart homology comparison, together with abelianness of the
category of abelian sheaves used in the epimorphism criterion.
The definition-performance repair and local private proof command are documented in
`coord/changes/sf-projective-cohomology-proof-attributes.md`, including all current
consumers and the original/new definition verbatim.

## Proved and sorry left

Closed three holes (node `lem-sf-projective-cohomology-split-model`):

- `WeilConjectures.sf_projective_cohomology_split_model`.
- `WeilConjectures.sf_shifted_free_generator_bijective_natural`.
- `WeilConjectures.sf_bounded_above_projective_chain_representatives`.

No holes added or split off. No `sorry` remains in the delivered module.
Validation: the original complete proofs compiled in 43.6 seconds and the first delivery's
axiom probe reported no forbidden axioms. A later attempt exceeded the unchanged 60-second
limit. Profiling isolated eager unfolding of `sfSplitRings`; changing only `abbrev` to
`def` reduced the profiled complete compile from 54.1 seconds to 9.0 seconds. Temporary
profiling, public-definition attributes and the increased heartbeat budget are removed.
The final file then compiled cleanly in 6.3 seconds, without warnings and with the
default heartbeat budget. The delivery tool rechecks the final packet.

## No longer needed

No original import removed. All original stated dependencies remain used, either directly
or through Mathlib's projective-source and canonical cohomology APIs. No module is withdrawn.
The explicit chain-homotopy quotient calculation in the planned generator-bijection step
is replaced by the canonical truncation triangle and projective-source vanishing; these
prove the same canonical forward map for arbitrary unbounded targets.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement or construction found. The original eager coefficient-ring
abbreviation was expensive to elaborate; ordinary definitional reducibility fixes that
without altering its object. The DAG's generator calculation can be shortened
by adapting the already proved private projective-source truncation calculation. Zero
ranks, equal endpoints, and vanishing outside the interval need no additional assumptions.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
