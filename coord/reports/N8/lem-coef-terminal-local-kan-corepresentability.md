# Stage-1 report: lem-coef-terminal-local-kan-corepresentability

## Files written

- `dag/nodes/sec-six-functors/lem-coef-terminal-local-kan-corepresentability.json`: repaired eight-step split, with no statement change and no new nodes.
- `citations.json`: verbatim quotes for every proof-step citation.

## Attachments

None. No exact sorry-free project declaration carries the item.

## WANTED

WANTED: Cisinski, *Higher Categories and Homotopical Algebra*, Definitions 7.2.2–7.2.6, Theorem 7.2.8, Remark 7.2.10 and Proposition 6.1.14, for the local-comma criterion; the supplied literature has no archival CatLR PDF. The proof is therefore recorded as agent-written from those cited places and the explicit coherent constructions.

## What was wrong and what was repaired

The retained split had removed cyclic Yoneda and point-cocone nodes but left two comparisons implicit. Step 2 now unfolds the internal functor simplicial set to identify constant-point transformation spaces with `Fun(K,Z)`. Step 6 now gives the covariant evaluation map and its parameterized inverse explicitly from the slice right fibration, right-pinch comparison, composition homotopies and the pointwise Kan mapping property. Step 8 states how contractible homotopy fibers extend the comparison over all coherent parameters. The statement, hypotheses, comma orientation, identity normalization and target-variable naturality are unchanged. The ten cited nodes were read in full; each quote in `citations.json` is a verbatim part of its cited statement, and `proof_deps` is exactly the union of step uses. No duplicate or Mathlib leaf was added, and no SGA source is used.

## Review by N8

I reread the current chapter and unit records, the item statement, all ten cited node statements, the blueprint ancestor, and the source places named above. I checked that the strict comma pullback agrees degree by degree with the nerve, that the singular unit and Kan mapping-invariance hypotheses allow empty nerves, and that terminality supplies the stated normalization. I checked the two formerly implicit comparisons directly: the constant-diagram mapping identification follows from the displayed definition of `Fun(K,𝒞)_n`, while the covariant evaluation and inverse are the parameterized family `f ↦ H(f)(z)`; composition and pinch homotopies give their simplicial compatibility. The data-map and target-map comparison is then equality at the normalized identity point, extended over coherent parameters by the cited contractible-fiber criterion. Small cases (terminal point, identity-only W, and empty comma nerve) satisfy the statement. `srvcheck.py` reports both `check_dag` and `review_split` passing, and the exact server preflight reports no finding.

## What I could not finish

The cited Cisinski source remains unavailable as a local archival file; no Lean or compiler work is authorized in this stage. The split itself is complete and contains no new unsplit dependency.
