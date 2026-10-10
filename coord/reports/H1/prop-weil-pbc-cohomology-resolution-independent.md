# prop-weil-pbc-cohomology-resolution-independent

## Worker delivery

No DAG file changed and no new node created. The slopmaster2 source has `CochainComplex.IsKInjective.nonempty_homology_iso` in `WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean:57`, with its docstring at lines 51-56 explicitly marking `(blueprint: prop-weil-pbc-cohomology-resolution-independent)`. Its statement is the general resolution-independence theorem for an additive functor `G` and two K-injective resolutions; the docstring names the specialization `G = Γ(T,-)`, `K = F[0]` as the node's étale-cohomology assertion. The compressed slopmaster2 sorry map records `s:false, ts:false` for this theorem (lines 51-68) and its sole project dependency, `nonempty_iso_quotient_obj` (lines 34-49), also `s:false, ts:false`.

Attachment: `CochainComplex.IsKInjective.nonempty_homology_iso` belongs to `prop-weil-pbc-cohomology-resolution-independent`. The lead should attach the declaration to the node and mark the Lean audit closed; this worker made no split under the source-first instruction.

No WANTED source, statement correction, or unfinished proof is reported.

## Review by H1

I verified the exact blueprint marker and statement in `WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean:51-68`. `CochainComplex.IsKInjective.nonempty_homology_iso` is the general additive-functor form of this node; the docstring identifies its specialization to étale cohomology. The local sorry map reports it and `nonempty_iso_quotient_obj` as `s:false, ts:false`, so the node is closed on slopmaster2 without a split. No new node was made.
