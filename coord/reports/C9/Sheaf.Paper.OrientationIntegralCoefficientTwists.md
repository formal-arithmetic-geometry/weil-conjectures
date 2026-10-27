## What changed

Prove `WeilConjectures.sfOrientationIntegralTensorUnit_isIso` in
`Sheaf.Paper.OrientationIntegralCoefficientTwists` from existing declarations.
The ordinary product identifies the tensor representative with the single line
at d+e. The derived single-functor shift comparison and intrinsic twist membership
make this object complete. The legacy comparison and the Roos completeness
criterion make the actual completion unit invertible; its representative
normalization and `tensorTowerIso` give the exact tensor operation unit in the
original statement. A proved private categorical helper combines invertibility
of two functor images without unfolding their coefficient constructions. No comparison map is replaced by an arbitrary isomorphism.

The complete module compiled cleanly through lcompile.py in 38.2 seconds, below
the 60-second per-file limit. deliver3.py performs the required delivery preflight
and axiom checks.

Add private proof imports for intrinsic shift stability, the legacy comparison,
the Roos completeness criterion and its coefficient datum. Update the existing
node's proof route to record these uses. Existing public statements, definition
bodies and public imports are preserved.

## Proved and sorry left

Closed one of the four original holes:
`WeilConjectures.sfOrientationIntegralTensorUnit_isIso`.
No holes added; no split-off statements.

Three original holes remain, all attached to
`def-sf-orientation-integral-line-comparisons` with their original source and
complete proof docstrings:

- `WeilConjectures.sfOrientationIntegralLineMaps_existsUnique`
- `WeilConjectures.sfOrientationIntegralComplexProduct_existsUnique`
- `WeilConjectures.sfOrientationIntegralPullUnit_isIso`

The pre-existing proved `sfOrientationIntegralComplex_good` is retained.
The tensor-unit proof uses the existing ordinary product theorem, whose proof
remains an independent hole. Thus the result is a proof from declared dependencies,
not a claim that its transitive axiom closure is now sorry-free.

## No longer needed

No modules withdrawn, no imports removed, and no original dependencies pruned.
The tensor-unit clause needs no separate local computation of surjective
quotient transitions: the existing normalized Roos completeness criterion
supplies this step. All public imports remain because they form the existing
re-exported interface.

## Where the brief, the DAG or earlier work was wrong

The existing node recorded only the previously completed good-complex clause;
it now also records the tensor-unit argument. The Frobenius line and pull-unit
statements require `IsIso g` and cannot directly supply the arbitrary-map clauses
of this item. No existing statement has been weakened or disputed.

The tensor completion argument also covers d=0, e=0, and the empty scheme:
shift stability, the original ordinary product and the Roos criterion have no
nonemptiness or positive-degree hypotheses. The auxiliary prime is chosen above
l+1 and imposes no characteristic hypothesis on X. The adic datum is used only
as proof input to the completeness equivalence, not to choose mathematical data.

Generic tools used across units: intrinsic constructible shift stability,
legacy completeness comparison, the adic coefficient datum and normalized Roos
completeness. These prove properties of the existing coefficient objects and do
not change the orientation unit's route.

Local elaboration disables only the three imported principal-Koszul size and
sheafification instances, whose unconstrained coefficient-size parameters caused
universe metavariables in existing declarations. No declaration signature or
consumer-visible attribute is changed. Local irreducibility follows the existing
ambient-operation proof pattern to avoid unfolding standard derived localization
and the coefficient limit and strict quotient tower during the final categorical
argument. The final application enables respectTransparency locally, so those
large constructions remain abstract while Lean checks the composition.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
