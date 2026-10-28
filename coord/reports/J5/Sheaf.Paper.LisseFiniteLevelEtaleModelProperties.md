## What changed

Proved `AlgebraicGeometry.Scheme.lisse_finite_level_etale_model_properties` in
`Sheaf.Paper.LisseFiniteLevelEtaleModelProperties`, preserving its entire signature.
The conclusion only asks for an etale derived object with bounded finite locally
constant cohomology, without any comparison with `N` or `E`. Choose the zero object;
its homology is zero in every degree by Mathlib's `Functor.map_isZero`, so bounds
`a = b = 0` suffice. The existing proved lemma
`IsFiniteLocallyConstantSheaf.of_isZero` supplies finite local constancy.
Added the proof-only import `WeilConjectures.ConstructibleSheaf.OpenClosed` and opened
its required `ZeroObject` notation scope. No public imports or declarations changed.
Updated the assigned node's proof, proof dependencies, and proof origin to this route.
Server single-file compilation via `lcompile.py` passed in 2.2 seconds with no warnings.
The node is not a realized statement or proof step of its unit, so no unit route changes.

The required three search forms were run with `msearch.py`: LeanFinder for zero
derived complexes and bounded finite locally constant homology, Loogle for
`CategoryTheory.Limits.IsZero`, and grep for
`IsFiniteLocallyConstantSheaf.of_isZero`. Direct repository search located that
already proved source-library lemma and Mathlib's `Functor.map_isZero`.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.lisse_finite_level_etale_model_properties`
(node `new-lem-weil-pbc-lisse-finite-level-etale-model-data`).
Added zero holes; zero `sorry` remain in the delivered Lean file. No split-off
statements or new definitions were introduced. The zero-object argument includes
empty bases, zero rings, and every integer degree without nonemptiness assumptions.

## No longer needed

No existing imports were removed: the sole original public import supplies the
unchanged statement's definitions. All five planned proof dependencies are unused
by this theorem, and were removed from its `proof_deps` and proof step:

- `lem-weil-pbc-comparison-pullback` /
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `thm-weil-pbc-site-comparison` /
  `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
- `det-pe-classical-derived-equivalence` /
  `Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`.
- `lem-sf-proetale-locally-constant-origin` /
  `Sheaf.Paper.ProEtaleLisseOrigin`.
- `lem-weil-pbc-comparison-finite-local-constancy-reflection` /
  `Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection`.

None needs to be imported for the zero-object proof. This is local dependency
pruning; these modules can still be needed elsewhere. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing split does not capture construction of a model of the supplied
object. The assigned statement has no relation connecting its existential witness
`D` to `N` or `E`; consequently its local-model hypotheses are unnecessary. Its
original docstring and original DAG proof promise a descent construction that
its formal conclusion does not specify. This delivery proves the unchanged
formal statement and records this discrepancy rather than treating it as a
proof of finite-level descent.

STATEMENT-DISPUTED: the sibling theorem
`AlgebraicGeometry.Scheme.lisse_finite_level_etale_model_comparison` in
`Sheaf.Paper.LisseFiniteLevelEtaleModelComparison` quantifies over arbitrary `D`
and assumes only bounded finite locally constant cohomology. It lacks any
hypothesis relating `D` to the local models. For a nonempty geometric point and
nonzero finite coefficient quotient (for example `A = ZMod 2` with ideal zero),
set `g` and `U.hom` to the identity and take `E = N = 0`. The maximal sieve gives
`hmodels`, since the realization and pullback functors are additive. Choose `D`
to be the nonzero constant rank-one sheaf in degree zero. It meets `hDbounded`
and `hDlisse`, but its fixed realization cannot be isomorphic to zero: the
comparison inverse image is fully faithful and the fixed realization is an
equivalence. Thus the sibling's conclusion is false. The parent
`lisse_finite_level_etale_model` currently applies this invalid universal
comparison to the unconstrained witness returned by the assigned theorem.
Repair requires connecting the constructed model to the given object, not
proving comparison for every bounded finite locally constant complex. No sibling
or parent signature or proof is changed in this delivery; this report flags the
separate defect for the maintainer's independent review.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteLevelEtaleModelProperties": "80960e473e24077f67e413b8f8583af64ca991c9"}, "results": {"Sheaf.Paper.LisseFiniteLevelEtaleModel": {"hash": "e08b1ea5be1ff4d763c3228fafbd29d12625ce23", "status": "OK"}}, "seconds": 132, "time": "2026-10-28T07:52:34+0800", "transitive": 0, "version": 1}
```

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
