## What changed

Continued Step 2 of `lem-route-is-iso-smooth-purity-map` inside the assigned
module, preserving all existing public signatures, public imports, attributes,
instances and data bodies.

Proved two private lemmas:

- `smoothTrace_exceptionalSingleDegree`: the homology vanishing retained by
  `IdentifiesExceptional` gives both standard t-structure bounds at `-2d` for
  every actual finite exceptional unit.
- `smoothTrace_exceptionalHomology_bijective`: for any source bounded above at
  `-2d`, the degree-`-2d` homology functor induces a bijection on maps into that
  exceptional value. It determines derived maps and uniquely lifts prescribed
  cohomology maps, using the already proved truncation Hom theorem.

Proved the separate private `smoothTrace_nativeExceptionalHomology`: extract the
actual native finite levels from the unchanged
`smoothTrace_normalizedFiniteSystem`, apply its retained `ReconstructionResult`
to those same levels, keep the reconstructed Tate object and its
`IdentifiesExceptional` proof, and supply the Hom bijections at every positive
level. The original
normalized-system theorem and its full data remain unchanged. This supplies the
finite single-degree Hom calculation used by the reconstruction route; it does
not assert an arbitrary derived-system lifting theorem.

Added the private proof import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`, and updated
the owning DAG proof description. No additional module is changed.

The argument includes `d = 0`, the first positive coefficient level `n + 1 = 1`,
empty schemes and a zero source. It uses only strict inequalities away from the
purity degree and the general truncation Hom theorem, with no extra positivity
or nonvanishing hypothesis.

Profiling the first assembly exposed expensive elimination of the full inverse
quotient-square package. The final proof obtains only the needed witnesses from
the smaller finite-system theorem and its reconstruction result. Profiling
options are removed. The optimized file typechecked in 42.0 seconds; its only
warning was a long documentation line, which is shortened before delivery.
The delivery tool performs the final compile and checks.

The server claim, queue, rework and build-error records were checked: A2 holds
this item; it has two holes and is classified as disputed. No rework row is
present. The historical build error reports a missing file, which is now restored.

## Proved and sorry left

Original holes closed: **0 of 2**. Holes added: **0**. Split off: **0**.
This delivery is partial formalization of a genuine reconstruction step.

All three new private lemmas are completely proved. The native assembly uses
the unchanged finite-system theorem, its retained reconstruction result, and
the new Hom calculation.
No existing declaration signature or docstring changes, including private ones.

The two unchanged holes in namespace
`AlgebraicGeometry.ProEtale.CondensedRing` are:

- `isIso_smoothPurityMap`, node `lem-route-is-iso-smooth-purity-map`;
- `smoothPurityIso_comp_openImmersion`, node
  `lem-route-smooth-purity-iso-comp-open-immersion`.

The pre-existing imported hole `existsUnique_smoothTrace`, node
`lem-route-smooth-trace-representing-unique`, is unchanged. Neither it nor the
unconditional purity instance is used in the new proofs. The retained finite
reconstruction inputs may depend on their own pre-existing holes; none is added
by this delivery.

## No longer needed

None. No existing import, module, node, or unit step is pruned. The unchanged
public declarations and the geometric reconstruction route still need their
recorded dependencies. The generic Hom calculation uses the existing proved
source-library theorem instead of introducing another statement with a hole.

## Where the brief, the DAG or earlier work was wrong

The assigned module is already restored and previously landed. Its historical
missing-file error is not a current definition defect.

STATEMENT-DISPUTED: the elaborated `isIso_smoothPurityMap` signature omits
`SmoothOfRelativeDimension d f.left`. The existing independent geometric-point
counterexample in this module rules it out for the identity with proposed
dimension one. Its signature has no supported correction entry in
`coord/upstream-statement-exceptions.tsv`; the source-library boundary therefore
requires preserving it.

STATEMENT-DISPUTED: the existing `smoothTrace` chooses from unnormalized
representing-pair uniqueness. The retained point/sign counterexample, and the
current `TraceExistence` module, show that uniqueness is false even in dimension
zero. The finite diagonal/deformation orientation must specify the actual
natural Hom equivalence. No use of that false uniqueness or its resulting
inconsistency is made to close an original hole.

The present finite-level Hom result is a genuine part of case (b) of exceptional
reconstruction. Transport into its strict varying-coefficient system Context and
the prescribed normalized trace construction remain. This report does not claim
completion of those steps or of the smooth-trace definition repair.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"WeilConjectures.SmoothPurity.Defs": "d391d1bf7bd8841478635f95d13251d0f22a130f"}, "results": {"Sheaf.Targets.SmoothPurityQbar": {"hash": "b61095f4237cc889a88d12105bb9497ef53983af", "status": "OK"}, "WeilConjectures": {"hash": "a9f1970d653af90a208232c6a0658c40dd10bba9", "status": "OK"}, "WeilConjectures.PoincareDuality.Poincare": {"hash": "24c41d940617dccc117d662fe9a0ea621d946970", "status": "OK"}, "WeilConjectures.TraceFormula.Dualizing": {"hash": "6f0205d1db4c599fd319656d4acc1446b3c84ebb", "status": "OK"}}, "seconds": 103, "time": "2026-10-28T12:05:41+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
