## What changed

Replaced the proof hole in `Sheaf.Paper.CoefficientDerivedSystemResolutionModels`
with a complete Lean assembly from three strictly smaller construction statements.
The existing public theorem signature, definitions, public import and docstring
are unchanged. Added private proof imports for the three new modules, the ringed
closed tensor construction and the semilinear derived sections calculus.

The parent now proves generic closed-evaluation calculations: `uncurry_formula`,
`evaluation_target`, `evaluation_source`, `evaluation_both`, `uncurry_naturality`,
`uncurry_precomp`, `baseChange_naturality`, `baseChange_transpose`,
`tensorComparison_inverse` and `baseChange_evaluation`. It also proves
`coefficientDerivedSystemTensors_exist`, retaining the associator/unit/symmetry
models; `coefficientSequence_isIso_iff_evaluations`, from the existing semilinear
calculus; and `fiberHom_eq_baseChange`, by injectivity of the closed transpose.
These are private proved helpers, not additional proof obligations.

The construction derives fiber naturality and beta-evaluation from these helpers.
It defines globalEvaluation as the actual composite of sections evaluation and
sections of fiberHom, so its model equation is reflexivity. It supplies the
existing enriched-isomorphism proof and assembles the arbitrary-system projection
and scalar Hom-zero equations without changing their statements.

The new modules separate reduction/quotient models, local internal-Hom fibers,
and sections/limit normalizations. Their support definitions are explicit Prop
formulas or record types. No public definition chooses data from an unproved
existence theorem: choices and witness elimination occur inside theorem proofs.
No other existing Lean module was changed.

Validation: all four modules compile through lcompile.py in dependency order,
with no warnings or errors; the parent takes 9.4 seconds. The combined updated
DAG closure has no missing dependency or cycle. The index-zero quotient remains
positive. No nonempty-scheme, boundedness, perfectness or arbitrary-input Hom
base-change assumption was added. Fiber assertions retain both normalized-input
hypotheses, and sections_projection remains valid for arbitrary systems.

## Proved and sorry left

This is a decomposition, not an axiom-free proof of the original obligation.
The parent `WeilConjectures.coefficientDerivedSystemResolutionModels`
(node `lem-coef-derived-system-resolution-models`) has a complete proof and zero
local sorries, conditional on the three statements below and the existing
project declarations. One existing hole was closed and three holes were added;
the net hole count of this packet is minus two, before any independent pruning.
No original hole was discharged without new split obligations.

Every sorry added by this delivery:

- `WeilConjectures.coefficientNormalizedReductionModels`, node
  `lem-coef-normalized-reduction-models`: reduction adjunction and normalized
  tensor/quotient models, for fixed tensor data. No Hom fibers or sections.
- `WeilConjectures.coefficientNormalizedInternalHomFibers`, node
  `lem-coef-normalized-internal-hom-fibers`: local Hom fibers, evaluation,
  transitions and internal composition, assuming reduction and quotient models.
  No sections, global limit, beta equation, naturality or conservativity.
- `WeilConjectures.coefficientDerivedSectionsNormalization`, node
  `lem-coef-derived-sections-normalization`: normalized scalar/tower sections,
  limit comparison, actual projections and scalar Hom-zero, assuming reduction
  and finite tensor normalization. No construction of reduction or Hom fibers.

Each is a whole public theorem with proof `by sorry`, source, complete proof in
words and a matching new DAG node. All private helpers are proved.

## No longer needed

None. No existing import or module was removed. The parent node now records its
actual immediate dependencies on the three smaller statements and the existing
ringed, semilinear and closed-scalar constructions. Every dependency in the old
proof_deps remains in the new transitive DAG closure; none is claimed pruned.
The blueprint unit and its route are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or target discrepancy was found. The original proof sketch
suppressed the transports between the specified coefficient functors and the
existing general derived constructions. These are substantial mathematical
normalization steps, now isolated rather than claimed automatic.

Closed naturality, transposition and beta-evaluation do not require new site
comparison statements: closed adjunction and the existing tensor square prove
them directly. Internal composition additionally needs associator coherence.
The parent retains the coherence witnesses from the ringed tensor theorem;
tensor/uncurrying models alone should not silently stand in for those witnesses.
The local Hom split explicitly assumes this retained coherence. The remaining
three obligations are independent parts of the construction, not renamed copies
of the original existential statement.

## New nodes

`lem-coef-normalized-reduction-models` is realized by
`Sheaf.Paper.CoefficientNormalizedReductionModels`. It records the fixed-tensor
reduction construction and finite quotient calculus, with the existing
projection-derived-adjunction, limit-projection, tensor-pullback and strict-site
results as planned inputs. The tensor coherence predicate only retains witnesses
already supplied by the existing ringed tensor theorem.

`lem-coef-normalized-internal-hom-fibers` is realized by
`Sheaf.Paper.CoefficientNormalizedInternalHomFibers`. It isolates the finite-prefix
Hom-fiber and transition argument and composition compatibility. Its support
record omits the naturality, transpose, beta and conservativity fields actually
proved in the parent.

`lem-coef-derived-sections-normalization` is realized by
`Sheaf.Paper.CoefficientDerivedSectionsNormalization`. It isolates ordinary
section transport, normalized derived comparisons and their projection/Hom-zero
equations. The resolution equation is the existing global-limit model formula
with its comparison supplied directly as a parameter.

All three nodes have the original chapter/unit, source references, numbered
proof steps, dependency records, recorded Mathlib searches and exact theorem
signatures. Only proof, proof_deps and proof_origin of the existing parent node
were updated. No change record is needed: no existing public interface changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CoefficientDerivedSectionsNormalization": "e694e3e2d2220305eedd04f70c65c6824e1d680d", "Sheaf.Paper.CoefficientDerivedSystemResolutionModels": "bb15ec923973679cc0f78d186dfa0bb723fce70c", "Sheaf.Paper.CoefficientNormalizedInternalHomFibers": "57192c37ddda660008127708a73c78cdb99a005f", "Sheaf.Paper.CoefficientNormalizedReductionModels": "3ac2efa7c7998abe2ffd345ca9023f8d7c267a62"}, "results": {"Sheaf.Paper.CoefDerivedSystemEvaluationCalculus": {"hash": "eb25d1ee42d53632b6dc1fd074d4c6dae0593d1d", "status": "OK"}}, "seconds": 16, "time": "2026-10-28T02:28:45+0800", "transitive": 0, "version": 1}
```

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
