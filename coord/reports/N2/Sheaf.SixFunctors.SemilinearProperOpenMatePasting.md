## What changed

Completed the two proper-mate assembly proofs in
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`:
`gamma_scalarRestriction` and `gamma_evaluation`. A proved private helper derives
both adjunction-evaluation equations from the specified direct-image mate, using
Mathlib's unit and counit mate identities. The proofs then apply the existing
`WeilConjectures.SemilinearSections.evaluation_mate` to the exact inverse-image
compatibility square. They retain every published comparison and hypothesis.

Added two proof-only imports, each stating one inverse-image compatibility step:
`IntrinsicScalarAlphaCompatibility` and `IntrinsicEvaluationAlphaCompatibility`.
Each uses the actual chosen functor and comparisons, has an independent module,
a source, a complete proof plan, and a DAG node. Updated only the item's proof,
proof dependencies and proof origin. Existing public imports, definitions,
declaration signatures and earlier completed proofs are unchanged.

The final applications specify all four coefficient and four open-extension
functors explicitly. Inferring them from the comparison isomorphisms expanded
localization data and caused slow kernel conversion; the explicit arguments keep
the existing constructions as named functors. No shared definition was modified.

Validation: the final item compiles cleanly in 10.3 seconds. The two new lemma
modules compiled in 30.8 and 29.8 seconds in the last import-ordered check, and
have not changed since. All profiling options, temporary debug modules and
reduced debugging heartbeat limits were removed.

## Proved and sorry left

Two original holes closed by decomposition, not a net proof-count improvement:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_scalarRestriction`.
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_evaluation`.

The item module has zero remaining `sorry`. Two holes are added, exactly:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.intrinsicScalarAlphaCompatibility`
  in `Sheaf.SixFunctors.IntrinsicScalarAlphaCompatibility`, node
  `lem-sf-intrinsic-scalar-alpha-compatibility`.
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.intrinsicEvaluationAlphaCompatibility`
  in `Sheaf.SixFunctors.IntrinsicEvaluationAlphaCompatibility`, node
  `lem-sf-intrinsic-evaluation-alpha-compatibility`.

Both remaining statements concern only the exact inverse-image/open-extension
beta/projector/compositor word, before deriving direct image or taking its proper
mate. The completed assembly proves the unit/counit normalization and transfers
these genuine geometric steps to the specified proper mates. No extra hypothesis
is introduced, and neither new statement mentions gamma or asserts an arbitrary
coefficient comparison can be chosen. Net hole change: zero, two decompositions.

Edge cases checked mathematically: the empty selected clopen factor gives its
zero projector, the full factor gives the identity, and both exact coefficient
functors preserve these maps. Zero coefficient rings give zero module categories.
Scalar restriction is exact for nonflat maps. Identity scheme maps use the same
unit-normalized comparisons. No cartesianness of the whole proper/open square,
faithfulness of derived evaluation, or finiteness of coefficients is required.

## No longer needed

No original Lean import was removed and no module is withdrawn or claimed pruned.
The two new imports are proof-only and both are used. The unit route is retained.

Removed the direct proof edges to the scalar ordinary/derived comparison,
restriction and adjunction nodes: they belong to the retained scalar support and
the new scalar inverse-image normalization step, rather than the completed final
mate calculation. They remain needed transitively and are not globally pruned.

The separate `lem-sf-semilinear-evaluation-ring-square`,
`lem-sf-semilinear-evaluation-ordinary-adjunction`, and
`lem-sf-semilinear-evaluation-derived-adjunction` wrappers are not used by this
proof. Their modules import the item itself and cannot be imported here without
an import cycle. Their necessary lower constructions and normalization proofs
already live in `SemilinearProperOpenEvaluationSupport`; the new evaluation node
reuses that support and `lem-sp-varying-ring-clopen-arrow-evaluation`.

The old direct edges to `def-sp-varying-ring-operations` and
`lem-sf-exact-localization-inverse-mate` are inherited through the normalization,
support and new inverse-image nodes. The old direct mate-pasting edge is replaced by
the explicit proved `evaluation_mate` declaration of
`lem-coef-semilinear-derived-sections`. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The two remaining coefficient clauses were still unfinished. The existing
`derivedScalarComparison` preserves alpha for a separately packaged scalar
functor, and `clopenArrowEvaluation` uses the single-level comparison. Neither
is directly the required equation for the item's uniquely section-normalized
rho/E with its specified rhoP/evalP and inverse open mates. This missing
identification is now explicit in the two inverse-image nodes. The new scalar
node's proof plan identifies the package through its section-normalized natural
isomorphism, rather than duplicating the existing package theorem.

The evaluation-adjunction wrapper modules are downstream consumers of this item,
so the old proof-dependency list could not be realized as direct Lean imports.
The existing lower support is the usable boundary. No mathematical statement or
blueprint unit step was changed.

## New nodes

`lem-sf-intrinsic-scalar-alpha-compatibility` records the scalar inverse-image
step. Use the existing ordinary scalar package; identify its functor with
rhoOrdinary by the section and transition formulas, transpose the normalized
direct-image comparison to identify rhoP, and use the inverse open mate for
rhoJ. Transport the already stated package alpha equality along those
identifications. Stacks 03D7, 03DI and 0F7B supply the adjunction/open construction;
the simultaneous coefficient-system extension is explicitly agent-formulated.

`lem-sf-intrinsic-evaluation-alpha-compatibility` records the evaluation
inverse-image step. Use the existing single-level clopen-arrow comparison and
its ordinary constant-diagram lift, localize the exact alpha word, and identify
the prescribed evalP and inverse open mate evalJ. This constructs the equality
before evaluating any derived morphism. Sources and the three Mathlib/library
searches are recorded in each node and both docstrings.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
