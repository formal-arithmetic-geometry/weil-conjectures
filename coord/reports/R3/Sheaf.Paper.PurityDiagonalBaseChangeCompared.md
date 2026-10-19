## What changed

Proved `WeilConjectures.PurityFiniteSetting.comparedDiagonalBaseChange` in
`Sheaf.Paper.PurityDiagonalBaseChangeCompared`, preserving every signature, definition,
public import and existing docstring. No other Lean module is changed.

The proof first derives `HasInvertibleExponent P.Coefficient X`: ell has p-adic norm less
than one, so it belongs to the recorded maximal ideal; its level-th power lies in the
uniformizer ideal to that level and vanishes in the coefficient quotient. This positive
power is a unit on X by the published local-unit theorem and the stalkwise unit criterion.
There is no ramification divisibility assumption. The base Y is locally Noetherian by
its finite-type structure map, hence quasi-separated. Apply upstream
`Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension` to each
self-product square, then `Etale.isIso_dualizingComplexBaseChangeMap_iff` at the unit.
Smoothness of both projections and the flipped Cartesian square are supplied by the
existing scheme interfaces. The three explicit diagonal restriction constructions stay
unchanged, with their specified inverse mate and composition/identity comparisons.

Added only the proof import
`WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange`.
Updated `lem-pur-diagonal-base-change` proof, proof dependencies, proof origin and obsolete
tool-use entries to describe this route. No new node or change record is needed.

Validation: an initial resumed dry run passed at commit 86827e2754: compilation and
preflight succeeded, with review class CODEX for the node-file change. Nothing was
pushed by the dry run. Earlier single-file compilation also succeeded without errors
or warnings (45.4 seconds), and a scratch compile with the delivery axiom probe passed
(38.6 seconds), reporting SHEAF-PROBED 5 and no unexpected axioms. An earlier attempt
timed out at 60 seconds; profiling showed no dominant costly unfolding (tactic execution
3.48 seconds, type checking 3.34 seconds). Edge cases remain covered by the unchanged
statement: d = 0, empty
schemes, and all positive coefficient levels, including levels not divisible by the
ramification index. The coefficient-unit argument uses stalkwise detection, which also
applies to the empty scheme. Delivery preflight performs the declaration/axiom probes.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.PurityFiniteSetting.comparedDiagonalBaseChange`
(node `lem-pur-diagonal-base-change`).

Zero holes remain in the item. Zero holes added; zero statements split off.
This is a complete proof from existing declarations, rather than a decomposition.
Existing imported declarations may still depend on their own recorded proof obligations.

## No longer needed

Removed all eight original proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`:
  node `lem-pur-proetale-constant-ring-composition` is unnecessary for the existing
  etale-coordinate chain and its specified comparison-site transport.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity`:
  node `lem-pur-proetale-derived-pullback-identity` is unnecessary; the existing etale
  composition/identity comparison already constructs the unchanged restriction chain.
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`:
  node `thm-pur-cohomological-smoothness` is unnecessary for this item; its underlying
  canonical smooth-base-change theorem gives exactly the two needed maps directly.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  no separate exceptional inverse-image construction is used by this proof.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  no separate intrinsic pullback/tensor/Hom interface is required in these canonical
  etale coordinates; the existing definitions retain the pullback chain.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  node `lem-weil-pbc-proetale-derived-pullback-composition` is unnecessary here; the
  explicit etale composition/identity chain is already available.
- `Sheaf.Paper.PurityFiniteSetting`:
  its direct proof import is redundant with the unchanged public imports. Its setting,
  local-unit result and node `def-pur-conventions` remain used.
- `Sheaf.Paper.PuritySectionInvariantIntrinsic`:
  the unchanged public `PuritySectionInvariantCompared` supplies the actual section
  invariant and its specified canonical presentation.

Removed the unused top-level tool approvals
`lem-weil-pbc-proetale-derived-pullback-composition` and
`lem-weil-proetale-isomorphism-inverse-image`. Kept the smooth relative-dimension
permanence approval. The latter inverse-image approval was already stale in the old
node; the previous review note also says it was unused.

These are dependencies no longer needed by this item, not claims that they have become
unreachable everywhere else. Original statement dependencies are preserved: the same
mathematical notions and exact theorem signature remain in force. The smooth-purity
unit route is unchanged: self-product base change, restriction along the diagonal,
composition, and identity. Its later deformation and vector-bundle arguments are untouched.

## Where the brief, the DAG or earlier work was wrong

The old plan expanded general pro-etale ringed-module coefficient, composition and
identity interfaces that this already-published canonical etale presentation does not
need. The stronger cohomological-smoothness theorem is also unnecessary for its single
base-change clause: the upstream smooth exceptional-base-change theorem applies directly
once the source exponent and quasi-separatedness of Y have been verified. No mathematical
statement was found false and no target, definition or intermediate signature changed.

The F1 landing d1f89ae698 failed the global build because smooth base change needs
QuasiSeparatedSpace Y, which its proof did not install. This delivery derives
IsLocallyNoetherian Y from the existing LocallyOfFiniteType aY hypothesis; the
quasi-separated instance follows without strengthening the statement. It also avoids
the DNC comparison import used by that failed landing, proving the coefficient-exponent
fact directly from the existing coefficient construction. No importer adaptation is
needed because all signatures, public imports and definitions are unchanged.

After that dry run, the submission compile timed out before pushing. A fresh profiling
compile passed in 39.0 seconds, with SHEAF-PROBED 5 and no unexpected axioms. It
reported 2.47 seconds of tactic execution, 3.81 seconds of type checking and 15.5
seconds of typeclass inference. Removed an unnecessary dependent substitution along
hf: the coefficient-unit proof now uses the given structure map aX directly. This
keeps the same mathematical argument and avoids rewriting its finite-type instances.
The updated packet passed compilation and preflight in a second dry run at edefd62211.

This resumed session retained the earlier sandbox proof, node, report and original
session clock. It checked the pending dry-run result before attempting delivery.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
