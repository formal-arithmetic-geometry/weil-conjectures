## What changed

Completed four theorem proofs in `lean/Sheaf/Paper/FrobeniusCoefficientTwistsCanonical.lean`.
Every existing declaration, signature, definition body, visibility, docstring and import is
unchanged. No other Lean module is modified.

- `WeilConjectures.FrobeniusCoefficientTwists.rationalTwistCommutation_naturality`:
  extract the rational natural isomorphism with the prescribed components from
  `WeilConjectures.derivedPullbackTensorIso`. Specialize its naturality to `(a, id)`.
  Rewrite the components, compose with `id tensor theta`, and use functoriality and
  componentwise composition in the product category.
- `WeilConjectures.FrobeniusCoefficientTwists.commonTwistCommutation_naturality`:
  the same argument using the existing common-stage natural isomorphism. Its unused
  finite coefficient parameter is instantiated at the recorded least finite stage.
- `WeilConjectures.FrobeniusCoefficientTwists.rationalWeilLine_heart`:
  use the actual integral signed line as the witness for each rational standard class.
  Its underlying derived object is a sheaf in degree zero. Mathlib's homology comparison
  with complexes and vanishing of single-complex homology prove both inequalities.
- `WeilConjectures.FrobeniusCoefficientTwists.commonWeilLine_heart`:
  represent both standard-class witnesses at the existing least finite coefficient field,
  apply the rational result, and use the identity isomorphism on the literal stage object.

The file compiles cleanly using `lcompile.py` (15.1 seconds in the last completed check).
The arguments cover every integer twist, including zero and negative twists, and require
no additional hypotheses. No finite-type or nonempty-site assumptions were introduced.
The naturality proofs use the already stated dependency, even though its own proof remains
open, as required by stage 3.

## Proved and sorry left

Closed 4 of the original 11 holes; added 0 holes; split off 0 theorems.
The four closed declarations are listed above. This is a partial proof delivery, not a
hole decomposition and not a claim that the imported dependencies are axiom-free.

Seven original holes remain, all in namespace `WeilConjectures.FrobeniusCoefficientTwists`
and all attached to node `def-weil-frobenius-coefficient-twists`:

- `existsUnique_positiveLineMaps`: completed coefficient extension of the specified
  root-limit map, tensor-power recursion, and uniqueness on local scalar/root generators.
- `existsUnique_signedLineMaps`: internal-Hom transport with the displayed evaluation
  equation, conjugation by the positive map, and uniqueness of all negative components.
- `existsUnique_finitePositiveLineMaps`: finite reduction and its normalized generator
  formula, including uniqueness. The site-descent interface uses a different module
  pullback construction and requires prime invertibility, so it is not directly applicable
  to this unrestricted theorem.
- `existsUnique_finiteSignedLineMaps`: the corresponding finite dual evaluation transport
  and uniqueness.
- `existsUnique_pullbackAugmentation`: construct the completed-linear quotient-unit maps,
  prove strict transition compatibility, and lift to the specified mapping cocone with zero
  second component; prove its two-component uniqueness and naturality.
- `pullbackAugmentation_isIso`: identify that particular normalized augmentation with the
  derived-completeness unit under isomorphism-site reindexing. An arbitrary existing
  derived pullback isomorphism alone does not identify this arrow.
- `existsUnique_completedToOrdinary`: descend the normalized good-representative
  comparison, with independence of resolutions, naturality, and the stated uniqueness.

The original theorem docstrings retain the sources and proofs in words for these holes.
I read the existing tensor/Hom, root comparison, finite site-descent, isomorphism reduction
and scalar-comparison interfaces. No replacement theorem or new unproved assumption is
introduced for their remaining glue.

## No longer needed

None of the existing imports is removed. They supply the published definitions and the
interfaces for the seven remaining proof obligations. No node or module is made unreachable
by this partial delivery, and no existing dependency is replaced by a newly stated lemma.
The common-stage naturality proof uses the common-stage naturality already packaged by
`derivedPullbackTensorIso`, so no additional finite-stage descent helper or import is needed.
The rational heart proof uses its existing integral membership witness and degree-zero
homology; no new local-freeness or finite-reduction helper is needed in this module.

## Where the brief, the DAG or earlier work was wrong

The item's owning DAG node is a definition with empty `proof` and `proof_deps`; there is no
numbered proof plan to translate for this item. Its `stmt_deps` already names the coefficient
line, heart, Weil-pair and derived tensor comparison interfaces used here. The proofs follow
those interfaces and the existing docstrings; no blueprint unit statement or step is bypassed
(the unit's `realized.statement` and `realized.steps` are empty).

No false statement or definition defect was established. In particular, the finite
site-descent and general scalar-comparison declarations are not interchangeable with the
specific unrestricted module pullbacks and normalized augmentation appearing here.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
