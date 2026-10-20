## What changed

Replaced the single `finite_compatibility` hole in
`Sheaf.SixFunctors.OpenTensorNormalization` by a compiling construction from
`exists_normalized`, `finite_comparisons_exists`, and
`finite_compatibility_of_comparisons`. The theorem's signature is unchanged.
Its two new imports are private proof imports.

`FiniteComparisonsExistence` proves the four finite realizations: forget
commutativity on the locally bijective constant-section maps, use the existing
scalar restriction equivalence, and take its additive inverse. The counit supplies
the underlying additive sheaf comparison. Its componentwise linearity proves
exactly the required constant-scalar equation. Cocontinuity of open composition
preserves local injectivity and surjectivity, so this also handles the literal
restricted constant ring sheaves on both opens. This construction uses the proved
private scalar restriction API of `FiniteConstantCoefficientTransport` through a
private `import all`; no source-library declaration is changed.

The two direct-image comparisons are also constructed in Lean. Their maps lift
the underlying additive sheaf comparisons through restriction of scalars. Local
surjectivity of constant sections makes them coefficient-linear. The inverse
underlying realization comparison is proved to preserve scalars; the ambient
coefficient unit identity is proved by the sheafification adjunction, and its
corner identity by naturality. Reflection of isomorphisms and cancellation give
the required section normalization for both g and gU.

`FiniteOperationComparisons` introduces `FiniteDirectPin`, the actual subtype
of a direct-image comparison isomorphism with its section equation, to retain
these two proved inputs. `FiniteOrdinaryPullPin` additionally retains the ordinary
pullback comparisons, mate equations and ordinary exactness. The ordinary mates
are constructed using the existing inverse-mate invertibility theorem for
equivalences; the unit-mate identity proves their equations. Conjugating exact
fixed inverse image through the realization equivalences proves preservation of
finite limits and colimits by both specified ringed pullbacks. Uniqueness of left derived functors also proves that both specified derived
counits are invertible on every complex, and this is retained in the ordinary
pin as `derivedExact`. Both new records contain explicit data types with no
postponed field.

The remaining work is separated into two independent mathematical results:
extending prescribed realizations and ordinary pullback pins to the derived,
open and tensor comparisons, and
identifying the transported canonical arrows once those comparisons are given.
The first result does not assume an Assertion or any beta/gamma equation. The
second assumes all comparison data and only proves the two map equalities.
The original DAG node's proof and proof dependencies now record this construction.
No existing statement, definition, attribute, public import, or unit route changes.

## Proved and sorry left

The original hole in
`SheafOfModules.OpenTensorNormalization.finite_compatibility` is closed by the
new combination proof. There are zero holes in the item module.

`SheafOfModules.OpenTensorNormalization.finite_comparisons_exists` and its private
helpers `finite_realization_exists`, `finite_inverse_scalar`,
`finite_direct_pin_exists`, `constant_direct_unit`, and
`corner_constant_direct_unit`, and `finite_ordinary_pull_pin_exists` are proved. These constructions are
independent of the finite comparison and compatibility holes.
`#print axioms` confirms that all six private helpers and `FiniteDirectPin` use
only `propext`, `Classical.choice` and `Quot.sound`; the comparison-existence
theorem still depends on its explicitly listed operation-comparison hole.

Two holes are added, each the entire body of a named public theorem:

- `SheafOfModules.OpenTensorNormalization.finite_operation_comparisons_exists`
  (`lem-sf-finite-operation-comparisons`): construct the pull, open and tensor
  comparisons and their remaining pins for the four prescribed realizations and
  two supplied ordinary pullback pins (including section-normalized right squares,
  ordinary mate isomorphisms and exactness).
- `SheafOfModules.OpenTensorNormalization.finite_compatibility_of_comparisons`
  (`lem-sf-finite-compatibility-transport`): identify the two transported canonical
  arrows, with all finite comparison data supplied as hypotheses.

This is a decomposition: one original hole closed and two lower holes added,
not a completed axiom-free proof of finite compatibility. The scalar preserving
realization argument is proved rather than another retained hole. There are no
holes in definitions and no new axioms.

Validation: the four delivery modules compile in import order with no warnings.
The expanded realization/direct-image construction compiles in about 12 seconds
and the item in about 37 seconds. A separate Lean check confirms that the fixed
ModuleCat-valued upperStar already preserves finite limits and colimits.
The unchanged data and geometric dependency modules were temporarily copied to
make their recent declarations available; the published dependency imports now
compile independently, and those copies have been removed from the packet.

Edge cases checked in the statements and constructions: the zero coefficient
ring is allowed (no Nontrivial instance is assumed), empty opens are allowed,
and the realization helper does not require finiteness. The restricted coefficient
rings are the literal restrictions used by finiteInput, rather than silently
substituting separately chosen constant sheaves on the opens. Comparison existence
retains the four prescribed realizations exactly; transport permits the residual
central-unit rescalings because its section, mate, unit and pure-summand pins are
all imposed together.

## No longer needed

No module or node is withdrawn, and no existing import is removed.

The finite route no longer needs the declared dependencies
`prop-weil-pbc-proetale-constant-ring-map` and
`prop-weil-pbc-proetale-constant-exact`. Constant-section preservation is proved
directly from the defining sheafification adjunction, including the literal
corner map. Exactness of the specified ringed pullback follows from its mate
comparison with the already exact ModuleCat-valued upperStar, transported through
the realization equivalences. The separate continuous-function coefficient-ring
identifications of those two nodes are therefore unnecessary here. This removes
their dependency edges from this route; it does not withdraw their modules or
claim that other consumers no longer need them.

`lem-cbc-proetale-extension-zero-base-change`,
`lem-cbc-extension-zero-projection-formula`, and
`lem-weil-pbc-conjugate-iso-unit-equation` remain needed below the canonical-arrow
transport node, rather than directly in the parent proof.

## Where the brief, the DAG or earlier work was wrong

The finite-specialization paragraph of the DAG explained uniqueness of the
canonical arrows, but did not expose a declaration constructing the four
section-preserving realizations or the pinned pull/open/tensor comparison record.
That construction is not supplied merely by knowing that constant inverse image
is exact. The realizations and the two section-normalized direct-image pins are
now proved. The remaining operation-comparison construction has its own precise
theorem and source-based argument.

The first proposed one-theorem extraction combined comparison existence and both
compatibility equations after assuming normalization. That only repackaged the
finite conclusion. It has been replaced by the genuinely separate comparison
construction and map-identification results, with an explicit proved realization
construction between them. No such repackaged theorem is in the packet.

## New nodes

`lem-sf-finite-comparisons-existence` attaches the proved construction in
`Sheaf.SixFunctors.FiniteComparisonsExistence`. Its private helper constructs
realizations by the inverse of the existing scalar restriction equivalence,
including the scalar equation, and constructs both section-normalized direct-image
comparison pins.

`lem-sf-finite-operation-comparisons` attaches the remaining construction theorem
in `Sheaf.SixFunctors.FiniteOperationComparisons`. Its input includes four
prescribed realizations and two ordinary pullback pins; its conclusion supplies the
remaining derived comparison isomorphisms, open and tensor comparisons and pins and preserves those four realizations
exactly. Its `FiniteDirectPin` definition contains actual isomorphism data and a
section equation. `FiniteOrdinaryPullPin` includes the mate comparison and exactness.
Neither definition has any postponed field.

`lem-sf-finite-compatibility-transport` attaches the remaining canonical-arrow
identification theorem in `Sheaf.SixFunctors.FiniteCompatibilityTransport`.
Its input already contains all comparison data, and its conclusion contains
only the two beta/gamma route equations.

All three nodes include statement attachments, complete proof plans, literature
sources, Mathlib searches and the original unit and blueprint ancestry.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
