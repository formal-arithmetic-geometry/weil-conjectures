# System tensor mate proof support

## Reason

H8 fills seven original proofs in `Sheaf.Paper.SystemTensorMateArrows`.
The preflight requests this record because its command comparison detects scoped
namespace openings and private instances as potential interface changes.

## Old

`system_kInjective` and `laxTensor_existsUnique` had postponed proofs and no
declaration-scoped namespace openings. The module did not contain the three
private instances listed below or the private coefficient and adjunction helpers.

## New

Every existing declaration signature, definition body, public import, visibility,
and instance attribute is preserved. Seven theorem bodies are proved. Three
original theorem holes remain; no holes or public declarations are added.

The added declaration wrappers are `open SheafOfModules in` for
`system_kInjective`, and `open CategoryTheory.MonoidalCategory in` for
`laxTensor_existsUnique` and private tensor helpers. These affect name resolution
within the enclosed declaration only. Both backward transparency options are
locally set to true for selected new proofs. Local irreducibility attributes for
`coefficientSequenceCommRingSheaf` and `laxTensorPresheaf` are scoped by sections.
They avoid repeatedly unfolding the coefficient construction during elaboration.
The module's pre-existing global options are unchanged.

The instances `commRingSheafify`, `openComposition_continuous`, and
`openBase_continuous` are all declared `private instance`. They provide local proof
support for existing sheafification and continuity facts. The last one refers to
the new private site functor `openBase`. None is an exported instance.

The three added imports are proof imports without `public`. All new helpers are
private and completely proved. The existing DAG node records the implemented
proofs and the dependencies of the three remaining original obligations; its
statement and Lean attachment are unchanged.

## Users

The read-only downstream audit, including name searches for `system_kInjective`
and `laxTensor_existsUnique`, found these three downstream modules:

| Module | Effect |
| --- | --- |
| `Sheaf.Paper.FiniteFreeCompactComposition` | Identical public interface and meaning. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | Identical public interface and meaning. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | Identical public interface and meaning. |

Neither theorem name occurs in a downstream source. No consumer is edited, no
forced adaptation is needed, and no target statement or definition meaning
changes. All source-library modules are untouched.

## Validation

The complete item module compiled without diagnostics in 38.1 seconds through
`lcompile.py`. The delivery performs the independent server preflight and axiom
audit. This record resolves the preflight's request for documentation of the
declaration-scoped commands; it does not authorize a mathematical interface change.

## Status

landed 20261020T211733-L-3495395 2026-10-20 (merge of deliver/H8/Sheaf.Paper.SystemTensorMateArrows)
