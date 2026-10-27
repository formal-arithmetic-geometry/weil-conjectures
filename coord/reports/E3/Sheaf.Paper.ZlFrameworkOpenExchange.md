## What changed

In `Sheaf.Paper.ZlFrameworkOpenExchange`, prove
`WeilConjectures.ZlFrameworkPbc.frameworkOpenMate_isIso` from the existing
`WeilConjectures.IntegralScalarExchange.openInverse_isIso`. Add its module as a
private proof import. The completed coefficient composition law and the chosen
Cartesian open square discharge its hypotheses. Reversal of the compositor word
identifies its square with the framework square. All declaration signatures,
existing docstrings and definitions stay unchanged.

Update `def-zl-framework-open-exchange` to record that proof and its dependency.
No other module is edited; no new statement or definition is introduced.

Validation: the item compiled through `lcompile.py` in 20.4 seconds. The first
delivery preflight compiled in 18.7 seconds and requested removal of one
tactic-sequencing style warning; that warning is corrected in this packet.
The delivery tool runs the final preflight.

## Proved and sorry left

Close 1 of the item's 4 holes:
`WeilConjectures.ZlFrameworkPbc.frameworkOpenMate_isIso`.
This is a proof from an existing named dependency, whose own proof remains an
independent stage-3 item; it is not a claim that the resulting axiom closure is closed.

The following 3 holes remain unchanged, all attached to
`def-zl-framework-open-exchange`:

- `WeilConjectures.ZlFrameworkPbc.frameworkOpenPullRealization_existsUnique`.
- `WeilConjectures.ZlFrameworkPbc.frameworkTowerOpenMate_isIso`.
- `WeilConjectures.ZlFrameworkPbc.frameworkAmbientExchange_strict`.

Holes added: 0. No split-off statements.

## No longer needed

None. No existing import, module, node or unit step is removed.
The existing quotient-augmentation and coefficient-composition dependencies are
still used. The arbitrary coherent-coefficient open-mate result supplies the
shorter route for the ordinary derived mate; it does not remove the strict-tower
or whole-realization obligations.

## Where the brief, the DAG or earlier work was wrong

The prior node grouped all four remaining obligations without naming the existing
arbitrary-coherent-coefficient open-unit mate theorem. That theorem already has
exactly the required completed-ring specialization, so a new sectionwise proof
or a new intermediate statement is unnecessary for the ordinary mate.
The theorem includes all Cartesian open squares, hence empty opens, identity
squares and zero complexes; the specialization adds no hypothesis.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
