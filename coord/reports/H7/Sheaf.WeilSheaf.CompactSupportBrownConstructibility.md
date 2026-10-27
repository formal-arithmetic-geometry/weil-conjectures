## What changed

Replaced the proof hole in
`AlgebraicGeometry.nativeBrownRight_preserves_weilComplex` with a proof of its unchanged
statement. Added a proved private geometric assembly lemma in the same module.

The geometric assembly base changes the chosen compactification to the algebraic closure,
packages the finite field as a `FiniteFieldDatum`, and uses the existing coefficient
construction and compact-support realization. It applies the existing geometric Brown
comparison with the realization's actual common-stage action and its adjunction.

The native argument restricts the specified free/forgetful derived adjunctions to the
localizing hulls, restricts the normalized invertible induction comparison, composes the
adjunctions, and applies `Adjunction.rightAdjointUniq`. The resulting isomorphism transports
geometric constructibility. `WeilComplex.objectProperty_iff` proves both the input and output
forgetful criteria. There is no change to a statement, definition, public import or consumer.

Added proof imports of `NativeWeilDerivedInductionComparison`,
`NativeGeometricBrownConstructibleComparison`, the new
`CompactSupportStageActionAdjunction`, Mathlib adjunction restriction and uniqueness, and
`WeilConjectures.WeilSheaf.Localization`.

Validation: `lcompile.py --all` compiled both packet modules without warnings. The existing
public theorem signature was compared verbatim with the repository source and is unchanged.
The new node signature matches its Lean statement, and its dependency closure does not
reach the parent item.

## Proved and sorry left

Original holes: 1. Closed upper hole:
`AlgebraicGeometry.nativeBrownRight_preserves_weilComplex`
(node `lem-sf-native-brown-right-constructible`). Its proof body has no `sorry`.

Added holes: 1, in
`WeilConjectures.LocallyFiniteAdicCompactSupport.compactSupport_stageAction_isLeftAdjoint`
(node `lem-sf-compact-support-stage-action-adjunction`). This is the only `sorry` in the
packet. Thus this is a decomposition, with net hole change zero, rather than an axiom-free
proof of the whole dependency closure.

The residual statement is only coefficient-stage adjunction descent for an already supplied
normalized `StageAction`. It mentions neither Brown adjoints nor Weil complexes, localizing
hulls, nor preservation of constructibility. It supplies the common-stage adjunction needed
by the geometric comparison. Its docstring and node give the right finite functors, their
invertible scalar transitions, the tower law and descent of the finite units and counits.

The private `nativeGeometricRight_constructible` helper is proved, with no separate hole.

## No longer needed

None. No original import was removed and no original dependency was pruned: the native
framework criterion, free-derived adjunction, native localizing hulls and Brown adjoints,
normalized induction comparison, and geometric constructible comparison are all used.
No unit statement or step was bypassed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The geometric comparison theorem is conditional on supplied compatible realizations,
a common-stage adjunction, and their compact-support comparison. It does not by itself
instantiate those data for the given finite field and compactification. The new proof
assembles the geometric data from the existing realization and coefficient construction;
the remaining missing interface is descent of the rational adjunctions to the precise
`StageAction.system.functor` returned by realization. The separate generic
`StageSystem.Morphism.adjunction` requires a right stage morphism and compatible unit/counit
records, so it does not directly close this interface.

The auxiliary coefficient closure in the realization API is lifted to the scheme universe,
but its common-stage action and the geometric comparison use unlifted `PadicAlgCl`.
The residual theorem retains this distinction and uses only the auxiliary construction's
rational operations on the actual finite subfields. No equality between the lifted and
unlifted common-stage categories is assumed.

Edge cases: zero inputs and empty schemes are included by the adjunction identities;
identity and repeated field extensions use the same scalar tower equations. Only relative
separatedness of f is used. No absolute separatedness of X or Y is added.

## New nodes

`lem-sf-compact-support-stage-action-adjunction` records the one remaining coefficient
assembly step, in `Sheaf.Paper.CompactSupportStageActionAdjunction`. It is strictly below
the geometric comparison application: after it, all geometric and native assembly in the
item is proved in Lean. Mathlib searches found generic adjunction and colimit results, but
no theorem for this project's normalized stage action. The existing generic stage-adjunction
descent theorem is explicitly a proof dependency of the new node.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
