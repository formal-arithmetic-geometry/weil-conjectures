## What changed

Proved `WeilConjectures.GeneratorReduction.affineTreeCompleteDetection` with its
original statement. All Lean changes are confined to the item module. Added
private proof imports and proved private helpers for unrestricted-target ordinary
restriction, transport of the canonical completion unit, affine-cover reflection,
finite point-cover admissibility, path immersions and structural tree induction.
The node proof now records those constructions.

The arbitrary-base step reuses the existing private constructions through
`import all`; it does not modify any shared interface. Restriction of the global
unit is tested at leaves by the stated completeness hypotheses, transported by
exact derived composition, combined up the tree, and detected globally on affine
opens. The affine-cover step applies the general ringed-pullback underlying-sheaf
comparison to the slice-restriction adjunction.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.GeneratorReduction.affineTreeCompleteDetection`
(`lem-sf-affine-tree-complete-detection`). Added zero holes. No `sorry` remains in
the item or in the delivery. Existing dependency theorems remain unchanged.

Validation: remote single-file compilation passed without warnings in 18.9 seconds.
The delivery command also runs the server preflight before pushing.

## No longer needed

No original public import or planned proof dependency was removed. No module is
withdrawn. The finite-index tree theorem is not applied: only its proved empty
scheme helper is reused. The structural induction is written directly for
`QcqsOpenClosedTree`, and does not impose invertibility of ell on the scheme.
The affine step needs neither chart-specific private comparisons nor a direct
import of `OrdinaryCompletedCoverDetection` or `CompletedCoefficientRingedCoherence`.
Those modules remain indirect dependencies of existing local-detection results;
this delivery does not claim they can be withdrawn.

## Where the brief, the DAG or earlier work was wrong

The three planned theorem statements alone do not supply the full arbitrary-base
argument: the ordinary restriction models and local conservativity statements
assume qcqs targets, whereas X in this item is arbitrary. The underlying private
constructions and the immersion algebraic-limit theorem already work without
that restriction. This delivery assembles their unrestricted variants privately
and proves affine-cover reflection explicitly, so no shared signature is changed
and no further version of the original obligation is split off.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
