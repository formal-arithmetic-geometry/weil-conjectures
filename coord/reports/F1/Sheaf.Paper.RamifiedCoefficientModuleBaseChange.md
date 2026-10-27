## What changed

Proved `WeilConjectures.RamifiedPullback.coefficientModuleBaseChange_exists` in
`Sheaf.Paper.RamifiedCoefficientModuleBaseChange`, preserving its full signature,
public import, and existing docstrings. All added helpers are private and proved.
The node now records the actual proof route.

The supplied coefficient isomorphism implies local kernel annihilation on every
extended module: localize a vanishing coefficient tensor, contract its second
factor with a module section, and use tensor generation and sheaf separatedness.
Descend the scalar action through the sectionwise surjective completed projection.
The two extension/restriction adjunctions give inverse comparison maps; their
unit formulas give the prescribed pure-tensor normalization. The scalar functor's
existing object equality transports the result to the statement's exact objects.

Proof imports are `Sheaf.SecSmoothPurity.CochainCoefficientArrows`,
`Sheaf.Paper.CompletedIntegralFiniteQuotientHomExt` (with `import all` to reuse its
proved private `AlgebraicGeometry.ProEtale.constantQuotient_surjective`), and
`Mathlib.RingTheory.Ideal.Maps` for `RingHom.liftOfSurjective`. The completed
projection's surjectivity follows from that quotient helper and `limit.lift_π`.
No definition or statement in any other module changes.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.RamifiedPullback.coefficientModuleBaseChange_exists`
(node `lem-weil-ramified-coefficient-module-base-change`).
Added 0 holes; split off 0 statements. The item has 0 textual `sorry` occurrences. The complete module compiled cleanly
through `lcompile.py` in 42.3 seconds, with no warnings.
Every private helper is proved; no new axiom or data chosen from an unproved
existence theorem is introduced. The descended action is explicitly the quotient
of the proved endomorphism ring action, and the comparison maps are constructed
by existing proved adjunctions. The final family is chosen only after its
normalized isomorphisms have been proved to exist.

## No longer needed

The proof does not need `lem-pur-change-of-rings-tensor-cancellation-independent`
(`Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients`),
which was a planned proof dependency. It is removed from this node's proof route;
its continued use by other modules is unaffected. No existing import line is
removed: the original module had only its required public data import.
The exploratory `Sheaf.Paper.RamifiedFiniteTensorSections` import was replaced by
the smaller direct proof import of `CochainCoefficientArrows`, whose normalized
adjunction is what the proof uses. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The original associator and
B-linearity plan is valid, but the sectionwise surjectivity of the completed
projections provides a direct kernel-descent route, avoiding another split of
the same obligation. The zero module, the empty site, and a zero coefficient
quotient satisfy exactly the same tensor, quotient-action, and adjunction
identities; the proof adds no flatness or ramification-positivity hypothesis.
The actual unit route and all public signatures are preserved.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
