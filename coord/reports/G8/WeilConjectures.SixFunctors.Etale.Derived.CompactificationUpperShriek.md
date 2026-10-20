## What changed

Marked the original instance
`AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`
as `STATEMENT-DISPUTED` in its docstring. Its signature, visibility, instance attribute,
proof body, public imports, and all other declarations remain unchanged. This is a
statement-dispute delivery for independent review, not a proof delivery or a definition repair.

The assigned assertion conflicts with the adopted source's active interface:
`lean/WeilConjectures/SixFunctors/Etale/Derived/UpperShriek.lean`, implementation notes,
explicitly says that the unrestricted assertion is not true for arbitrary coefficient
categories and therefore assumes `[(R(f)_![A]).IsLeftAdjoint]` in its general-coefficient
construction. Its torsion-module instance instead uses `LowerShriekLeftAdjoint`.
The legacy instance assigned here has neither that assumption nor a coefficient restriction.
I am reporting this conflict for review, not claiming to have exhibited a counterexample.

Retained the earlier attempt and its rejected split in `scratchpad/`. No rejected
arbitrary-coefficient coproduct axiom has been restored. Checked the current source,
claim, rework and return records before editing; the item is present and held by G8,
and there is no corresponding quarantine restoration or numbered return to perform.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split off: 0.

The original hole remains, with its original body:
`AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`.
No theorem is claimed proved by marking the statement disputed.

The retained scratch diagnostics have complete proofs and are not delivered as library
assumptions. `BrownCriterion.lean` proves that, for the assigned functor, the requested
property is equivalent to preservation of all coproducts. `AcyclicBrownReduction.lean`
proves the implication from the following two geometric inputs to the requested property:
(1) direct image preserves exactness of unbounded complexes of direct-image-acyclic
sheaves; (2) every classical higher direct image preserves coproducts.
`FiniteCoefficientBrown.lean` proves the requested property for every torsion commutative
module coefficient ring and arbitrary proper morphism, using the existing upstream
coproduct theorem. Despite its historical filename, this last diagnostic needs neither
finiteness of the ring nor Noetherian or quasi-compact hypotheses on the schemes.
It does require `ModuleCat Λ` and the explicit hypothesis `IsAddTorsion Λ`.
The general two-input reduction compiled in 4.8 seconds with only `propext`,
`Classical.choice`, and `Quot.sound`. The torsion-module specialization compiled in
5.0 seconds; its axiom report includes `sorryAx` from existing geometric dependencies.
Neither diagnostic contains a direct hole. These conditional and specialized proofs do
not establish the unrestricted instance.

## No longer needed

None. No source declaration, module, DAG attachment, or import is removed. In particular,
the earlier retirement of this namespace is not repeated. The source-library boundary
requires retaining its declarations, even though the active interface takes adjoint
existence as a hypothesis.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: The unconditional arbitrary-Grothendieck-coefficient assertion
conflicts with the active source interface and exceeds the available geometric lemmas.
The implementation note in `UpperShriek.lean` is an explicit reason to dispute its
intended validity. It is not itself a formal counterexample, and this report does not
infer falsity merely from the absence of a proof or a torsion hypothesis.
Independent review should resolve which source contract is intended before another
worker is asked to prove the unrestricted instance. No weakening is proposed or made.

There is currently no DAG node with `lean.module` equal to the assigned module. The
readiness pipeline still dispatches it as a stage-3 proof item: `Dag.waiting` considers
attached stated nodes, so a source module with no attachment has no missing-dependency
entry, and `queue.stage3` admits it. This fails to supply the promised numbered plan
and general-coefficient proof dependencies. No queue or launcher script was modified.

The historical node `lem-etale-proper-derived-lower-star-coproducts-for-grothendieck`
was explicitly corrected on 2026-10-18 from arbitrary Grothendieck coefficients to
finite commutative module coefficients on Noetherian quasi-compact schemes. Its current
attachment is `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts`, declaration
`AlgebraicGeometry.Etale.proper_rightDerivedLowerStar_preservesCoproducts`.
It cannot supply the unrestricted assertion. The stronger upstream theorem
`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`
drops the scheme restrictions but still requires a torsion module coefficient ring.

The current blueprint, `sec-six-functors-basics/sk-prop-ctf-finite-proper/` under
`literature/blueprint/main-20261015/blueprint/`, specifies finite coefficients and uses
the torsion cohomological-dimension bound. In `literature/stacks-project/etale-cohomology.tex`,
Lemma `lemma-cohomological-dimension-proper` assumes torsion abelian sheaves and Lemma
`lemma-proper-mod-n-direct-sums` (Tag 0F11) treats Z/nZ coefficients. Brown representability
(Tag 0F5Y) is the formal final step; it does not establish the missing geometric input.

The previous attempt correctly rejected its unsupported split, but ending with a
readiness-tool blocker left the mathematical statement conflict unregistered. The
normal delivery mechanism explicitly accepts a newly marked statement dispute and
routes it to independent review. This delivery uses that mechanism without claiming
proof progress, adding a replacement assumption, or changing a source signature.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
