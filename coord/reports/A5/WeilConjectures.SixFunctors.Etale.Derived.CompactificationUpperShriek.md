## What changed

Marked the existing instance
`AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`
with a `STATEMENT-DISPUTED` comment. Every original signature, attribute, public import,
non-theorem body and proof body is preserved. No mathematical proof progress is claimed.
No other library file is changed.

The unrestricted source assertion conflicts with the active interface in
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`: its implementation notes explicitly
reject an unconditional adjoint for arbitrary coefficients, its general construction takes
an adjoint-existence hypothesis, and its unconditional instance uses finite module
coefficients through `LowerShriekLeftAdjoint`. The assigned legacy instance has no such
hypothesis. This packet registers that contract conflict without silently weakening it.

Read the current module, the earlier F4, H1 and G8 reports and change records, the G8
maintenance report, the corrected coproduct node, the analogous pro-etale node, and the
current blueprint coproduct proof. There is no rework row or current numbered A5 return.
The source-library boundary forbids repeating the historical namespace retirement.

Validation: scratchpad/BrownReduction.lean compiles cleanly through lcompile.py and proves
three diagnostics. `adjoint_iff_coproducts` identifies the exact requested property with
preservation of every coproduct indexed in Type (u+1), using the derived pullback/pushforward
adjunction to construct the triangulated structure and applying Brown representability.
`adjoint_of_acyclic` proves the general reduction from (i) preservation of exact complexes of
direct-image-acyclic sheaves and (ii) coproduct preservation by every classical higher direct
image. Both have only propext, Classical.choice and Quot.sound in their axiom audits.
`adjoint_of_torsion` proves the proper specialization for ModuleCat Λ under IsAddTorsion Λ,
with neither finiteness nor Noetherian assumptions. Its audit also lists sorryAx inherited
from the existing geometric theory. These diagnostics contain no direct holes and are
scratch files, not new library assumptions or purported proofs of the original instance.

Searches: LeanFinder returned underived module-sheaf and site adjunctions, not the requested
unbounded general-coefficient theorem. Loogle did not resolve its queried identifier.
The msearch grep query returned no match. Direct rg searches found the existing torsion
proper coproduct theorem and its finite-coefficient Brown application, but no theorem
establishing the unrestricted geometric inputs. The corrected historical dependency is
not used at hypotheses it does not have.

## Proved and sorry left

Original holes closed: 0 of 1. Added holes: 0. Split off: 0.

The sole original hole remains exactly as received:
`AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`.
There is currently no DAG node attached to this module. Marking a statement disputed is
not a proof and does not reduce the hole count. No new theorem or node moves this hole.
The compiled conditional and torsion-specialized scratch proofs are not counted as
closing the unrestricted assertion.

## No longer needed

None. No import, declaration, namespace, module, node or dependency is pruned. The source
API is retained in full, including its original hole. The active finite-coefficient route
through compactification, proper coproduct preservation and Brown representability stays.
The pro-etale ambient counterexample is not transferred to the etale site: it concerns
sheaves that are not of etale origin and does not refute this particular assertion.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the unrestricted legacy instance and the active source interface have
incompatible contracts. This is not a claim of a Lean-certified counterexample. Neither
failure to find a proof nor a missing torsion hypothesis alone is treated as a refutation.
A source-supported resolution of the actual generic coefficient assertion is needed.

The promised numbered plan is absent: no current dag/nodes file has lean.module equal to
the assigned module, and no node names the assigned etale instance. The historical node
`lem-etale-proper-derived-lower-star-coproducts-for-grothendieck` was corrected on 2026-10-18
from arbitrary Grothendieck coefficients to finite commutative module coefficients on
Noetherian quasi-compact schemes. Its Lean attachment now names the existing theorem in
Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts. It cannot supply the missing
generic input. The stronger upstream proper coproduct theorem removes the scheme
restrictions but still assumes ModuleCat Λ and IsAddTorsion Λ.

The current blueprint proper-coproduct proof uses the torsion cohomological-dimension
bound. Brown representability supplies the formal last step, not that geometric bound
for arbitrary A. The unit and chapter route are unchanged, and no new unsupported
arbitrary-coefficient lemma has been introduced.

The prior G8 delivery already recorded this dispute. The subsequent upstream-verbatim
restoration removed its comment. coord/reports/maintenance/G8-CompactificationUpperShriek.md
records a previous stale dispatch of this same unused source hole and says no fresh
mathematical delivery was needed then. This assignment is again present in the current
queue, so this packet reports its actual restored source state through the normal review
mechanism instead of changing queue scripts or restoring the rejected generic split.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
