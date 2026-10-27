## What changed

Restored the archived IntegralExpressionRecursion item, preserving its theorem type
and every existing specification definition. Relocated its 19 data/specification
declarations verbatim into IntegralExpressionRecursionData and retained their public
availability from the original module. The change record is
coord/changes/T2-integral-expression-recursion-data.md.

Constructed coefficientTransformation by recursion in the natural transformation
category, with separate tensor branches and the actual compactification open/proper
composite. Proved coefficientTransformation_app. Constructed transposeComparison
explicitly from the actual adjunction unit and total-limit image, and proved
transposeComparison_coefficient using the inverse hom-set equivalence.

Constructed canonicalComparisons as the inverse of that specified natural
transformation once its components are known invertible. Proved its whole-system
coefficient identity. The original theorem now combines the three strictly smaller
component obligations with this construction and coefficient calculation.

The data relocation is for acyclic dependencies, not a response to a compile-time
failure. The two newly constructed transformations have irreducible attributes and
explicit component lemmas to avoid unfolding the recursive implementation during
elaboration. No existing definition receives a new irreducible attribute.

Validation: lcompile.py accepted all five delivered modules, including the complete
support proof and original theorem. It also accepted both direct importers,
IntegralRealizationAssemblyData and IntegralComparisonRecursionLaws, unchanged
against this set, with no warnings. Their temporary sandbox copies were removed.
The original theorem type and relocated specification block were checked byte for
byte against the archived item.

## Proved and sorry left

This is a decomposition, not a net proof: one original hole closed, two holes
added. The original module has zero holes. Every name below lies in namespace
WeilConjectures.IntegralSystemRealization.ExpressionRecursion.

Closed: integralExpressionRecursion, from the following separate obligations.
Proved without a local hole: coefficientTransformation_app,
transposeComparison_coefficient, canonicalComparisons_coefficient, and
canonicalComparisons_support.
The comparison statements depend on the named invertibility theorem through the
constructed inverse; the support proof also uses canonicalComparisons_equations.
No definition has a sorry, and no arbitrary data is selected from an unproved
mere-existence statement.

Remaining holes, each in its own new module, with a source and complete proof in words:

- transposeComparison_isIso: lem-sf-integral-expression-transpose-is-iso.
- canonicalComparisons_equations: lem-sf-integral-expression-canonical-equations.

The first concerns only invertibility of a fixed map. The second identifies the
explicit inverse with the recursive formulas. Neither repeats the original
existential statement. The coefficient identity is fully formalized.

canonicalComparisons_support has a complete proof from the equations. The private
unaryA_reduction helper cancels the input unit/counit using naturality of the
primitive comparison. The private properA helper identifies proper counit transport
with model.push by its naturality and the other triangle identity. The compactification
proof applies these to the open/proper equation and uses dc.normalization directly.
Its whole-system equality requires no separate tower-limit or projection theorem.

Edge cases checked from the constructions and hypotheses: a leaf is the actual
unit transpose; an empty input index has no expression in this grammar; repeated
variables work through prod' of natural transformations with the same source;
empty full domains give natural isomorphisms componentwise; identity/empty open
immersions impose no additional conditions; zero inputs and identity quotient
transitions use the same actual functors and system morphisms. Good transport in
the component proof plans keeps both common intervals and all origin squares.

## No longer needed

Removed the three original proof-only imports:

- Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
  (lem-weil-ringed-tower-pushforward-limit-comparison).
- Sheaf.Paper.CompletedCoefficientPushforwardComparison
  (lem-pur-completed-coefficient-pushforward-comparison).
- Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
  (lem-sf-compact-support-restriction-of-scalars).

These three lemmas are not needed again to identify the direct comparison:
DirectComparisons already includes the actual whole-system open/proper normalization
and all finite projection equations. The support obligation uses that supplied
normalization, primitive specifications, naturality and the triangle identities.
The two obsolete tool_uses approvals for the ringed tower comparison and compact
support restriction are removed from this node. This does not claim global
withdrawal of these modules; they can still be used elsewhere, including inside
the underlying operation definitions.

The remaining original planned dependencies remain through the specifications or
the smaller proofs: expression-domain, system operations, basic realization,
evaluation calculus, and integral/rational compact-support definitions. No unit
statement or unit proof route is bypassed; the item's unit has no realized entries
requiring a different construction. No Lean module or DAG node is deleted.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined in rework.tsv; its absence from lean was not evidence
that it was withdrawn. The archived module compiled unchanged before proof work.
Its complete Lean attachment and all definitions have been preserved by restoration
and reexport, with declaration ownership recorded on the new data node.

The original DAG unnecessarily rederived tower normalization already assumed by
DirectComparisons. The proof can use the given actual map equality directly.
The transpose construction also makes a separate induction for the coefficient
identity unnecessary: it is the hom-set equivalence's inverse identity.

No statement is disputed or weakened. The original l != D.p hypothesis remains
verbatim even though the assembly uses only the supplied Primitives and
Reconstruction assumptions.

## New nodes

- def-sf-integral-expression-recursion-data: verbatim relocated specifications,
  explicit natural coefficient recursion, its component formula, explicit adjunction
  transpose and its proved counit identity.
- lem-sf-integral-expression-transpose-is-iso: invertibility on the exact intermediate
  domain, plus the uniquely determined inverse comparison and its coefficient lemma.
- lem-sf-integral-expression-canonical-equations: identification of that fixed inverse
  with the displayed finite-tree recursion and its domain witnesses.
- lem-sf-integral-expression-canonical-support: proved identification of its single-input
  compactification branch with the direct comparison using the supplied normalization.

Change record: coord/changes/T2-integral-expression-recursion-data.md.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
