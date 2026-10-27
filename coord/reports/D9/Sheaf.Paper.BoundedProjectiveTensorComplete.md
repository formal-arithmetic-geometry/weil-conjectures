## What changed

Implemented `WeilConjectures.bounded_projective_tensor_complete` without changing its
signature, hypotheses, universe parameters, definitions or public imports. Its proof
now derives every bounded-complex and tensor conclusion from two separate source facts:
normalized exactness of quotient completion, and its rank-one coefficient calculation.

The private proved helpers establish finite-product/retract completeness by the adopted
`DerivedCategory.FlatDevissage`, closure of finite sheaf retracts under finite biproducts
and tensor products, finite support for totalization, and site flatness. The totalization
argument constructs the maps to and from the finite sum of nonzero tensor summands;
it does not replace the sheaves by constant projective coefficient modules.
`KFlatTotalTensorModel.kFlat_total_tensor_model` supplies the existing K-flat tensor
representative comparison. The proof uses only private proof imports for these tools.

Added `Sheaf.Paper.IntegralQuotientCompletionExact` and
`Sheaf.Paper.CompletedCoefficientUnitComplete`, each with one source statement,
one named hole, a full proof in words and its own DAG node. These are separate parts of
the argument (former steps 3--5 and step 6), not copies of the bounded-projective theorem.
Neither asserts any of its bounded-complex or tensor conclusions. They use the existing
completion and its actual normalized unit throughout.

Validation: `lcompile.py --all` compiled all three modules; the assigned module took
33.6 seconds and has zero holes. Both new statement modules also compiled (8.2 and
7.5 seconds). The final packet is a decomposition with two outstanding source results.
No definitions or existing consumer interfaces were modified.

## Proved and sorry left

Closed the original hole in `WeilConjectures.bounded_projective_tensor_complete`
(node `lem-fix-bounded-projective-tensor-complete`) by a complete Lean proof from
the two source obligations and existing declarations. There are zero holes in the
assigned module.

The following two new holes remain:

- `WeilConjectures.integralQuotientCompletion_exact`, in
  `Sheaf.Paper.IntegralQuotientCompletionExact`, node
  `lem-sf-integral-quotient-completion-exact`.
- `WeilConjectures.completedCoefficientUnit_completionUnit_isIso`, in
  `Sheaf.Paper.CompletedCoefficientUnitComplete`, node
  `lem-sf-completed-coefficient-unit-complete`.

Local accounting is one old hole closed and two new holes added. This is a decomposition,
not an axiom-free proof or a claim of positive net hole progress. All five private
finite-retract helpers are proved. There is no hole in a definition and no added axiom.

Edge cases: finite products with rank zero are handled by finite-biproduct APIs;
an empty support interval is allowed; the zero complex and degrees outside support
are handled by `IsZero`; no compatibility of a term's chosen splitting with the
differential is assumed. The integer interval indexing the total degree is finite,
including when it is empty. The new coefficient calculation fixes the actual quotient
augmentation, not merely an arbitrary isomorphism of its source and target.

## No longer needed

No existing public import was removed, and no module is withdrawn. The original tensor-colimit and bounded-flat proof imports stay. The following original
private imports are removed from the assigned module (their source obligations are
recorded in the new nodes where still needed):

- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Mathlib.CategoryTheory.Localization.CalculusOfFractions`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatScalarTowerRealization`
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`
- `Sheaf.Algebra.Homology.RoosConeCalculus`
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`
- `Sheaf.Paper.CompletedFreeCellOrdinaryLimit`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`

Temporary exploratory proof imports are also absent from the delivered Lean files.

Direct uses of `lem-pe-roos-cone-calculus`, `lem-pc-tensor-mapping-cone-iso`,
`lem-pc-kflat-resolution`, `lem-pur-derived-change-of-rings`,
`lem-pur-left-derived-from-kflat-class`, `lem-weil-pbc-localization-universal-property`,
`lem-sf-completed-free-cell-ordinary-limit` and
`lem-weil-proetale-surjective-tower-derived-limit` are grouped under the two new
source results. These nodes remain needed; they are not claimed as pruned.

The proof no longer needs the following original planned dependencies:

- `lem-pe-kflat-scalar-tower-realization`: the exactness obligation uses the native
  module quotient tower and the existing normalized completion comparison directly.
- `lem-pc-right-fraction-representation` and `lem-pur-quasi-iso-cone-acyclic`:
  the resolving-class derived-functor theorem handles exact descent; a second
  bespoke roof-and-good-cone proof is unnecessary.
- `lem-sf-triangle-morphism-iso` and `lem-weil-pbc-complex-ses-triangle`:
  the adopted proved `DerivedCategory.FlatDevissage` already implements the bounded
  stupid-truncation induction, so these extra Sheaf wrappers are unnecessary here.

The parent `proof` and `proof_deps` record this route. The obsolete scalar-tower-realization
`tool_uses` entry was removed; all other existing approvals keep their order.
The new total-tensor tool is declared in
`split_report.tool_uses`. No unrelated declaration or source-library module was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The bounded finite-projective
argument is valid for the independently sized coefficient and site universes as written.
The source library already proves the generic bounded devissage and the K-flat total
tensor model, which substantially shorten the proposed proof.

The two remaining obligations require normalization glue not stated as a ready-to-apply
lemma: exactness must use the same coherent shifts as the actual completion unit,
and the ordinary-limit coefficient calculation must identify that unit, including its
zero shifted coordinate. The new statements isolate these two source results.
The separate principal-completion exactness interface uses another coefficient model
and does not directly specialize to the independently sized `IntegralOnSlice` interface.

## New nodes

`lem-sf-integral-quotient-completion-exact` records exactness and shift compatibility
of the actual quotient completion and its unit, from Stacks 06XN/05SE and the signed
Roos cone calculus. Its proof contains no completeness assumption about any object.
Its Lean module is `Sheaf.Paper.IntegralQuotientCompletionExact`.

`lem-sf-completed-coefficient-unit-complete` records the rank-one coefficient calculation,
from the completed-free-cell ordinary limit and pro-etale surjective-tower theorem.
It is independent of the exactness obligation and asserts nothing about arbitrary
bounded complexes. Its Lean module is `Sheaf.Paper.CompletedCoefficientUnitComplete`.

Both nodes have independent Lean statements, source citations, proof steps, dependency
unions, blueprint provenance and three kinds of Mathlib search. No change record is
needed because no existing signature or definition changed.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
