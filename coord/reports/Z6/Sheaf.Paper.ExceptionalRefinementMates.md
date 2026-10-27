## What changed

The item keeps its theorem signature and the node's mathematical statement. Its one theorem body is
now a complete assembly from two smaller geometric statements. The assembly uses the existing proved
refinementComparisonOfLeft, proves both transpose formulas directly from Mathlib conjugation, and
proves right_coefficient_square_of_left in ExceptionalRefinementRightSquare by inverse-Hom
transposition. That lemma derives the right localization and common-field descent equations from
their left squares and the four fixed counit equations. It introduces no geometric assumption.

Existing records and construction maps move into ExceptionalRefinementTransportData,
ExceptionalRefinementMatesData and ExceptionalRefinementSystemData, publicly re-exported by the
item, so the new obligations use them without an import cycle. This separation follows profiling and
explicit-instance/universe fixes: the large generated dependent-record checks are compiled
separately. The new LeftMates record contains only left comparisons, their shifts, ring
normalization and left descent equations. Existing definitions other than Transport retain their
mathematical data. The inclusion shift instance proof is explicit at each ring stage.
reducedInputShift explicitly composes the canonical full-subcategory inclusion shift with
reductionShift, and SystemRealization.realizationShift has a let-bound instance selecting exactly
that inclusion shift; its displayed equality is unchanged. No source-library module is changed.

Transport is repaired to mean the actual common-field transport required by the existing node. It
gains the integral compact-support scalar comparison fixed by the concrete whole system scalar map,
its raw rational localization, and the closed left functor's action on cross-field transition arrows
through these same comparisons. These fields do not mention a refinement or assert one exists. The
change is explicit: the old weaker record did not formalize the node's prescribed common-field
transport. See coord/changes/Z6-exceptional-refinement-common-transport.md for old/new definitions
and users. No existing Lean importer or external namespace user exists; a source search of both
roots found none, so there are no forced adaptations or existing consumer compiles.

Elaboration keeps respectTransparency enabled. Coefficient universes and inherited inclusion shift
instances are supplied explicitly; the large ambient derived category and constant sheaf remain
locally irreducible. No shared reducibility attribute changes.

Validation: all seven delivered modules passed server compilation through lcompile.py. The
final assembly compiled cleanly in 20.3 seconds. The delivery command additionally runs its
required preflight and axiom probes; its results are recorded with the delivery.

## Proved and sorry left

One original textual hole is replaced:
WeilConjectures.ExceptionalRefinement.exceptional_refinement_mates
(lem-sf-exceptional-refinement-mates). This is a decomposition, not a proof without remaining
assumptions: the repaired intended statement is proved from two new smaller obligations. The old
under-specified Transport assertion is not claimed proved unchanged.

Two holes are added, each exactly the whole proof of a public theorem in its own module:

- WeilConjectures.ExceptionalRefinement.exceptional_refinement_left_construction
  (lem-sf-exceptional-refinement-left-construction): only the geometric left comparisons, their
  shifts and normalizations; no right maps, adjunction equations or system package.
- WeilConjectures.ExceptionalRefinement.exceptional_refinement_system_realization
  (lem-sf-exceptional-refinement-system-realization): the strict-system lift of an already
  normalized comparison; no existence or descent of stage comparisons.

The item and all three data modules have zero remaining sorry. The delivery has exactly two. The
public right_coefficient_square_of_left lemma is fully proved. No axiom or hollow definition is
introduced. Net textual holes closed minus added is 1 - 2 = -1; this is not claimed as net proof
progress.

## No longer needed

The assembly removes the direct proof imports ExceptionalFiniteOperations,
CompactificationCoherence, RefinementCoefficientMate, SemilinearDerivedSections,
ExceptionalSystemTransport, DiagramOpenClopenShiftModels, IntegralRealizationShiftCoherence,
SystemProperOpenScalarSquare, ExceptionalFieldDescent and Mathlib.CategoryTheory.Shift.Adjunction.
The public imports IntegralCompactificationSystemRealization and SystemProjectionFormulaCoherence
are replaced with their definition owners IntegralCompactificationRealizationData and
SystemProjectionFormulaMaps. The other two original public imports remain. No existing consumer
relies on the removed theorem imports. The geometric results remain proof-plan dependencies of the
appropriate new obligations; removing their direct assembly imports does not claim their mathematics
has been pruned.

The original exceptional integral scalar mates result (lem-sf-exceptional-integral-scalar-mates) is
not needed for this refinement construction: the repaired input directly retains the canonical
compact-support scalar maps, and right localization/common descent follows from the proved
right_coefficient_square_of_left calculation. Similarly, lem-weil-pbc-mate-pasting is not required
as a separate black box for that calculation. The generic adjunction-conjugate helper and Mathlib
conjugation suffice. The direct tool_uses approvals for compactification coherence and semilinear
derived sections are removed from the assembly node; those geometric tools remain in the lower proof
plans. The categorical calculation is in its own proof module so it compiles independently of the
geometric records. No existing module is withdrawn, and no whole module is claimed globally
unnecessary.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old Transport record is under-specified; the within-field common q
identities do not fix the closed functor on arrows between different fields. For f = identity on
Spec(k), take the identity compactification and a standard transported operation family. Conjugate
one closed functor on each pair object by a nonzero scalar depending only on its field, and
conjugate its inverse adjoint accordingly. Within one field the scalars cancel. Thus all
single-field restrictions, identity q comparisons, shifts and adjunctions survive. Across two
different fields the scalar ratio changes the map. The commonLeft formula would force the canonical
objectwise comparison, which is not natural for this altered action. The previous record therefore
admits examples outside the node's fixed actual common-field transport.

The repair pins the transition generators to the actual normalized scalar comparisons, independently
of any refinement. The published sfCompactSupportNormalizedScalarIsomorphisms provides exactly these
normalized scalar data. The existing coefficient-assembly API already records the corresponding
commonTransitionNatural and common_morphism_normalized conditions. The sole DAG citer,
lem-sf-constructible-exceptional-left-refinements, already has those input normalizations; its
intended use still holds, provided its eventual proof retains them. There is no change to a
Challenge statement or to the fixed unit route.

The existing exists_coefficient_left_refinements theorem is not a usable shortcut: it asks for a
whole coefficient construction and its normalization, rather than the two given Transport records,
and its own DAG proof depends on this item. We do not create that cycle. The original DAG already
has a longer dependency cycle via integral reconstruction/shift data and the coefficient-assembly
parent. The new decomposition retains that existing mathematical plan; it does not create a
dependency between previously separate base components.

## New nodes

- def-sf-exceptional-refinement-transport-data owns Transport and its repaired scalar and transition
  fields, together with the canonical ring inclusion shift.
- def-sf-exceptional-refinement-left-data owns Mates and the new left-only conclusion record.
- def-sf-exceptional-refinement-system-data owns the actual system support word, primitive
  realization map and SystemRealization record, including the inherited shifts.
- lem-sf-exceptional-refinement-left-construction carries the left geometric construction from the
  retained refinement proof, including the scalar transition computation. It is strictly smaller
  than the item: the right mate calculus and system package are absent.
- lem-sf-exceptional-refinement-system-realization carries the intrinsic word, conservative
  invertibility, prescribed total-limit realization and shift squares for a given P. It is an
  existing-comparison lift, not the original comparison-existence theorem repackaged.

- lem-sf-exceptional-refinement-right-square owns the fully proved categorical counit calculation,
  independent of the geometric record and either new geometric obligation.

Each new theorem has its complete proof plan and source in its docstring and node. Three kinds of
Mathlib search were run and recorded. The only change record is
coord/changes/Z6-exceptional-refinement-common-transport.md.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
