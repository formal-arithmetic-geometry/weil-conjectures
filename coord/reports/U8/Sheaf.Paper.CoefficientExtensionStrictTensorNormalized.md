## What changed

Replaced the proof hole in
`WeilConjectures.coefficientExtensionStrictTensor_normalized` by the K-flat,
localization, adjunction, and Hom-bijection argument. Its statement and public
imports are unchanged. Proved private helpers establish K-flatness of the actual
finite scalar complex, transport K-flatness across an ordinary complex
isomorphism, and identify the localized actual transition.

Added `Sheaf.Paper.CoefficientExtensionOrdinaryQuotientIso`, stating the remaining
ordinary balanced-association calculation with its adjunction-unit equation.
It applies to arbitrary ordinary complexes: it assumes neither K-flatness nor
flat terms, and contains no derived normalization conclusion. The main proof
uses change of rings and the normalized derived quotient unit to pass from this
ordinary equation to the derived Hom criterion. This follows the assigned route.

The new proof imports the ordinary quotient lemma, K-flat change of rings,
the private object/map equations of IntegralScalarExtensionWellDefined, and
Mathlib's HomCongr, and the existing exact-functor composition API. The small
composition identity is proved locally, avoiding the broader derived-adjunction
import. The new ordinary module publicly imports only
CoefDerivedSystemEvaluationCalculus and IntegralScalarExtensionUniverses.
No existing definition or public signature changes.

Validation: the final main module compiles through lcompile.py without warnings
in 31.9 seconds. The new ordinary module compiles in 40.1 seconds. Profiling
options were removed; there are no transparency overrides. Import-cycle checks,
original-signature comparison, line lengths, exact new Lean attachment, and the
union of each node's proof dependencies were checked.

## Proved and sorry left

Closed the direct hole in
`WeilConjectures.coefficientExtensionStrictTensor_normalized`
(node `stage3-pur-extension-strict-tensor-normalized`).

Added one hole:
`WeilConjectures.coefficientExtensionOrdinaryQuotientIso`
(node `stage3-pur-extension-ordinary-quotient-iso`). This is the whole proof of
that public theorem in its own module, with its source and complete ordinary
argument in its docstring.

Counts: one original hole closed, one ordinary hole added; a decomposition,
with net hole reduction zero. There are no other holes in the delivered files.
The original theorem now has a complete proof from the named dependencies and
the ordinary lemma. In particular the K-flat computation, localization of the
unit equation, evaluation conjugations, and final bijection are proved here.

## No longer needed

No original public import or library module is pruned. The original node's
standalone proof edge to `lem-coef-semilinear-derived-sections` is unnecessary:
the proof uses the finite-quotient calculus directly. Its module remains a
transitive public dependency of CoefficientExtensionReductionData, so this is
not reported as removing that module from the targets' closure.

The proof does not need CoefficientExtensionStrictDerivedComparison, the
coefficient-extension reduction model, a completed-limit computation, or a
normalization theorem for an arbitrary derived scalar extension. Those are not
imported. A trial proof import of CoefficientSequenceRoosModel was removed;
the exact transition localization formula is proved directly from liftNatTrans.
A trial MapDerivedCategoryMate import is also replaced by the smaller existing
exact-functor API and a local proof of the needed composition identity.
All original unit statements and routes remain in place.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The stated dependencies provide K-flat
change of rings, the quotient adjunction and its normalized derived unit, but do
not state the ordinary balanced associator together with its actual strict
transition equation. This ordinary part of steps 1--2 is now explicit. It is
strictly below the assigned derived obligation: it has no good-representative
hypothesis or derived conclusion, and the main proof supplies the K-flat and
localization argument separately.

The latest blueprint has reorganized the old integral-operations source path.
The source calculation is cited directly to Stacks 03D7 and 03EK, together with
the precise steps of the assigned node; its proof origin is recorded as an agent
expansion. The ordinary formulas include m=n via the restriction unitor, zero
complexes, and the empty scheme, and make no flatness assumption on B_m to B_n.

## New nodes

`stage3-pur-extension-ordinary-quotient-iso` states the ordinary quotient
association and its actual transition-adjoint equation for arbitrary complexes.
It inherits the item's chapter and unit. Its docstring and node give the local
balanced maps, their inverse, sheafification, differential compatibility,
successor identification, induction to general n≤m, and the identity case.
LeanSearch, LeanFinder, Loogle and source searches found ordinary module
associators, but no statement with these strict-system transitions. No existing
interface is changed, so there is no change record or forced consumer adaptation.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
