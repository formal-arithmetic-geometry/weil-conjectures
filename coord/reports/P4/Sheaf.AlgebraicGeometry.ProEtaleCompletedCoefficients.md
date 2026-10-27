## What changed

The original `sfb_completed_coefficients` signature and every coefficient construction are
preserved. The constructions move to `ProEtaleCompletedCoefficientData`, publicly reexported
by the original module, so the smaller compatibility lemmas precede the assembly without a
cycle. Ten definition bodies move verbatim. The comparison predicate's rational naturality
field uses the underlying bundled `coefficientPullbackIso` components. Each component is
identity followed by the original `condensedPullbackHom`, as checked by the proved generic
normalization helper. This equivalent presentation avoids a repeated kernel timeout during
concrete ring-object instance conversion. It is explicitly recorded for definition review.

The assembly uses the existing `completedCondensedRational` and
`completedCondensedPadicRational` fraction maps. A private helper builds their natural
transformations and explicit `IsColimit` records from the supplied universal properties,
uses the supplied pullback leg equations in their bundled presentation, and applies
the scalar telescope's ring universal property.
For the integral clauses it verifies compactness, finite discrete quotients and separation for
both the finite-extension integers and the standard p-adic integers. Another private helper
proves the normalized isomorphism with the ZMod tower directly from the kernel and surjectivity
of `PadicInt.toZModPow`; quotient representatives prove successor naturality, including n=0.
Proved generic helpers combine the integral and rational clauses and transport the comparison
along equality of the canonical inclusion maps. A private generic monoidal-category lemma proves the underlying comparison formula,
documenting equivalence of the bundled naturality equation with the raw compositor equation.
The proved rationalization assembly is in `ProEtaleCompletedRationalization` so compiled
artifact production stays below the per-file limit; the main module imports its proved theorem.
The local normed-field instance is confined to the integral branch.
The algebraic-closure clauses use the published abelian colimit, inverse-image preservation,
the filtered ring-object upgrade and compositor naturality.

Change record: `coord/changes/P4-completed-coefficient-data-extraction.md`.

## Proved and sorry left

Closed the body of `AlgebraicGeometry.ProEtale.sfb_completed_coefficients`
(node `lem-route-sfb-completed-coefficients`) by a complete assembly from the existing coefficient
unit and two smaller named steps. This is a decomposition, not a net elimination of proof holes:
one old hole closed, two new holes added, zero holes in definitions.

The delivery leaves exactly these two holes, in separate modules:

- `AlgebraicGeometry.ProEtale.sfb_normalized_integral_quotient_cone`
  (`lem-pe-normalized-integral-quotient-cone`): only the normalized compact quotient limit and
  its preservation, with no rationalization or algebraic-closure assertion.
- `CategoryTheory.scalar_telescope_ring_universal`
  (`lem-pe-scalar-telescope-ring-universal`): only the abstract ring universal property from
  a specified module telescope, with no p-adic or pro-etale input.

Also proved `AlgebraicGeometry.ProEtale.sfb_rational_comparison_from_completed` in the
new rationalization assembly module; its former private implementation is separated for
compilation performance, with no additional hole.

Both admitted statements are true source steps, strictly smaller than the original conjunction. Their docstrings
and nodes contain complete proof arguments. Edge checks include the zero quotient at n=0,
the zero ring, I=top (where separation forces a zero ring), empty schemes, and scalar zero
(where the invertibility hypotheses force zero objects). No arbitrary witness is chosen as
definition data from an unproved existence theorem.

Validation: remote `lcompile.py --all` returned successful compilation for all five
deliverable modules and the three direct importers, `IntegralTensorPullbackData`,
`CondensedZlReductionCone` and `CondensedZlReduction`. The importer copies were byte-identical
to the repository and removed after validation. The original target signature is byte-for-byte
identical. Ten construction bodies were checked identical; the single predicate change is
recorded above. All node JSON parses, and all Lean lines satisfy the 100-character limit.

## No longer needed

No module or DAG node is withdrawn. The reviewed statement dependencies are retained.
The assembly's direct proof dependencies name the existing coefficient unit and the explicit
compatibility steps, rather than importing every internal step separately. Every dependency
of the current statement review remains reached directly or transitively; the specialized
p-adic reduction node records the exact Mathlib reduction lemmas used in the tower proof. The original unit's integral, localization, finite-field-colimit and pullback steps
remain represented by the existing completed-coefficient module and the explicit compatibility
lemmas; no unit route is bypassed. The positive-index integral and localization APIs are reused
through the completed-coefficient module rather than re-proved.

The original proof imports `Mathlib.CategoryTheory.Adjunction.Limits` and
`Mathlib.CategoryTheory.Yoneda` are removed: the assembly uses the existing coefficient APIs,
not an adjunction or Yoneda argument. Every original public import is retained. The new data
module imports only the constructions its definitions need. The redundant explicit import
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` was removed from the new scalar lemma
module; it is already public through `ModuleObjects.Preadditive`.

## Where the brief, the DAG or earlier work was wrong

The item's attached route node was provisional at initial inspection, with empty `proof`
and `proof_deps`, although the Lean docstring gave a seven-step plan. Its stage-1 statement
review completed during this work; that current reviewed statement and its statement
dependencies are preserved in this packet. Existing declarations state most of that plan in
a different presentation: positive quotient indexing and a ring comparison for commutative
colimit models. They do not directly supply this theorem's point-level constant-section
normalization or its universal property against arbitrary monoid objects. The two new nodes
state exactly these gaps rather than duplicate the entire comparison theorem. The current
reviewed statement and all existing signatures are preserved. Its rational naturality
condition is reexpressed via the canonical bundled ring comparison to avoid the kernel
conversion timeout; the old and new equations have the same meaning by the identity law.

## New nodes

`def-pe-completed-coefficient-comparison-data` attaches the relocated, identical comparison
data to its new module, including the equivalent bundled naturality presentation; the
coefficient objects and their maps are unchanged.

`lem-pe-normalized-integral-quotient-cone` is the generic compact, separated finite quotient
cone with its constant-section normalization and scheme pullback property. The source is the
integral-limit argument, using finite constant representations and represented tower limits.

`lem-pe-scalar-telescope-ring-universal` isolates the localization Ring structure paragraph:
fraction cocones give the map, tensor-colimit uniqueness proves multiplicativity, and the
zeroth leg and recurrence give factorization and uniqueness.

`lem-pe-rational-comparison-from-fraction-maps` attaches the proved rationalization assembly
in its own module. It constructs the natural transformation and IsColimit and applies the
scalar ring universal property. This node adds no proof hole.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
