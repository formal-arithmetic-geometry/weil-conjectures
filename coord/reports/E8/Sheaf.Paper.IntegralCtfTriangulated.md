## What changed

Completed `WeilConjectures.integral_ctf_isTriangulated` in
`Sheaf.Paper.IntegralCtfTriangulated`, preserving its signature, universes, hypotheses,
public imports, and the definition `integralCtfProperty`.

The proof separates bounded integral constructibility from the property of one uniform
Tor interval. It proves the latter is isomorphism invariant, contains zero with interval
[0,0], is stable under integer shifts with interval [a-m,b-m], and is closed under middle
vertices using [min(a,c),max(b,e)]. It then intersects this property with the existing
bounded integral constructible triangulated property.

The finite-stage theorem supplies the quantitative shift and extension clauses.
`import all Sheaf.Paper.FiniteCtfTriangulated` also reuses its already proved private
`tensor_functor`, `amplitude_iso`, `amplitude_mono`, and `torModules` helpers. These occur
only in the theorem proof. The zero argument transports the exact tensor functor's
zero preservation to every K-flat tensor representative; it does not infer a uniform
interval from separate finite-amplitude existence statements. Exactness and shift
comparisons of the canonical reductions come from `integralDerivedReduction_exact`.
An explicit proof import names `Sheaf.Paper.IntegralDerivedReduction`.

Updated the existing node's proof, proof dependencies and proof origin to match this
argument. No public declaration or consumer changed, so no change record is needed.
The theorem-local unused-variable lint option preserves the original explicit `n`
binder in its instance-inference lambda without a warning.

Validation: the initial complete pruned proof compiled through `lcompile.py` in 3.0 seconds,
with no warnings. The final version keeps the Limits open inside the proof and takes
a zero object from the existing integral subcategory, preserving the file interface.
The delivery dry run checks that final version with its axiom probe. Both explicit proof imports pass `tools/import_direction.py may`.
The source passages checked were Stacks Tags 08FZ and 08G2(2), and the integral paragraph
of the current main-20261015 `def-weil-finite-tor-amplitude`. The unit's `realized`
statement and steps are empty; no unit route is bypassed. Zero, empty schemes, arbitrary
integer shifts, and both orders of endpoint intervals are covered by the argument.

The required msearch queries were: LeanFinder, “Tor amplitude zero object triangulated
subcategory uniform reduction shifts” (only t-structure matches, no replacement);
Loogle, `ObjectProperty.IsTriangulated` (no indexed match); grep,
`HasProEtaleTorAmplitude|integralDerivedReduction` (no indexed match). Direct rg searches
of Sheaf, WeilConjectures and Mathlib located the finite quantitative theorem, its proved
helpers, the reduction exactness interface and Mathlib's triangulated intersection API.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.integral_ctf_isTriangulated`
(node `lem-weil-integral-ctf-triangulated`).

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining in the item: 0.
This is a complete proof from existing declarations, not a decomposition. Existing
imported declarations may still depend on their own registered sorries; they are not
claimed to have been proved in this delivery.

## No longer needed

Removed these eight unused proof imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedTensor`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

The proof needs neither the independent-coefficient small-model Tor presentation nor
the unrestricted scalar-reduction or Sf-integral presentations. It works on exactly
the categories and canonical reductions named by the existing item statement.
The two tensor imports are replaced by reuse of the proved finite-stage tensor helper;
the two direct change-of-rings imports are replaced by the canonical reduction API.

Removed `lem-pur-derived-change-of-rings` and `def-weil-derived-tensor` from this node's
direct proof dependencies: their constructions are already encapsulated by the
canonical reduction exactness and finite-stage tensor helper. They remain indirect
requirements where the imported construction uses them. No claim is made that these
modules leave the entire targets' import closure. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the six-step argument was found. Several global dependency
records have since moved to unrestricted or independent-coefficient interfaces, while
this item's unchanged statement still uses the original finite-field-indexed integral
interface. The original public dependencies already state the needed matching
triangulation and reduction exactness, so no coefficient bridge or statement repair
is required. The initial proof-import list included the alternative interfaces without
needing them. The updated proof records the actual canonical interface and the existing
finite-stage helpers used by the Lean proof.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
