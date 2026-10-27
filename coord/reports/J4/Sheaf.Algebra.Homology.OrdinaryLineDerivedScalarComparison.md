## What changed

Proved `SheafOfModules.OrdinaryLineScalar.comparison_identity_arbitrary` in
`Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison`. The prescribed arbitrary
signed-power line isomorphism remains the actual tensor map after scalar multiplication
normalization. Added proved private helpers for the normalized ordinary tensor comparison
and the categorical pasting and cochain-resolution calculations, with the inverse
ordinary-unitor formula
proved inside the tensor helper. A proved private equality identifies the existing
concrete pure tensor with the generic ordinary tensor; both calculations reuse this
equality while keeping the constructors locally irreducible. The ordinary equation uses
the existing pure-tensor extensionality and tensor-map formulas from
`ScalarHomOrdinaryTensorComparison`; the derived argument uses the existing representative
normalization. An explicit private import of `KFlatResolutionIndependentCoefficients`
supplies a resolution for transferring the equation to arbitrary unbounded complexes.

Kept large comparison and pure-tensor constructions locally irreducible, with a proved
conversion lemma reused by both section calculations. The existing category and abelian caches remain active. The monoidal cache declaration
remains intact; a local instance selects its canonical underlying tensor structure directly. The site-specific
successor-universe sheafification instance is disabled locally: its coefficient
hom-universe is `t + 1`, whereas this module uses `max a (t + 1)`. Existing general
sheafification instances supply the declared coefficient size. The degree-zero collapse
witness is hidden from unnecessary local unfolding. The flat-term argument transports
exactness through the existing tensor comparison and uses the explicit finite-limit and
finite-colimit composition lemmas.

Updated the existing node's ninth proof step and proof dependencies to record this
argument. All existing public statement meanings and construction data are preserved. Existing
universe and category arguments are now explicit at concrete use sites, including
source/target categories in `compute`, to avoid redundant instance search and unfolding.
The change record is `coord/changes/J4-ordinary-line-explicit-parameters.md`; no consumer
adaptation or source-library edit is needed.

## Proved and sorry left

Closed one of the three original holes:
`SheafOfModules.OrdinaryLineScalar.comparison_identity_arbitrary`.

The two original holes left, both attached to
`lem-pur-ordinary-line-derived-scalar-comparison`, are:

- `SheafOfModules.OrdinaryLineScalar.ordinary_line_derived_scalar_comparison`.
- `SheafOfModules.OrdinaryLineScalar.comparison_tower`.

No holes were added or split off. Every new private helper is fully proved.
The existing proof of `comparison_identity` now uses the proved arbitrary-comparison
lemma instead of its former sorry.

## No longer needed

None. No original imports, nodes or modules were removed. The other theorem clauses
remain attached to this node and retain their original proof plans and dependencies.
The proof does not impose an identity on an arbitrary line automorphism: it retains the
specified `A m` for every integer, including zero and negative exponents.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The narrow site-specific sheafification
instance caused spurious universe constraints in the general coefficient size; this
module now uses the existing general instances. The old ninth proof step did not explicitly
name the flat K-flat resolution used to extend the representative calculation to an
arbitrary complex. The updated step records this dependency and the naturality/cancellation
argument. The blueprint unit route is unchanged. No new node was needed.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
