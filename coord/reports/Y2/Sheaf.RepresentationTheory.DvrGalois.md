## What changed

Proved `Rep.isZero_dvr_galois_cohomology` without changing its signature. The proof follows
all six steps of the existing blueprint plan. Added four supporting modules: tame coordinate
finite quotients, exact kernel invariants and the injective-resolution comparison, its local
Galois specialization, and the vanishing/finite-cardinality consequences of the two-term
procyclic computation. The fixed module is constructed as an actual submodule; no arbitrary
module is selected from an unproved mere existence theorem.

## Proved and sorry left

Closed the one original hole, `Rep.isZero_dvr_galois_cohomology` (lem-exc-dvr-galois).
Added zero holes. The four new supporting results and every helper are proved in this delivery.
No `sorry` remains in any delivered module. Existing imported statements, notably the tame
Galois sequence, the abelian discrete-module infrastructure and the procyclic computation,
remain independent dependencies as required by the stage-3 brief.

## No longer needed

Removed direct proof imports `Sheaf.CategoryTheory.DiscreteModulesAbelian`,
`Sheaf.RepresentationTheory.ProcyclicTwoTerm`,
`Mathlib.CategoryTheory.Preadditive.Injective.Resolution`,
`Mathlib.CategoryTheory.Abelian.RightDerived`, and
`Sheaf.FieldTheory.HenselianDVRTameSequence` from the item: their required results occur in the
supporting modules. All seven original proof dependencies are still used transitively.
Removed the redundant direct `Mathlib.NumberTheory.Padics.PadicIntegers` import from the
comparison: `ProperSpace` supplies it. Group quotient, finite-group and Pi lemmas are
proof imports in the supporting modules.
No node or module is pruned from the mathematical argument, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier draft had a `sorry` comparison, missing node/report records and incompatible choices
of zero-morphism instances in its injective-resolution argument. These are completed here.
The resumed dry run exposed a timeout and universe mismatches in the retained exactness helpers.
Their quotient is now explicitly in `Type`, with coefficient carriers in `max u w`, exactly
as required by the comparison theorem and the chosen abelian structures.
The statement and all six original proof steps are mathematically unchanged.
The retained naturality proof timed out while rewriting through chosen invariant functors.
Explicit applications of their naturality equations and inverse identities avoid that
unfolding. Local irreducibility now hides the fixed submodule after its membership lemma,
the quotient action after its application lemma, and inflation adjunction after construction.
The kernel-invariants module compiled in 16.1 seconds with the default heartbeat setting.
No compile limit is raised.
The resumed five-module packet passes the delivery dry run. Its full inventory axiom
probe for `KernelInvariantsCohomology` reached 60 seconds; the tool records that the
merge repeats this check. A focused `#print axioms Rep.kernelFixed_cohomology_iso`
check of the compiled module passes in 1.8 seconds and reports only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx` inherited from the existing imported
statements. No new hole or axiom is introduced.
Averaging only needs an open normal subgroup fixing the chosen lift, so no separate finite
module spanned by its orbit is necessary. The finite-quotient argument uses invertibility of
ell on the other adic factors and Cauchy's theorem, avoiding a separate factorization theorem
for continuous maps out of an infinite product.
The main theorem's isomorphism transport now uses the correctly directed isomorphism
for zero objects and its underlying linear equivalence for finiteness. Implementation-only
functors, the averaging lemma and injective-resolution helpers are private and fully proved.
The injective-preservation import is proof-only. The existing warning-as-error option is
scoped to the main theorem, so it does not apply to generated axiom-probe lines.

## New nodes

`lem-exc-tame-ell-coordinate`: second paragraph / step 2, proved finite-quotient argument.
`lem-exc-kernel-invariants-cohomology`: third paragraph / steps 3--5, proved averaging,
inflation adjunction, preservation of injectives and comparison by an injective resolution.
`lem-exc-dvr-galois-comparison`: proved local specialization of the preceding two results
and the existing tame Galois sequence.
`lem-exc-procyclic-cohomology-conclusions`: final paragraph / step 6, proved vanishing
and finiteness by subquotients of the two finite terms.
No existing signature, definition or visibility changed. The module-command scope change
is recorded in `coord/changes/Y2-dvr-galois-warning-scope.md`.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
