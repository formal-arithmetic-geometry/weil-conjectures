## What changed

Only `lean/Sheaf/Paper/PrimitiveQuotientRealizationComparisons.lean` is changed.
All original public signatures, public imports, definitions, and docstrings are preserved.
Six original theorem holes have complete proof bodies. All added helpers are private and proved.
No definition repair, new public declaration, new module, or axiom is introduced.

The balanced association and unit are constructed by uniqueness of ordinary scalar-extension
left adjoints, with their units fixed on sheafified pure tensors. Their formulas, naturality,
uniqueness, quotient transitions, three-field square, and identity square are proved explicitly.
Quotient K-flatness uses the independent-coefficient change-of-rings theorem. System K-flatness
uses exact component evaluations and the existing total-tensor evaluation isomorphism. Flatness
of a system module follows by applying this to its degree-zero complex and the single-tensor
collapse; the universal derived scalar counit is then invertible.

Private proof imports expose the already-proved isomorphism-transport helpers in
`KFlatRingedToposPullback` and the degree-zero K-flat helper in
`FlatSingleDerivedNormalization`. Private reducibility settings keep adjunction-choice and
association constructions from expanding during subsequent tensor calculations. These are
lexical proof settings, with no downstream effect.

The node copy records the actual routes for the six completed helpers and identifies the
remaining realization-normalization obstruction. No target signature or unit route changes.

Validation: the supported single-file compiler passed with no diagnostics in 54.6 seconds.
The original seven public theorem signatures and all three original public definition bodies
are unchanged. The only direct consumer is `Sheaf.Paper.EffectiveQuotientModelDescent`;
its interface is unchanged and no adaptation is required.

## Proved and sorry left

Closed six of the original seven holes, all attached to
`lem-trf-primitive-quotient-realization-comparisons`:

- `WeilConjectures.primitiveQuotientReductionGood`.
- `WeilConjectures.primitiveQuotientScalarAssociation`.
- `WeilConjectures.primitiveQuotientSystemGood`.
- `WeilConjectures.primitiveQuotientScalarTransition`.
- `WeilConjectures.primitiveQuotientScalarTriple`.
- `WeilConjectures.primitiveQuotientScalarUnit`.

One original hole remains, at the same node:
`WeilConjectures.primitiveQuotientRealizationComparisons`. It is marked
`STATEMENT-DISPUTED` for the reason below. Its statement is unchanged.
Holes added: zero. Split-off statements: zero. This is six proofs, not a decomposition.
The proofs use existing named declarations, including declarations still awaiting their own
proofs, as required by stage 3.

## No longer needed

The direct proof import `Sheaf.Algebra.Homology.ChangeOfRingsKFlat` is replaced by
`Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`. The former theorem
requires a coefficient universe tied to the site universes, whereas the item permits
independent field and site universes. Accordingly `lem-pur-kflat-change-of-rings` is replaced
by `lem-pur-kflat-change-of-rings-independent` in this node's plan.

Removed unused direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.FlatRoosFunctorDescent`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.

The six completed helpers do not use these four modules. Their nodes are retained in the
uncompleted realization plan: this delivery does not claim that they can be globally pruned.
No module is withdrawn. All four original public imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED: primitiveQuotientRealizationComparisons`.

`CoefficientReductionPresentation` in `CoefDerivedSystemEvaluationCalculus.lean` controls
`e` only after each finite derived evaluation, together with strict compatibility of the
chain isomorphisms `κ`. The normalizations in `IntegralComparisonRealizationModels.lean`
then require an equation after total derived limit for *every* such `e`. The available
`isIso_iff_evaluations` is conservativity, not faithfulness. It does not justify this equation.

There is a concrete obstruction already for identity pullback and identity scalar extension.
Let A = Z_p, let B be the p-adic completion of the countable free A-module, let D = product A,
and inject B into D by multiplying coordinate i by p^i (i starting at zero). Set M = D/B
for this injection. Both B and D are complete and p-torsion-free, so M is derived complete.
The class x of (1,p,p²,...) is nonzero: its unique preimage would be (1,1,1,...), which is
not in B. For every n, subtracting the first n coordinates shows x belongs to p^n M.
This is the standard nonclosed-image example of
[Stacks 07JQ](https://stacks.math.columbia.edu/tag/07JQ); derived completeness follows from
[Stacks 09AT](https://stacks.math.columbia.edu/tag/09AT).

Put K = A direct-sum M in degree zero, and let delta send the A summand to x in M and
vanish on M. Then delta is nonzero, delta² = 0, and t = 1 + delta is an automorphism.
Its derived reduction modulo p^n is the identity for every n: delta = p^n delta_n and
multiplication by p^n on the two-term quotient resolution is null-homotopic. But K is
derived complete, so the total derived limit of its reduction system carries t to the
nonidentity automorphism t itself.

The example also applies to the stated pro-etale setting: take E = Q_p and a geometric
point of characteristic different from p. Use the corresponding complete coefficient
sheaf, its completed countable direct sum, and its countable product. This point is weakly
contractible, so sections there are exact; the same vector x is a nonzero section of the
cokernel. The two complete torsion-free sheaves make its cokernel derived complete by the
same two-term resolution argument. Replace K by any flat-term K-flat representative P.

Take the canonical strict reduction presentation (C,e,κ), whose existence is part of
S.reductionModel. Replace e by S.reduction.mapIso(t) followed by e. Every finite evaluated
map is unchanged, so this remains a CoefficientReductionPresentation with exactly the same
C and κ. In identity pullback the generator condition uniquely determines q: inverse-image
unit generators generate after sheafification. Thus q is the same for the two presentations.
All remaining factors in the two asserted normalization equations are the same isomorphisms.
Cancelling them would force the total limit of reduction(t) to be the identity, contradicting
its action on the derived complete K.

A repair should pin e by an equation in the *whole system derived category* to the strict
chain presentation determined by κ, rather than only by its finite evaluations. That is an
interface correction affecting other consumers and has not been silently substituted here.
The six true helper theorems do not require this stronger normalization. The earlier stage-2
review's identity-field and identity-map checks did not test an automorphism invisible after
all finite derived evaluations. This report does not claim a Lean-certified counterexample;
it identifies the explicit missing coherence and the mathematical counterexample for review.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
