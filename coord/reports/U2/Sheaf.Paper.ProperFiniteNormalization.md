## What changed

Replaced the three proof holes in `Sheaf.Paper.ProperFiniteNormalization` by explicit
proofs, preserving every existing declaration signature and definition body.
The bounded-origin clause uses `finiteRing_constructibleDerived_origin`; boundedness
supplies a finite vanishing interval and a bounded-below antecedent. The refinement
clause is associativity followed by `clopenSupportCanonicalComparison_coherence`.

The quotient square is proved for arbitrary finite coefficient maps in a private helper:
apply ordinary derived direct image to the identity-open scalar square, then use
naturality of the published `sfDerivedImageRestriction`. The successive ordinary
comparison is deduced by pasting these squares with `sfCompactSupportRestriction_comp`,
naturality of both coefficient associators, and cancellation of the invertible source
normalization. The compact-support component uses the existing composition theorem;
the composite square uses the same generic helper. No new coefficient map or comparison
is chosen, and no preservation of K-injectives by scalar restriction is assumed.

Added `Sheaf.AlgebraicGeometry.ProEtaleIdentityOpenScalarRestriction`, isolating the
identity-open scalar compatibility before any direct image, proper morphism,
compactification, boundedness, or coefficient-level specialization. Updated the item
node's proof and dependency lists to this argument.

## Proved and sorry left

Closed the existing hole in
`WeilConjectures.PurityFiniteSetting.properFiniteNormalization` by a complete proof
from existing declarations, without new holes for that theorem.

Replaced the holes in
`WeilConjectures.PurityFiniteSetting.properFiniteNormalization_quotient` and
`WeilConjectures.PurityFiniteSetting.properFiniteNormalization_successive`
by complete combining proofs from the single new identity-open lemma and existing
comparison declarations. These two closures are a decomposition, not an independent
proof of the new lemma.

Holes closed: 3. Holes added: 1. Remaining holes in the assigned module: 0.
The only added hole is `AlgebraicGeometry.Scheme.sfIdentityOpenRestriction`
(node `lem-weil-identity-open-scalar-restriction`), exactly `:= by sorry` in its own
module. Its docstring and node give the unit-normalization, sheafification uniqueness,
and exact localization argument. All private helpers are proved.

## No longer needed

Removed direct imports (retained APIs needed by signatures are supplied by the two
public comparison modules; proof-only prerequisites are imported privately):

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.Paper.CompactificationCoherence`
- `Sheaf.Paper.FiniteFieldFiber`
- `Sheaf.Paper.FixedEtaleOriginDerivedCategory`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.SfDerivedDirectImage`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `WeilConjectures.Compactification.RefinementCategory`

The direct finite-level proof no longer calls `constructible_proEtale_origin`:
the existing finite-ring theorem gives the bounded antecedent in the exact intrinsic
coordinates. It no longer calls `compactification_coherence` directly: the already
published bounded-constructible comparison cocycle suffices. There is no separate
fixed-etale-origin-category construction in this proof. Thus the item's direct proof
route no longer needs `lem-sf-proetale-constructible-origin`,
`prop-compactification-coherence-detailed`, or `def-sf-etale-origin-subcategory`.
These still occur inside other retained library modules and are not withdrawn.

Sheafification uniqueness, extension exactness, and termwise derived factorization
are moved to the new strictly smaller identity-open lemma; they are retained as its
proof dependencies. The direct-image scalar theorem remains encapsulated by the
published comparisons in `SfCompactSupportRestrictionOfScalars`. No Lean module or
upstream declaration is withdrawn; no unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing node plan's origin statement is implemented more directly by the already
proved finite-ring constructible derived-origin theorem. The canonical bounded
comparison already exposes the needed cocycle. The coefficient compatibility is not
definitional: `sfIntrinsicDerivedOpenId` and `sfOpenRestrictionDerived` are separately
normalized constructions, so their identity-open compatibility must be proved.
That is the one remaining auxiliary theorem, rather than assuming arbitrary
isomorphisms commute.

The new identity-open statement was checked on identity coefficient maps, the zero
ring, and the empty scheme: it asserts equality of the canonical normalized maps,
without any nonzero, surjectivity, flatness, or boundedness assumption. Its proof is
the source's sheafification uniqueness argument, not a restatement of the proper
normalization theorem.

## New nodes

`lem-weil-identity-open-scalar-restriction` records the scalar square for the canonical
identity extension by zero on the whole unbounded category. It is step 4 of the item
before applying any direct image; it has no morphism to a second scheme and no
compactification or properness hypotheses. The combining proof is naturality of the
ordinary direct-image comparison, and the successive comparison follows by a real
pasting/cancellation argument. Searches by leanfinder, Loogle and grep are recorded in
`searches.jsonl`; none states this normalized derived square. No definitions or
statements were repaired. The public import cleanup is recorded in
`coord/changes/U2-proper-finite-normalization-imports.md` for review.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
