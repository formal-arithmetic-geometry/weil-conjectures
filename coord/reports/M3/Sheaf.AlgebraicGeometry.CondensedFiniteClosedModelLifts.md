## What changed

Proved `AlgebraicGeometry.ProEtale.condensed_finite_closed_model_lifts` in
`Sheaf.AlgebraicGeometry.CondensedFiniteClosedModelLifts`, preserving every existing
signature, definition and public import. Added proved private helpers deriving the
pullback composition and identity comparisons and full faithfulness along a scheme
isomorphism. The specified reduction identifies the fiber map with a quotient
immersion composed with an isomorphism. Henselian rigidity, pullback preservation of
dualizability and scalar projective calculus make its restriction fully faithful on
the two dualizable objects. `FullyFaithful.isoEquiv` lifts the prescribed isomorphism;
cancellation proves its canonical restriction formula and uniqueness. Faithful
flatness gives the spectrum range inclusion. The finite coproduct is affine, flat,
surjective and quasi-compact, and the finite spectral-cover API supplies the exact
pro-etale precoverage condition.

Added private proof imports of
`Sheaf.AlgebraicGeometry.CondensedWContractibleProjectiveCalculus`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence`, and
`import all WeilConjectures.RingTheory.WContractibleGeometricCriterion`. The last
uses the existing proved private ring-equivalence invariance helper. Updated the
item node's proof to describe these comparisons and the finite-cover proof.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.condensed_finite_closed_model_lifts`
(node `lem-zl-condensed-finite-closed-model-lifts`).
No holes added, no split-off statements, and no sorry remains in the delivered module.
The proof uses the existing declared rigidity, locality and projective-calculus
results as authorized by stage 3; it does not claim their remaining holes are closed.

## No longer needed

Removed the private proof import `Sheaf.RingTheory.IndEtaleStability` and removed
`lem-weil-pbc-ind-etale-stability` from the item's proof dependencies. The source
already proves `Algebra.IndEtale.weaklyEtale`, which the scheme instance uses directly;
the larger stability theorem is unnecessary for this argument. No declarations or
modules are withdrawn. All other stated proof dependencies are used. The other
existing private imports remain needed for henselianity, dualizability, spectrum
surjectivity and affine morphism instances. Every existing public import is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The rigidity theorem is phrased for the literal
quotient, while the item uses the specified isomorphic closed fiber. The proof
explicitly transports full faithfulness along that isomorphism and verifies the
factorization of the specified fiber map. The scalar projective-calculus theorem
has landed and supplies dualizability of the prescribed scalar model.

Checked the source arguments in HRS Corollary 4.4(2), Lemma 4.1 and Theorem 4.13,
and Bhatt--Scholze Definition 2.2.10, Lemmas 2.2.12 and 6.1.1. The existing unit route
is retained. Finite-cover APIs cover the empty index set without a nonemptiness
hypothesis; each prescribed P remains independent of the other indices.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
