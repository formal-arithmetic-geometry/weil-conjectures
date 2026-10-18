## What changed

Proved `AlgebraicGeometry.Etale.properSmoothCurves_finiteModule_higherDirectImage_constructible`
with its signature and public imports unchanged. All helpers are private and proved in the
item module. Updated the existing node's proof, proof dependencies and proof origin to
record the actual argument.

The proof transfers constructibility through isomorphic underlying abelian sheaves using
the existing finite-value/lisse comparisons. It decomposes the base into complementary
clopen dimension loci. Quasi-finite shriek constructibility handles dimension zero for
all finite coefficient modules directly. On dimension one, the existing prime-coefficient
curve theorem extends to finite prime-killed modules by a finite vector-space basis and
additive functors. Strong induction on a positive annihilator then uses the kernel of
multiplication by a prime and its cokernel. Extension closure follows from the
triangulated constructible-homology property and the exact constant-sheaf functor.
Bounded-below and unbounded derived pushforwards are compared by their existing
compatibility isomorphism. Etale derived base change and open/closed gluing combine
the two loci.
The algebraic-closure projection of a residue-field fibre is integral and surjective;
incomparability and going up identify its Krull dimension with the ordinary fibre.
This supplies precisely the hypothesis of the dimension-loci declaration. Empty loci,
zero modules, the zero coefficient ring and negative cohomological degrees are included.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.properSmoothCurves_finiteModule_higherDirectImage_constructible`
(node `lem-weil-pbc-etale-proper-smooth-curves-finite-module`).
No holes added; no `sorry` remains in the delivered module. This proof uses existing
named declarations, including the dimension-loci, prime-coefficient and quasi-finite
shriek declarations, whose proofs remain separate project obligations.

Validation: the complete delivered module compiled through `lcompile.py` on the project
server in 59.0 seconds. Every helper is proved; there are no new modules or nodes.
The finite-vector-space helper keeps the original commutative-ring structure in its
signature, and the exact-functor helper handles the two canonical zero-morphism
instances explicitly. These interfaces avoid expensive definitional comparisons of
concrete derived sheaf functors.

## No longer needed

Removed proof imports (some remain available transitively; these are removals of direct
proof dependencies, not claims that every module becomes globally unreachable):

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

Removed these edges from this node's proof plan:

- `lemma-constructible-hom-constant-locally`
- `def-weil-pbc-constructible-abelian-sheaf`
- `def-weil-pbc-etale-constructible-sheaf`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-constant-sheaf-geometric-stalk`
- `lem-weil-pbc-etale-restriction-injectives`
- `def-weil-pbc-direct-image`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `def-sbc-smooth-morphisms`
- `def-weil-pbc-scheme-conventions`
- `def-weil-proper-morphism`
- `def-sbc-locally-finite-presentation`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-sheafification-exact`
- `lem-weil-pbc-right-derived-universal-delta-functor`
- `lem-weil-pbc-module-direct-image-left-exact`
- `lem-weil-pbc-module-sheaves-enough-injectives`

The explicit abelian-chart scalar-refinement argument is replaced by the existing
finite-stalk/lisse equivalence; no separate local scalar-endomorphism construction is
needed. Etale derived base change replaces the restriction-of-injectives argument.
The triangulated constructible-homology property replaces the explicit five-term
long-exact-sequence construction. Quasi-compactness of the source follows directly from
properness over the compact base; the separate qcqs permanence detour is unnecessary.
Statement dependencies, including the definitions of constructibility, properness,
smoothness and derived direct image, are retained in `stmt_deps`; removing their redundant
proof edges does not prune their statements.

## Where the brief, the DAG or earlier work was wrong

No statement was changed or disputed. The dimension-loci declaration states geometric
fibre dimensions, whereas this item's hypothesis concerns ordinary residue-field fibres;
the proof now supplies the integral-surjective dimension comparison explicitly. Its
one-dimensional prime-coefficient input requires dimension exactly one, so applying it
to the whole family would miss the dimension-zero case; the clopen decomposition is
essential. The original docstring is retained verbatim; the updated node describes the
shorter implemented coefficient-transfer and extension arguments.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
