## What changed

Partial proof delivery in `Sheaf.Paper.CoordinateSectionProductRecursion`.
Proved `ordinaryWitness_compare` by unfolding its inverse Hom equivalence and
applying `Equiv.apply_symm_apply`. Proved the three ordinary-witness equation
theorems by rewriting the corresponding pro-etale equations inside the literal
witness function, in every endpoint presentation. All existing signatures,
definitions and public imports are preserved.

Updated Step 9 of `lem-pur-coordinate-section-product-recursion` to record this
actual argument. Steps 1--8 and 10 remain the plans for the four original
pro-etale obligations. No new statements or modules were introduced.

## Proved and sorry left

Four of the eight original holes closed, with no holes added:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.ordinaryWitness_compare`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_ordinary`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_ordinary_baseChange`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_ordinary_invariance`

Four original named theorem holes remain unchanged, all attached to
`lem-pur-coordinate-section-product-recursion`:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_recursion`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_baseChange`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_permutation`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_exponent`

The ordinary-witness equation proofs depend on these original pro-etale holes;
this is four closed declaration bodies, not a claim of axiom-free purity.
No decomposition or new hole is hidden in a definition.

Validation: the first proof version compiled through lcompile.py in 29.9 seconds.
The version with unused proof imports removed was also submitted for compilation.
Delivery runs its own compiler probes and preflight checks.

## No longer needed

Removed these unused direct proof imports:

- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.Paper.SupportedCupFunctoriality`
- `Sheaf.Paper.SupportedCup`
- `Sheaf.Paper.AffineSpaceThomMap`
- `Sheaf.Paper.AffineSpaceCoordinateBoundaries`
- `Sheaf.AlgebraicGeometry.CartierKummerMap`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Mathlib.CategoryTheory.Adjunction.Mates`

The completed witness proofs need only the two existing public imports and their
public dependency closure. Step 9 no longer uses
`thm-sf-ambient-adjoint-class`; it was removed from `proof_deps` because no other
step cites it. The other originally cited nodes are retained wherever the
remaining pro-etale proof plans still need them. No whole module withdrawal or
claim that a transitively imported module has left the target closure is made.

## Where the brief, the DAG or earlier work was wrong

The original Step 9 planned an additional site-comparison calculation for the
ordinary-witness theorems. Their actual signatures quantify over lifts of the
already specified pro-etale arrows through one fixed Hom equivalence. Equality
of the pro-etale arrows therefore implies each stated ordinary equality simply
by congruence, independently of the endpoint presentation. The exact realization
of a single witness is the inverse-equivalence law. No mathematical statement
or unit route was changed.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
