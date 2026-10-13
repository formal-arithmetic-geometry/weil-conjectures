## What changed

Proved `CategoryTheory.localizedHomComplex_cycles_bijective` in
`Sheaf.Algebra.Homology.LocalizedHomComplexCyclesBijective`, with its signature and
public imports unchanged. Added proof-only imports for sheaf-module limits,
product preservation, and the explicit abelian-group cycle kernel.

The private, fully proved `fan_bijective` helper obtains joint injectivity and
surjectivity of the projections of a limiting fan in types by testing its
universal property on a one-point type. Applied it to the evaluated product
cones from `homComplex_exists`. Degree-zero indexing is transported along
`p + 0 = p` using pointwise cast equivalences. Injectivity then follows from
component equality and the monic cycle inclusion. For surjectivity, assemble
the components of the given chain map, use the prescribed differential and
its chain-map equation to show the assembled section is in the kernel, and
lift it with `ShortComplex.abCyclesIso.inv`. Component extensionality and the
assumed projection formula identify its image with the given map.

This follows the existing node's route; no DAG dependencies, definitions,
statements, or other modules were changed. The unit has no realized steps to
bypass. Read Stacks Tag 0A8X, the construction preceding Equation 0A8Y, online
because this clone contains literature indexes but not the fetched TeX sources.

Searches: Lean Finder for the localized cycle/chain-map correspondence returned
sheafification and internal-Hom section equivalences, but no exact theorem.
Loogle for `Concrete.isLimit_iff` returned no match (unknown identifier).
Mathlib grep located `Types.isLimitEquivSections` and product preservation;
source-library and Sheaf grep found only this comparison and its downstream
consumers. The proof uses the existing Hom-complex construction rather than
introducing any intermediate statements with holes.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.localizedHomComplex_cycles_bijective`
(node `lem-pur-localized-hom-complex-cycles-bijective`).

Holes added: none. Sorries left in the delivered module: none. Both private
helpers are fully proved. This is a proof, not a decomposition into new holes;
`CategoryTheory.homComplex_exists` is already fully proved in the library.

## No longer needed

None of the original imports or proof-dependency nodes were removed.
The only DAG dependency, `def-pur-hom-complex` (module
`Sheaf.Algebra.Homology.HomComplex`), is used for its product cones and
differential formula. No planned node or module is bypassed or pruned.
The exploratory import `Mathlib.CategoryTheory.Limits.Types.Products` was
removed because the fan universal property suffices directly.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The existing plan is sufficient.
Lean's simplifier does not normalize the dependent projection family's
codomain under `Function.Bijective`; the proof explicitly transports the
family with `Equiv.piCongrRight` and proves the cast formula by substitution.
The abstract cycle object is lifted using Mathlib's explicit abelian-group
kernel isomorphism, with the next-index equality given by `CochainComplex.next`.

## Second reading by G3

1. Compared the only delivered module against the repository with `diff`, and
   checked the existing theorem signature byte for byte: unchanged. All public
   imports and the existing docstring are unchanged; no definitions, change
   records, or other library modules are delivered.
2. Read the entire proof and both private helpers. The helper tests the
   limiting fan on a singleton, so works for empty index sets as well. The main
   proof uses genuine product limits, the chain-map equation, and the explicit
   kernel isomorphism; no data comes from an unproved existence theorem. The
   delivered source has no sorry or forbidden declaration. Compilation and
   axiom results are recorded below after validation.
3. No statements were split off and no holes were added. Independently searched
   the sheaf and upstream homology sources for Hom-complex cycle comparisons,
   and Mathlib's type-product and concrete-limit APIs for fan bijectivity. The
   generic section equivalence would require additional discrete-section
   conversion; the short, proved fan helper avoids that conversion. The ordinary
   Hom-group cocycle results do not identify this evaluated sheaf product.
4. The sole original dependency `def-pur-hom-complex` is used for both its
   limiting product cones and differential formula. All original imports
   supply the statement's constructions; the added private imports supply
   limit-preservation instances, evaluated fan comparison, and the explicit
   cycle kernel. There are no unused original proof dependencies to prune.
   Checked `dag/units/sk-def-sf-operations.json`: both realized lists and the
   unit's steps are empty; no unit route is bypassed.
5. Read the existing node's statement, proof, proof_deps and proof_origin. Its
   product/kernel argument agrees with the Lean proof and uses exactly
   `def-pur-hom-complex`; no node edit or new node is needed.

Repairs: initial compilation twice exceeded 60 seconds. Factored the product
and kernel argument into a private, fully proved `cycles_bijective_of_product`
helper over an arbitrary complex with limiting product projections and the
degree-zero differential identity. The original theorem specializes it to
`homComplex_exists`. This avoids repeatedly unfolding the large chosen
bifunctor during elaboration. The helper is the same proof under generalized
data, has no holes, and introduces no public interface or new dependency.
Restricted backward definitional equality to respect transparency, disabled
backward defeq attributes, explicitly supplied the ring-sheaf parameter and
typed the differential congruence and lifted cycle, and supplied the arguments
of the final projection rewrite. The differential calculation follows the
explicitly typed component formula. These changes keep the mathematical route.

Validation: the repaired proof compiled in 46.5 seconds; the explicit scratch
`#print axioms CategoryTheory.localizedHomComplex_cycles_bijective` listed only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The
heartbeat-option comment was then added to satisfy the style linter.

Final validation: the degree-zero private-helper version compiled without
warnings in 51.1 seconds. Its explicit axiom print lists exactly `propext`,
`Classical.choice`, and `Quot.sound`.
