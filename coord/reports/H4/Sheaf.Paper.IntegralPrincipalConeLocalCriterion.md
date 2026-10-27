## What changed

Prove `WeilConjectures.IntegralPrincipalCone.localCriterion` without changing its
statement, its two definitions, or any existing source-library declaration.
The proof follows the singleton Koszul reflector route already recorded by the node.

The new restriction modules construct direct restriction of module sheaves across an
equivalence of sites, compare its Hom complexes, derived internal Hom, sheafification,
section localizations and exact derived slice restriction, and transfer the covering-sieve
local divisibility condition. `NativePrincipalCompletenessSmallModel` assembles these
comparisons for the canonical `AsSmall` model. Every construction retains the independent
site-object, site-arrow and coefficient universes.

`PrincipalIdealLocalTestCriterion` identifies the covering-sieve tests with the existing
principal image-ideal completeness predicate. `PrincipalConeKoszulRoosComparison` compares
the scalar cone tower with the tensor Koszul tower and its prescribed augmentation.
`PrincipalConeSmallSiteCriterion` applies the existing ringed reflector and normalized
presentation comparison. `PrincipalConeExactEquivalence` proves that an additive
equivalence preserves the cone completion and the specified zero-homotopy unit.
`NativePrincipalConeCriterion` combines these results before shrinking the site. The item
then compares its original representative-based slice test with exact derived restriction,
uses exact pro-etale products and transports along the given `Q(P) ≅ K`.

All new data are direct constructions or canonical comparisons. No definition selects an object
from an unproved mere-existence theorem. The existing reflector is used only through
its theorem about a presentation and the normalized comparison for that presentation.
No existing statement, definition, visibility or public import changes. No forced
adaptations or change records are needed.

## Proved and sorry left

Closed: `WeilConjectures.IntegralPrincipalCone.localCriterion`
(node `lem-pur-integral-principal-cone-local-criterion`): 1 of the original 1 holes.
Added: 0 holes. Split off with `sorry`: 0. No `sorry` remains in any delivered module.
Every new helper statement and every data-construction obligation is proved in this packet.

The proof uses the already-stated `CategoryTheory.ringedKoszulCompletionReflector` and
`CategoryTheory.principalKoszulRoos_presentation_comparison`. Their existing holes are
not claimed closed by this delivery; they are the intended remaining proof dependencies.
The scalar-cone comparison uses no regularity, K-flatness or boundedness. The constructions
and arguments cover a zero scalar, an invertible scalar, the zero complex and empty covers.

Validation: all 16 delivered modules compile through the required remote compiler with
no errors or warnings, within the per-file limit. The original definitions and theorem
signature are unchanged. The required delivery command also performs the project's
compilation, signature, import, node and axiom checks.

## No longer needed

The proof does not use the planned small-universe-only
`Sheaf.CategoryTheory.RingedEquivalenceSlices`
(`lem-weil-pbc-ringed-equivalence-slices`) or
`Sheaf.CategoryTheory.RingedEquivalenceLocalTests`
(`lem-weil-pbc-ringed-equivalence-local-tests`). The independent-universe restriction
comparisons replace their role here. No source-library declaration or other module is
withdrawn.

`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
(`lem-weil-proetale-countable-products-exact`) is unnecessary for this proof: the existing
stronger `Sheaf.AlgebraicGeometry.ProEtaleProductsExact` (`det-pe-products-exact`) supplies
the actual coefficient-universe instance directly. The strict Roos model remains used
through the normalized Koszul presentation comparison.

Removed exploratory proof imports from `NativeRingedRestrictionHom`:
`Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses`,
`Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`Mathlib.CategoryTheory.Sites.Equivalence`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
The Hom-complex comparison needs only ordinary module sheaves, limits and the existing
Hom-complex projections. The tensor-cone comparison also removes the exploratory import
`Sheaf.Paper.IntegralPrincipalConeQuotientComparison`: every finite map is an actual
isomorphism, so product and cone isomorphisms suffice. It uses the existing normalized
cocone-lift naturality from `IntegralDerivedOperationsOnSlices` and the proved cone-square
comparison in `PrincipalConeExactEquivalence`. Other helpers keep proof-only imports private.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-equivalence interfaces identify the site and coefficient universes.
They cannot be applied directly to the actual pro-etale site, whose object and arrow
universes differ. The new direct restriction API supplies the missing comparisons;
the mathematical route and unit's realized route are retained.

The ringed-reflector node's current Lean attachment points to its completed-coefficient
specialization. This proof uses the retained general companion
`CategoryTheory.ringedKoszulCompletionReflector` in
`Sheaf.CategoryTheory.RingedKoszulCompletionReflector`, whose docstring names that same
node, on the genuinely small `AsSmall` model. Its general statement is the one needed
here; no specialization is silently used outside its universe constraints.

A dependency traversal also found an existing metadata cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. Both declarations are already proved
in `RingHomExtensionDifferential.lean`; their recorded proof edges need reconciliation.
These two node files are unchanged by this packet.

## New nodes

`def-pur-ringed-principal-local-tests` (`Sheaf.CategoryTheory.RingedPrincipalLocalTests`): For a ringed site with coefficient universe containing its object and arrow universes, define a compatible slice section from one terminal value, local divisibility by a global section using a covering sieve, and the localization test as derived internal Hom from the sheafified localization into exact derived slice restriction. Principal local completeness means zero for all such tests at locally divisible sections. Every slice section is determined by its terminal value; local completeness is invariant under derived isomorphism. Fully proved; no hole added.

`lem-pur-native-principal-completeness-small-model` (`Sheaf.CategoryTheory.NativePrincipalCompletenessSmallModel`): Let C be a site of object size c and arrow size v and let R have coefficient size q=max(c,v,r). Equip AsSmall at size q with the induced topology and its canonical equivalence to C. Under the displayed global and slice sheafification and derived-category structures, an object N is principally locally complete for a if and only if its exact restriction is principally locally complete for the restricted section on AsSmall. Fully proved; no hole added.

`lem-pur-native-principal-cone-criterion` (`Sheaf.CategoryTheory.NativePrincipalConeCriterion`): For a site of object size c and arrow size v, a commutative ring sheaf of size q=max(c,v,r), and the displayed global and slice sheafification, derived-category and countable-product hypotheses on the site and its AsSmall model, the principal cone completion of any scalar chain endomorphism μ is principally locally complete. Q(P) is principally locally complete if and only if the specified principal cone unit is invertible. No site-universe identification, regularity, K-flatness or boundedness is used. Fully proved; no hole added.

`lem-pur-native-ringed-restriction-derived-hom` (`Sheaf.CategoryTheory.NativeRingedRestrictionDerivedHom`): For continuous restriction along an equivalence inducing equivalences on slices, suppose the corresponding module restriction is an equivalence and both sites admit the indicated additive sheafification and derived categories. Restriction of derived internal Hom(L,M) is isomorphic to derived internal Hom of the two restricted objects. The derived-category universes may differ. Fully proved; no hole added.

`lem-pur-native-ringed-restriction-divisibility` (`Sheaf.CategoryTheory.NativeRingedRestrictionDivisibility`): For a dense equivalence F:C→D of sites, a commutative ring sheaf R on D, a compatible global section a, U in C and a compatible section s on D/FU, s is locally divisible by a on a covering sieve if and only if its restricted section on C/U is locally divisible by the restricted a. This holds for zero sections, arbitrary covering sieves, and independent site and coefficient universes. Fully proved; no hole added.

`lem-pur-native-ringed-restriction-equivalence` (`Sheaf.CategoryTheory.NativeRingedRestrictionEquivalence`): An equivalence of categories carrying the indicated dense-subsite topologies induces the equivalence of module sheaves over a commutative ring sheaf and its restriction. Its structural ring maps are the original equivalence unit and counit maps. Direct module restriction is isomorphic to the forward structural functor and hence is an equivalence, without identifying site and coefficient universes. Fully proved; no hole added.

`lem-pur-native-ringed-restriction-hom` (`Sheaf.CategoryTheory.NativeRingedRestrictionHom`): Let F:C→D be a continuous equivalence of sites such that every induced slice functor is an equivalence, and let R be a commutative ring sheaf. Direct module restriction is additive and agrees with the structural ringed pushforward by an identity change-of-scalars isomorphism. For every two cochain complexes L,M, restriction of their sheaf Hom complex is isomorphic to the sheaf Hom complex of their restrictions. The coefficient universe contains both site object and morphism universes; no equality of these universes is assumed. Fully proved; no hole added.

`lem-pur-native-ringed-restriction-local-test` (`Sheaf.CategoryTheory.NativeRingedRestrictionLocalTest`): Under a dense equivalence of ringed sites with the indicated sheafification and derived-category structures globally and on slices, restriction of the principal localization test for (N,U,s) is isomorphic to the test for the restricted derived object, object and compatible slice section. The test uses exact derived slice restriction and sheafified sectionwise localization; no equality of site and coefficient universes is assumed. Fully proved; no hole added.

`lem-pur-native-ringed-restriction-localization` (`Sheaf.CategoryTheory.NativeRingedRestrictionLocalization`): Continuous and cocontinuous restriction of a commutative ring sheaf commutes with sheafified sectionwise localization at any compatible global section. The restricted section is its actual pullback along the site functor. Assume the displayed commutative-ring and additive sheafification structures on both sites; site and coefficient universes remain independent. Fully proved; no hole added.

`lem-pur-native-ringed-restriction-sheafification` (`Sheaf.CategoryTheory.NativeRingedRestrictionSheafification`): For a continuous and cocontinuous functor of sites, a commutative ring sheaf R, and a module presheaf P over its ring presheaf, direct restriction of the module sheafification of P is isomorphic to sheafification of the restricted module presheaf. Assume additive sheafification and its locally bijective criterion on both sites, with the common coefficient universe containing both site sizes. Fully proved; no hole added.

`lem-pur-native-ringed-restriction-slices` (`Sheaf.CategoryTheory.NativeRingedRestrictionSlices`): A dense equivalence of sites induces a dense equivalence on every slice. Direct module restriction commutes with over-site restriction, and both global and slice module restrictions are equivalences. With the displayed additive sheafification and derived-category structures, the square formed by their exact derived functors commutes by a natural isomorphism, with independent site and coefficient sizes. Fully proved; no hole added.

`lem-pur-principal-cone-exact-equivalence` (`Sheaf.Algebra.Homology.PrincipalConeExactEquivalence`): For an additive equivalence H between abelian categories with countable products, and any cochain endomorphism μ:P→P, H applied degreewise to the principal completion is isomorphic to the principal completion of H(μ). Under this isomorphism the image of the specified normalized degree-zero completion unit is the specified completion unit. This is a chain-level comparison, before derived localization. Fully proved; no hole added.

`lem-pur-principal-cone-koszul-roos-comparison` (`Sheaf.Paper.PrincipalConeKoszulRoosComparison`): On a small ringed site, let P be any cochain complex and μ its scalar endomorphism for a compatible global section a. The principal cone completion of μ is isomorphic in the derived category to the strict tensor singleton-Koszul Roos complex. The comparison sends the specified principal cone unit to the prescribed Koszul Roos unit. The statement uses the displayed countable-product and derived-category hypotheses and requires no regularity or K-flatness. Fully proved; no hole added.

`lem-pur-principal-cone-small-site-criterion` (`Sheaf.Paper.PrincipalConeSmallSiteCriterion`): On a small ringed site, assume the displayed derived categories globally, on slices and on strict countable towers, and exact countable products. For any compatible global section a and its scalar chain endomorphism μ on P, Q of the principal cone completion is principally locally complete for a. Moreover Q(P) is principally locally complete if and only if the specified principal cone completion unit becomes an isomorphism. Fully proved; no hole added.

`lem-pur-principal-ideal-local-test-criterion` (`Sheaf.Paper.PrincipalIdealLocalTestCriterion`): On a small ringed site with coefficient universe equal to its site universe, let I be the image ideal sheaf of multiplication by a compatible global section a. For any derived module object N, the covering-sieve principal local completeness condition is equivalent to IsLocallyDerivedRingedIdealComplete for I and its actual image inclusion. No regularity, boundedness or invertibility assumption is imposed on a or N. Fully proved; no hole added.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
