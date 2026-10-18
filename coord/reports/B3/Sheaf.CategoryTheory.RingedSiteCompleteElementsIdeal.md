## What changed

Proved `CategoryTheory.ringedSite_complete_elements_ideal` without changing its
signature or any existing definition. Its carrier is the actual completeness
predicate. Zero, addition and scalar multiplication give an ideal; restriction,
covering-sieve descent and `Ideal.span_le` give the remaining clauses.

Added five proved supporting modules: `RingedSiteCompleteElementMultiplication`,
`RingedSiteCompleteElementsLocal`, `RingedSiteCompleteElementAddition`,
`RingedSiteLocalizationCech`, and `TwoLocalizationExact` (the first four under
`Sheaf.CategoryTheory`, the last under `Sheaf.RingTheory`). Multiplication uses
colimits, flatness and Hom-complex currying; locality uses restriction comparisons
and separatedness of cohomology sheaves. Addition uses the proved binary Cech row
and triangulated RHom. The Cech proof constructs actual presheaf maps, proves
pointwise exactness by Bezout and denominator clearing, identifies the sequential
and fraction localizations, and applies exact sheafification.

All six modules compile through the server compiler. No axioms or arbitrary data
from an unproved mere existence statement were introduced. The colimit comparison
uses the existing localization theorem whose formula determines its isomorphism.
Zero rings, zero denominators, empty covering sieves and zero generator families
are covered by the proofs. No existing consumer needs adaptation.

## Proved and sorry left

Closed the original one hole:
`CategoryTheory.ringedSite_complete_elements_ideal`
(`lem-weil-pbc-ringed-derived-complete-elements-ideal`).

Added zero holes. There are zero `sorry`s in every delivered module. The five new
public theorems are proved:

- `CategoryTheory.ringedSite_completeElement_mul`.
- `CategoryTheory.ringedSite_completeElements_locality`.
- `CategoryTheory.ringedSite_completeElement_add`.
- `CategoryTheory.ringedSite_localization_cech`.
- `localization_two_exact`.

These proofs use the existing declared derived-Hom and localization-colimit APIs;
the delivery does not claim to close holes in those pre-existing dependencies.
There are no split-off obligations left for another worker.

## No longer needed

Removed all five original proof imports from the item:
`Mathlib.RingTheory.Localization.Away.Basic`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
`Sheaf.Algebra.Homology.DerivedInternalHom`,
`Sheaf.CategoryTheory.RingedSiteModules`, and
`Sheaf.Paper.RingedLocalizationRHomCalculus`.
The needed interfaces are imported through the actual supporting proofs; this is
not a claim that the shared derived-Hom or module-category definitions are unused.

The route no longer uses node
`lem-weil-pbc-ringed-localization-rhom-calculus` or module
`Sheaf.Paper.RingedLocalizationRHomCalculus`: multiplication is proved directly
using tensor products of the defining sequential diagrams, and locality directly
using exact slice restriction. It also no longer uses
`lem-weil-pbc-standard-covering-glue`: the binary ring row is proved directly from
Mathlib's coprime-power and localization APIs. The original hand-written cone and
local-boundary-chase step is replaced by the existing triangulated RHom exactness
interface. No unit statement or unit proof step is bypassed.

During development also removed unused biproduct-preservation and additive-functor
imports from the addition module; its biproduct zero argument explicitly maps the
sum of the two projection-inclusion composites.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The original plan is valid,
but several categorical comparisons were implicit: preservation of the sequential
localization under slice restriction, its comparison with sheafified fractions,
and composition of the actual chosen derived restriction. These are now proved
as private helpers. The DAG has been updated to the route actually implemented.

## New nodes

`lem-weil-pbc-ringed-complete-element-multiplication`: original step 2, proved by
flat sequential colimits and tensor-Hom currying. No remaining hole.

`lem-weil-pbc-ringed-complete-elements-locality`: original step 5, proved by exact
slice restriction and sheaf-separatedness descent. No remaining hole.

`lem-weil-pbc-two-localization-exact`: the ordinary ring part of original step 3,
proved by denominator clearing and Bezout identities for coprime powers. No
remaining hole.

`lem-weil-pbc-ringed-site-localization-cech`: the presheaf and sheaf part of original
step 3, including the comparison with the actual sequential localization. No
remaining hole.

`lem-weil-pbc-ringed-complete-element-addition`: original steps 3 and 4, combining
the Cech row, multiplication closure and exact contravariant RHom. No remaining
hole. No change record is needed because existing signatures and definitions
are unchanged.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
