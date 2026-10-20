## What changed

`Sheaf.Paper.TorsionLimitSheafCompleteness` now has a complete Lean proof of all five
clauses, without changing the theorem's signature. It uses the natural multiplication
difference on countable powers, the abelian five lemma, preservation of ordinary limits,
a nilpotent product-shift argument, covering-sieve descent, and degreewise chain
invertibility. No transition map is assumed surjective.

`TorsionCompletionDefinitions` extracts the 17 existing constructions unchanged to avoid
an import cycle between the ideal-power lemma and its consumer. `MultiplicationDifference`
constructs the actual countable-power functor and its natural endomorphism; additivity
and preservation of limits are proved. `TorsionCompletionIdealPowers` proves section
power membership for the actual kernel ideal by local constant lifts and separatedness.
`ProEtaleMultiplicationDifferenceCriterion` proves the source criterion needed by the
consumer for restrictions of ambient modules and complexes. It transports exact products
through the actual site and module equivalences, identifies the actual sectionwise
localization with the telescope colimit, and conjugates tower endomorphisms through the
product, derived restriction and degree-zero comparisons. In particular, this result has
also been proved during this session. The generic single-complex comparison stays
inside this module and is proved for abstract abelian categories, so its specialization
does not repeatedly unfold the module-sheaf construction.

Validation: `lcompile.py --all` compiled all five files cleanly. The criterion took
23.4 seconds and the item took 17.3 seconds; unchanged dependencies were served from
the compiler cache. All temporary profiling and file-stop commands have been removed.
The original 17 constructions compare verbatim with the extracted declarations, and
the item's theorem signature is unchanged.

## Proved and sorry left

Closed the item's one direct hole:
`AlgebraicGeometry.Scheme.torsionLimitSheaf_completeness`.

No direct holes added or left. The item and all four new modules have zero `sorry`.
The independent multiplication-difference criterion is proved from existing declarations,
including the already proved exact-product and local Hom/tower calculations. The packet
closes one direct hole and adds zero; there is no unfinished split-off theorem. Existing
library dependencies retain their own proofs and axiom obligations.

Proved without direct holes:
`AlgebraicGeometry.Scheme.proEtale_multiplicationDifference_criterion`,
`AlgebraicGeometry.Scheme.torsionCompletionIdeal_section_pow`,
`CategoryTheory.countablePower_additive`, and
`CategoryTheory.countablePower_preservesLimitsOfShape`.
All private helpers in the packet are proved.

Edge cases checked: zero ring, zero and unit ideals, exponent zero in the ideal-power
lemma, empty covering sieves, zero modules, zero and invertible sections in the difference
criterion, arbitrary inverse-system maps, and complexes with no boundedness assumption.
The original boundedness and Noetherian hypotheses remain in the theorem signature.

## No longer needed

No mathematical node or module of the original plan is pruned: exact pro-etale products,
weakly-etale localization, derived products and the local Hom tower criterion remain
needed through the independent criterion. None of the unit's statements or proof steps
is bypassed. No upstream declaration or module is removed or weakened.

Removed direct imports from the item (public statement imports are retained transitively
through the definitions module; proof imports not used by the assembled proof were removed):

- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Mathlib.Algebra.Category.Ring.Limits`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.HomologicalComplex`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`
- `Mathlib.CategoryTheory.Functor.OfSequence`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.LocalHomTowerCriterion`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`

The original proof dependencies `lem-weil-proetale-weakly-etale-localization`,
`lem-weil-proetale-countable-products-exact`, `lem-weil-derived-limit-products-core`,
`lem-weil-pbc-local-hom-tower-criterion` and `def-weil-derived-limit` are no longer direct
uses of the upper proof. The first four occur in the criterion's actual proof; the last
is used through derived-limit existence and the local Hom theorem. They are not claimed
as globally pruned. The original three tool approvals are preserved unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original first proof step combines several nontrivial
formal comparisons: equivalence of coefficient-sized slices with raw pro-etale sites,
telescope localization with the genuine sectionwise localization, exact termwise products
with derived products, and componentwise invertibility with derived vanishing. The existing
local-Hom theorem takes an ambient derived object and a supplied tower-limit witness;
it does not directly state the arbitrary-slice sheaf and complex criterion required here.
The separate criterion is therefore deliberately restricted to ambient objects, which is
exactly what the consumer uses. Its proof supplies the derived-limit witness and all
localization, single-complex and product comparisons. All steps of the original plan
have been implemented in Lean. The kernel ideal power step is proved directly for the
actual quotient kernel through constant sheafification.

## New nodes

`def-weil-pbc-torsion-completion-sheaf-model` attaches the unchanged 17 extracted
constructions to their own module. Change record:
`coord/changes/torsion-completion-definitions-extraction.md`.

`def-weil-pbc-multiplication-difference` records countable powers and identity minus
the section-multiplication shift, including the proved additive and limit APIs.

`lem-weil-pbc-torsion-completion-ideal-powers` is fully proved, including the exponent-zero
and empty-cover cases. It supplies the genuine kernel-ideal input to nilpotence.

`lem-weil-pbc-proetale-multiplication-difference-criterion` is fully proved. Its node and
docstring describe the implemented exact-product, telescope, derived-product comparison,
fully faithful single-functor and chain-isomorphism argument. Blueprint searches for
multiplication tower,
constant quotient, extended ideal and 0997 found no equivalent imported blueprint node.
Mathlib searches ran through leansearch, leanfinder, loogle and grep; ordinary coefficient
power membership is used, while none states the sheaf criterion.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
