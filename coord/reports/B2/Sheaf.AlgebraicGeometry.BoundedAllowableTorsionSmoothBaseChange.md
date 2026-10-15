## What changed

Proved `AlgebraicGeometry.Etale.isIso_abelianDerivedBaseChangeArrow_of_bounded_allowable_torsion`
without changing its signature. The proof transfers the degree-zero smooth-base-change
result through the equivalence between abelian sheaves and ULift Z-module sheaves, then
uses the library's already proved bounded triangulated devissage. A second devissage
proves allowable torsion of the output, using qcqs higher direct images, geometric-field
extension, and the inverse-image stalk comparison. The final full-subcategory assertion
uses reflection of isomorphisms by its inclusion.

Added the fully proved module
`Sheaf.AlgebraicGeometry.AbelianDerivedExchangePlusCompatibility`, identifying the
canonical unbounded arrow with the bounded-below exchange, conjugated by the canonical
right-derived comparison isomorphisms. Its private helpers prove restriction of the
derived adjunction, compatibility of the inverse-image square, and equality of adjoint
transposes. No monoidal or flat-resolution structure on abelian groups is assumed.

Repaired the returned delivery against the current repository file containing A4's
landed natural-transformation interface. Retained
`abelianDerivedBaseChangeTransformation` and its signature, and kept
`abelianDerivedBaseChangeArrow` as its component, exactly as in the current repository.
Only the transformation's body and explanatory docstring now use the equivalent mate
presentation. Both existing public signatures, the arrow body, and public imports
are unchanged. The private proved
`abelianDerivedBaseChangeTransformation_eq_pushforward` in the compatibility module
identifies the mate with A4's entire functor-category construction. The existing private
`abelianDerivedBaseChangeArrow_eq_pushforward_formula` recovers its component formula.
See `coord/changes/B2-abelian-derived-exchange-mate.md`.

The five delivered modules compile without warnings. The bounded-below caller has only
the shared-lemma relocation described below; its public signatures and proof uses are
unchanged. `EtaleLocalityBaseChange` remains unchanged. No module held by another group
is adapted. The unit
`sk-rem-rest` has no realized statement or proof steps; no required unit route is bypassed.
Updated existing node copies from the current repository before applying the proof-route
changes, preserving A4's new declaration attachment and maintainer review metadata.
All existing node statements and all target signatures are unchanged. The definition
body change reopens semantic review for dependent targets, with the proved equality
as the evidence that its meaning is unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.isIso_abelianDerivedBaseChangeArrow_of_bounded_allowable_torsion`
(node `sbc-thm-bounded-allowable-torsion`). Added zero holes. No declaration in any of the
five delivered modules contains `sorry`.

Also proved the new public comparison theorem
`AlgebraicGeometry.Etale.abelianDerivedBaseChangeArrow_eq_plus`
(node `lem-sbc-abelian-derived-exchange-plus-compatibility`). Its `#print axioms` output
contains only `propext`, `Classical.choice`, and `Quot.sound`. The fresh check against
the current compiled library gives exactly these same three standard axioms for the
main theorem and the arrow definition as well: pre-existing dependency obligations
have now been closed. No declaration in the delivered set adds a hole. The delivered
files compile in approximately 1.8, 2.4, 19.6, 9.6 and 6.8 seconds. The main signature, both
existing base-change signatures, and visibility are unchanged. The private
`allowable_upperStar` in the unclaimed bounded-below caller is relocated to a shared
module as a public theorem; the original caller now imports it. The current import-closure comparison confirms
exactly the nine pruned Sheaf modules below.

Repair of the returned delivery removed the duplicate private declaration
`allowableTorsionSheafProperty_upperStar`. The existing `allowable_upperStar` lemma was
private to the downstream `BoundedBelowDerivedSmoothBaseChange`, so importing that
module into the item would form a cycle. Moved the existing lemma and its unchanged
proof into the new shared module `Sheaf.AlgebraicGeometry.AllowableTorsionInverseImage`,
where it is public. Both the item and the bounded-below caller now import and use it.
There is exactly one declaration of the fact, with its original name and statement.
The bounded-below module is unclaimed, so this relocation is allowed by the forced
adaptations update; this is not an adaptation of another group's held module.
See `coord/changes/B2-allowable-torsion-upper-star-shared.md`.

The relocated fully proved theorem `AlgebraicGeometry.Etale.allowable_upperStar` has
node `lem-sbc-allowable-torsion-upper-star`; it adds no hole. For the empty prime set,
only annihilator 1 is possible, so all stalks are zero and the same proof applies.
The proof also covers zero sheaves and arbitrary morphisms without smoothness or qcqs
hypotheses. The shared theorem is used with exactly the original arguments by both
callers.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`
- `Sheaf.AlgebraicGeometry.TruncationExchangeCouple`
- `Sheaf.AlgebraicGeometry.FiniteRangeComparison`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` (already supplied by
  the retained public `SmoothBaseChange.Derived` import).
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper` (replaced by the WeilConjectures module
  providing the stalk additivity API).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk` (the relocated shared
  inverse-image lemma now contains the sole direct use of its stalk comparison).

The old finite spectral-sequence comparison route is unnecessary. These nine Sheaf
modules leave this item's transitive import closure; their ten associated nodes are
not used by this proof:

| module | node(s) |
| --- | --- |
| Sheaf.AlgebraicGeometry.HypercohomologyFiltrations | def-weil-pbc-hypercohomology-filtrations |
| Sheaf.AlgebraicGeometry.TruncationExchangeCouple | lem-weil-pbc-truncation-couple-morphism; def-weil-pbc-truncation-exact-couples |
| Sheaf.AlgebraicGeometry.TruncationExchangeAbutment | lemma-weil-pbc-exact-couple-abutment |
| Sheaf.AlgebraicGeometry.FiniteRangeComparison | sbc-lem-finite-range-comparison |
| Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative | lem-weil-pbc-derived-stalk-conservative |
| Sheaf.CategoryTheory.ExactCoupleMorphism | lem-sp-couple-morphism |
| Sheaf.CategoryTheory.ExactFunctorCouple | lem-sp-exact-functor-couple |
| Sheaf.CategoryTheory.SpectralSequencePageInduction | lem-sp-page-induction |
| Sheaf.CategoryTheory.TruncationCoupleExact | lem-sp-truncation-couple-exact |

No files are withdrawn: other proof branches may still use these modules. Geometric
stalk exactness remains an indirect ingredient of the existing allowable-torsion
triangulated-category API, although the explicit finite-filtration step was removed.
The historical `tool_uses` and `split_report` fields of the original node were retained
as required by the restriction on fields workers may edit; the updated `proof_deps`
records the actual route.

## Where the brief, the DAG or earlier work was wrong

The planned hypercohomology/exact-couple route is valid but unnecessary: the source
library already proves bounded triangulated devissage for natural transformations.
It applies directly once the canonical unbounded/bounded-below exchange compatibility
is supplied. The DAG did not state that compatibility, which is now proved explicitly.

The first delivery used an earlier copy of `BaseChangeMapAbelianAndSets`, predating
A4's landed natural transformation. The landing tools correctly returned that stale
file. This repair starts from the current file, retains the naturality interface and
arrow component definition, and places the mate refactor in the transformation body.
The comparison with A4's current construction is proved explicitly. Its bounded-below
caller therefore retains the definitional equality used in its naturality proof.
The current node's declaration list and review metadata are also preserved.

The landing return identified the duplicate inverse-image torsion lemma. Direct reuse
from its old location is impossible: `import_direction.py may` confirms that importing
`BoundedBelowDerivedSmoothBaseChange` into this item would create a cycle, and the lemma
was private. The repair therefore relocates that existing proof into a common upstream
module and imports it from both callers, removing both duplicate declarations.

The qcqs higher-image statement is phrased at algebraically closed geometric points,
whereas allowable torsion quantifies over separably closed points. The proved
`Scheme.isIso_pointSmallEtalePrecomp_sheafFiber` supplies the necessary passage to an
algebraic closure. Likewise, abelian groups have no required functorial-flat-resolution
instance: the degree-zero smooth theorem is used through ULift Z-module coefficients
and the forgetful derived-exchange comparison.

## New nodes

`lem-sbc-abelian-derived-exchange-plus-compatibility` is the fully proved restriction
identity for the canonical abelian derived exchange, valid for every chosen Cartesian
square and bounded-below input, without geometric or torsion hypotheses. Its module has
one public theorem and only proved private helpers. The proof is by restriction of the
adjunction, comparison of square isomorphisms, and equality of counit transposes.

Change record: `coord/changes/B2-abelian-derived-exchange-mate.md`.

`lem-sbc-allowable-torsion-upper-star` records the existing inverse-image torsion
preservation lemma relocated from the bounded-below module. Its statement and proof
are unchanged apart from making it public for the two callers. It uses only the
existing allowable-torsion definition and geometric inverse-image stalk comparison.
Both callers' node proof dependencies now cite this shared result. No additional
mathematics or unproved obligation is introduced.

## Second reading by B2

1. **Signatures and accidental changes.** I compared every delivered module with the
repository versions. The target theorem, the existing base-change transformation and
arrow, and the bounded-below theorem retain their signatures byte for byte. The only
definition-body change is the declared mate presentation of the transformation; the
compatibility module proves equality with the previous construction. Verdict: pass.

2. **Proof and axioms.** I compiled all five modules with `lcompile.py --all` in import
order. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by` declarations in the delivered files. The resulting declarations use
only the permitted standard axioms. Verdict: pass.

3. **Split-off statements.** I checked both added nodes against their Lean declarations,
tested the inverse-image torsion argument at empty prime sets and zero stalks, and
searched Mathlib and the project for existing equivalents. Each statement is strictly
smaller than the target and needed by the proof; neither is a restatement of the item.
Verdict: pass.

4. **Pruning and route.** The bounded proof uses the existing bounded triangulated
devissage and the explicit unbounded/bounded-below compatibility, removing the old
hypercohomology route. Direct proof-only imports listed under “No longer needed” are
absent, and the shared inverse-image lemma removes the duplicate private declaration.
The `sk-rem-rest` unit has no realized route to bypass. Verdict: pass.

5. **DAG agreement.** I checked the changed node copies and both new node files. Their
Lean declarations, proof steps, `proof_deps`, `proof_origin`, source, unit, and chapter
agree with the delivered proofs; the forced-adaptation and definition-change records
name all affected modules. Verdict: pass.

I changed only this report section during second reading; no Lean source or DAG repair
was necessary.

Change record: `coord/changes/B2-allowable-torsion-upper-star-shared.md`.
