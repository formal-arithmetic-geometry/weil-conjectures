## What changed

Closed the original proof hole in
`AlgebraicGeometry.ProEtale.isZero_rightDerived_globalSections_comparisonUpperStar_of_isAffine`.
Its signature and four public imports are byte for byte unchanged. The proof uses finite
refinements by affine ind-etale objects, the existing simultaneous etale Cech presentation,
categorical filtered-colimit exactness, injective-presheaf Cech exactness, and a categorical
finite-cover vanishing criterion. This retains the two-limit route of Stacks 099U.

Six new modules construct the categorical argument:
`AffineComparisonCategoricalCechSystem`, `CategoricalInjectiveCechExactness`,
`CategoricalFiniteCoverLocalZero`, `CategoricalFiniteCoverLocalEpi`,
`CategoricalFiniteCechSectionsEpi`, and `CategoricalFiniteCechCriterion`.
All constructions are explicit. No data is chosen from an unproved existence theorem.

The existing, unclaimed `AffineComparisonInjectiveVanishing` module exposes
`affineProEt_cechNerve` and `affineProEt_finite_refinement` in place, with their exact
signatures and proof bodies unchanged. Their signature dependencies
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale` and
`WeilConjectures.CategoryTheory.Sites.CechComplex` are now publicly imported there.
The item reuses these helpers instead of duplicating them. The local product-instance
registration and the helper visibility changes have the two change records below.
No target statement or existing definition changes; there are no forced adaptations.

The second reading found that the existing upstream theorem
`CategoryTheory.ShortComplex.exact_iff_evaluation` already supplies the pointwise
exactness test. `CategoricalFiniteCoverLocalEpi`, `CategoricalFiniteCechCriterion`,
and `AffineComparisonCategoricalCechSystem` now import its module only for their proofs
and use it directly. The new duplicate public theorem
`CategoryTheory.Sheaf.shortComplex_exact_of_evaluations` and its change record are removed.
The criterion no longer directly imports the local-epimorphism module just for that helper.
Its node and the other affected proof descriptions are updated.

## Proved and sorry left

Original holes closed: **1 of 1**,
`AlgebraicGeometry.ProEtale.isZero_rightDerived_globalSections_comparisonUpperStar_of_isAffine`.
The assigned module contains zero holes.

New holes added: **1**,
`CategoryTheory.Presheaf.hom_eq_zero_of_sheafification_zero`, node
`stage3-categorical-finite-cover-local-zero`, in
`lean/Sheaf/CategoryTheory/CategoricalFiniteCoverLocalZero.lean`.
It has exactly `by sorry`, a source and a complete proof in words in its docstring.
It asserts detection of maps out of a zero-sheafification presheaf by finite-cover
restriction kernels. The remaining work is the categorical plus/sheafification
local-kernel argument, using AB5, finite refinements and transfinite plus.

This is a **decomposition, net zero holes**. It does not assert that the target's
import closure is proved. The following principal declarations have complete proofs:

- `AlgebraicGeometry.ProEtale.AffineEtaleCechSystem.categoricalOriginalExactAt`;
- `CategoryTheory.Presheaf.exactAt_categoricalCech_of_injective`;
- `CategoryTheory.Sheaf.hom_eq_zero_of_finite_cover_lifts`;
- `CategoryTheory.Sheaf.epi_app_of_finite_cech_exact_one`;
- `CategoryTheory.Sheaf.isZero_rightDerived_eval_of_finiteCech`.

All eight delivered modules compile through `lcompile.py --all`. A scratch axiom probe
of all principal declarations shows only `propext`, `Classical.choice`, `Quot.sound`
and, where the outstanding locality input is used, `sorryAx`. The categorical limit
transfer and injective contraction have only the three permitted axioms. The unchanged
original consumer `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`
also compiles against the sandbox overlay. The delivery dry run performs the full
module and declaration checks again.

## No longer needed

Removed five proof-only imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleComparisonSections`;
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`;
- `Sheaf.Paper.EtaleFiniteDataDescent`;
- `Sheaf.RingTheory.IndEtaleStability`;
- `Sheaf.RingTheory.IndPrincipalZariski`.

The former direct proof-dependency entries
`lem-weil-pbc-ind-etale-stability`, `def-weil-pbc-ind-etale-algebra`,
`def-weil-pbc-site-comparison-morphism`, `def-sp-grothendieck-abelian`,
`lem-weil-pbc-comparison-sections`, `lem-weil-pbc-etale-finite-data-descent`,
`lem-weil-pbc-limit-affine-stage`, and `def-sp-injective-resolutions` are replaced by
the assembled presentation and categorical lemmas. Some remain indirect or statement
dependencies. No existing module is withdrawn or claimed to leave the target closure.
No maintainer `tool_uses` approval is removed or changed.

Removed duplicate geometric proofs from the item and reused the existing helpers in
`AffineComparisonInjectiveVanishing`. Its abelian-coefficient theorem is not used by
this proof, but its module is needed for the geometric helpers and is not pruned.
The direct `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over` import used in an
older returned version is unnecessary after that reuse.

The new categorical-system module does not need
`Mathlib.Algebra.Homology.HomologicalComplexLimits`.
The second reading removes the duplicate pointwise-exactness theorem, the criterion's
proof import of `Sheaf.CategoryTheory.CategoricalFiniteCoverLocalEpi`, and its matching
direct node dependency. That module remains an indirect dependency through the
section-epimorphism theorem. `ShortComplex.exact_iff_evaluation` supplies the shorter
route in all three affected modules. The attempted removal of the item's
`WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine` import failed because
`Scheme.AffineProEt.ofEtale` then becomes unavailable; the required import is retained.

## Where the brief, the DAG or earlier work was wrong

The original plan supplied an abelian-group Cech criterion but not the categorical
finite-cover criterion or cofree contraction. Applying Hom from arbitrary coefficient
objects does not preserve epimorphisms, so the categorical proof uses coefficient
epimorphic refinements instead of elementwise lifts. The sole remaining locality
statement is strictly smaller than affine derived vanishing: it has no injectivity,
geometry, positive Cech homology or derived functor in its conclusion.

The source CechCriterion documentation calls Lemma 21.10.9 Tag 03F7; its verified tag
is 03F9, and the preceding section-surjectivity lemma has Tag 03F8. The new documents
use these tags. The Stacks sources of the locality argument concern ordinary
sheafification; the node and docstring explicitly describe the categorical extension
using AB5 and transfinite plus.

The earlier returns correctly identified duplicated geometric and pointwise-exactness
helpers. The geometric proofs are reused in place. The previous pointwise-helper
repair still duplicated the upstream `ShortComplex.exact_iff_evaluation`; the second
reading now removes that duplication altogether. No false statement was found.

## New nodes

`stage3-affine-comparison-categorical-cech-system`: constructs complex diagrams and
section cocones, proves finite-product colimits, and transfers stage exactness.

`stage3-categorical-injective-cech-exactness`: constructs the cofree categorical
presheaf and the Hom comparison with the existing ordinary cofree contraction;
exactness is detected by the kernel representable and transferred through a retract.

`stage3-categorical-finite-cover-local-zero`: the sole outstanding theorem, with the
local restriction-kernel and transfinite-plus proof described above.

`stage3-categorical-finite-cover-local-epi`: proves the sheaf-epimorphism local-lift
test using the presheaf cokernel, finite-product exactness and coefficient refinements.

`stage3-categorical-finite-cech-sections-epi`: proves zero-cocycle compatibility,
sheaf gluing, the first-degree correction and epic quotient evaluation.

`stage3-categorical-finite-cech-criterion`: proves dimension shifting using the
section-epimorphism theorem, Cech homology sequence and the existing generic
`rightAcyclic_of_epi_map_g` theorem.

Change records:
`coord/changes/h4-affine-comparison-local-products.md` and
`coord/changes/h4-affine-comparison-shared-geometric-helpers.md`.
The obsolete pointwise-helper visibility record is removed with that new helper.

## Second reading by H4

1. **Signatures and visibility.** Compared every delivered module with the shared
   repository using `diff`. Six are new. The item's original signature and public
   imports are identical. In the existing geometric-helper module, only the two
   declared private-to-public visibility changes and their two necessary signature
   imports differ; all existing binders, conclusions and proof bodies are identical.
   The changes are recorded. No target or existing definition is altered. Verdict: pass.

2. **Kernel checking and constructions.** Read all eight modules and compiled the
   full overlay through `lcompile.py`. Scanned for forbidden declarations and proof
   escapes. The only literal hole is the reported public locality theorem; no
   definition has a hole. Cofree objects, Cech maps, cocones and product diagrams are
   explicit constructions. Choices of limit/colimit witnesses determine their objects
   up to the canonical equality/isomorphism used downstream. Scratch `#print axioms`
   probes give only the permitted axioms and the reported open dependency. The original
   LowerStarAcyclic consumer compiles unchanged. Verdict: pass, with one declared hole.

3. **Split theorem and search.** Matched every locality hypothesis and conclusion
   against its node: arbitrary Grothendieck abelian coefficients; finite products in
   slices; finite refinements with all nonempty repeated nerve terms in B; zero
   sheafification; and annihilation of every generalized section killed by such a
   cover. Empty covers force the whole section object into a restriction kernel;
   the zero presheaf and singleton/identity cases are consistent. No uniform cover,
   projective generator, or isomorphism-invariance of B is assumed. The proof uses
   one-fold nerve covers before recursive use of hcov, AB5 to commute the finite
   pullbacks with unions, and finite composition/refinement. This is a locality input,
   not a renaming of the original target. Independent LeanFinder, Loogle and rg
   searches found concrete-coefficient locality results but no applicable categorical
   local-kernel theorem. The search did reveal the upstream exactness theorem, which
   is now reused. The missing categorical locality API is substantial and cannot be
   closed by a short existing-lemma application. Verdict: true, needed, strictly smaller.

4. **Route and pruning.** Traced the main proof through affine finite refinement,
   simultaneous etale presentation, injective cofree contraction, filtered-colimit
   exactness and the finite-cover criterion. The ordinary abelian Cech criterion and
   the other existing site/etale criteria have narrower coefficient types. Reviewed
   `dag/units/sk-thm-properbasechange.json` and its realized statement/steps: none is
   bypassed or edited. The geometric presentation and generic dimension-shifting
   lemma are used as tools in the recorded route. The import and old proof-dependency
   removals are all listed above; no whole-library pruning is claimed. Verdict: pass.

5. **DAG agreement.** Checked all seven node files, their principal Lean statements,
   source/creation/blueprint/search records and the proof-step dependency unions.
   Existing-node changes are only proof, proof_deps and proof_origin. The six new
   nodes have the required fields and the locality theorem's verbatim signature.
   Updated the categorical-system, local-epimorphism and criterion proof descriptions
   to cite the actual upstream pointwise test; removed the criterion's obsolete direct
   dependency. The unit/chapter assignments and realized route are retained. Verdict: pass.

Changes made by this reader: replaced three pointwise-exactness proof fragments with
`ShortComplex.exact_iff_evaluation`; removed the duplicate new public helper, its change
record, and the criterion's redundant direct local-epimorphism import/dependency;
updated the affected nodes, added the independent search record, and rewrote this report
for the final delivery. No signature of any existing declaration was changed by this reader.
