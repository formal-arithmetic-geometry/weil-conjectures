## What changed

The statement of `AlgebraicGeometry.Scheme.exists_boundedFree_stalk_complex_local_lift`
is unchanged. Its proof conjugates the differentials to coordinate modules, spreads their
coefficients and square-zero relations, constructs the section-ring complex with
`CochainComplex.of`, and applies the existing `affinePerfectSheafification` functor.
The finite free term isomorphisms are proved using `tildeFinsupp`, restriction,
`overEquiv`, and `mapFreeIso`. The original bounds follow from rank-zero coordinate
modules being subsingleton. The final stalk complex isomorphism uses
`HomologicalComplex.Hom.isoOfComponents` and naturality on coefficient germs.

Added `Sheaf.AlgebraicGeometry.SquareZeroStalkCoefficientsSpread` and
`Sheaf.AlgebraicGeometry.AffineFreeSheafStalkRealization` as proof imports, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` for its existing free-sheaf
restriction and unit comparisons. Updated the item's DAG proof to the implemented route.
No existing signature, definition, public import, or instance changed. The second reader
removed an unused public Free import from the new comparison module.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_boundedFree_stalk_complex_local_lift`
(node `lem-sc-bounded-free-stalk-complex-local-lift`). There is no sorry in the item's module.

Proved the new theorem
`AlgebraicGeometry.Scheme.exists_squareZero_stalk_coefficients_spread`
(node `lem-sc-square-zero-stalk-coefficients-spread`) entirely from Mathlib, including its
coordinate-matrix correspondence, finite germ lifting, and finite zero-germ shrinking.
Its module has no sorry and needs only the three permitted axioms.

Added one remaining hole:
`AlgebraicGeometry.Scheme.exists_affine_freeSheaf_stalk_realization`
(node `lem-sc-affine-free-sheaf-stalk-realization`). This compares individual finite
coordinate modules and arbitrary maps under the already constructed affine sheafification
functor and ambient ordinary-direct-image stalk. It has no complex, differential,
boundedness, square-zero, support, or neighbourhood-existence assertion. The docstring
specifies the finite basis germ construction and proves naturality in words.

Accounting: one original hole closed, one new hole added. The upper theorem is a
proved reduction with one remaining comparison lemma, hence a decomposition, not a
claim of an axiom-free proof of the upper theorem. All private helpers are proved.
Empty degree intervals and zero ranks are handled by empty finite index types and
`Fin.elim0`; no nonempty-rank or germ-injectivity assumption was added.

## No longer needed

Removed proof imports `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`
and `Sheaf.Algebra.FinitePresentationColimit`. The corresponding nodes
`lem-weil-pbc-localization-colimit-principal-localizations` and
`lem-pc-fp-module-map-descent-affine` are not dependencies of this proof.
The direct stalk representative/equality criteria eliminate both colimit-descent steps.
No further old proof imports were present. Existing public imports remain required by
the statement and direct-image instance, with unchanged visibility.
This is pruning of this branch; it makes no assertion that other target branches cease
using those two modules.

## Where the brief, the DAG or earlier work was wrong

The planned principal-localization diagram is indexed by a preorder, whereas the stated
finite-presentation descent theorem requires a partial order. Neither of those declarations
alone provides the free-module stalk identification after ordinary open direct image.
This delivery uses germs directly for coefficient spreading, avoiding the index-interface
mismatch, and isolates that geometric comparison. Existing free-matrix lifting and equality
shrinking results compare pullback to Spec of a stalk and cannot be applied directly to the
ambient module-stalk functor in this statement. The existing affine sheafification functor
is reused rather than introducing an arbitrary sheafification witness.

The unit `sk-prop-av-cube` has no realized statement/step at this node; its route is unchanged.
The local Stacks source files are absent on this machine. Relevant tags were checked on the
official Stacks site; new proof origins are marked as agent-written expansions.

## New nodes

`lem-sc-square-zero-stalk-coefficients-spread`:
`lean/Sheaf/AlgebraicGeometry/SquareZeroStalkCoefficientsSpread.lean` contains the proved
algebraic spreading part (no sheaf complex or stalk isomorphism). Its node records the
coefficient and product-entry finite intersections and the Mathlib search results.

`lem-sc-affine-free-sheaf-stalk-realization`:
`lean/Sheaf/AlgebraicGeometry/AffineFreeSheafStalkRealization.lean` states the remaining
natural finite-coordinate comparison for the existing affine sheafification functor.
Its source is Stacks Tags 01HV, 01IB, 01C6 and the elementary cofinal neighbourhood
calculation for ordinary open direct image. It is strictly one part of the upper proof.
No change record is required because no existing interface changed.

## Second reading by K3

1. Compared the delivered item with the repository by diff. PASS: both existing
   declarations retain their signatures byte for byte; the zero-map instance body
   is unchanged. No existing definition or public import changed. Also restored the
   existing node's recorded signature formatting to the repository's exact text.
2. Compiled all three delivered modules in dependency order through lcompile.py:
   PASS, without errors or warnings. The only textual sorry is the full proof of
   exists_affine_freeSheaf_stalk_realization. No axiom, unsafe, opaque, extern,
   implemented_by, or hollow definition occurs. Explicit #print axioms checks in
   a scratch copy show only the permitted axioms for the coefficient theorem and
   only those axioms plus sorryAx for the upper theorem and the remaining lemma.
   The complex L is constructed by CochainComplex.of and the existing concrete
   affinePerfectSheafification functor; no definition chooses arbitrary data from
   the unproved comparison theorem. Its existential is used solely in a proof.
3. Read both new statements and their nodes. PASS: coefficient spreading contains
   no sheaf-complex comparison; stalk realization contains no complex, support,
   shrinking, or square-zero assertion. The remaining hole is strictly one part
   of the original argument. Checked rank zero, empty degree intervals, arbitrary
   maps with zero source/target, and the vacuous empty-scheme case. The construction
   intersects only finitely many opens, and imposes no germ-injectivity assumption.
   Expanded the remaining docstring with the explicit finite basis-germ map,
   coordinate-germ inverse, and injectivity/surjectivity argument. Corrected Tag
   01HV's lemma number to 26.5.4 (7), checked on the official Stacks site:
   https://stacks.math.columbia.edu/tag/01HV . Second searches used loogle
   "stalk", "free", leanfinder's finite-tuple germ query, and grep's coordinate/
   square-zero queries. Read FiniteFreeModuleStalkEquiv, OpenModuleStalkFreeProjective,
   FiniteFreeStalkFiniteMatrixLift, and Mathlib tilde.toStalk. These supply ingredients,
   but do not state the needed natural comparison for ordinary direct image of this
   particular affine sheafification functor. No quick closure was found.
4. PASS: read the conjugation, matrix product, zero-germ shrinking, free-term
   comparison, bounds, and componentwise complex isomorphism proofs. The two old
   dependencies removed from proof_deps are both listed under No longer needed.
   The unit sk-prop-av-cube has empty realized statement and step lists; this node
   is below its route, and no unit realization is bypassed. Removed the unused
   public Mathlib.Algebra.Category.ModuleCat.Sheaf.Free import in the new comparison
   module; recompilation succeeds through its remaining statement imports.
5. PASS: existing node changes only lean/proof/proof_deps/proof_origin; the proof
   steps and dependency unions match the Lean reduction. Both new nodes have source,
   complete proof plans, search records, creation/blueprint metadata, chapter/unit,
   and matching Lean signatures. Corrected the same citation in the new comparison
   node's source and proof_origin. No statement-change record is needed.

Second reading changed only the unused import, the remaining lemma's proof docstring,
the incorrect source lemma number, the existing node signature's formatting, and this
report. Accounting remains one original hole closed and one new hole added: a
decomposition, with zero net holes closed. The coefficient-spreading theorem is proved
without sorryAx; the upper theorem still depends on the named comparison hole.
