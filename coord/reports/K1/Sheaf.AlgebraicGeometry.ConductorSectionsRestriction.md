## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.conductor_sections_restriction`
with a complete Lean assembly proof, preserving its signature and visibility.
The tensor-power comparison is constructed from the source library's proved
`nonempty_pullback_tensorPow_iso`, uniqueness of left adjoints, and a proved private
recursive `tensorPowCongr`. Pullback invertibility uses the proved source-library instance.
The original ideal multiplication map is monic by the Dual module's instance.
Its categorical image is identified with its source by `imageMonoIsoSource`.

Applied `conductorIdealZeroIntersection` to get the morphism between image sheaves,
its section bijectivity and its commutative square. Composed the source image
isomorphism, that section map, and a component image comparison. Proved additive
bijectivity by composition. The compatibility proof evaluates the square and
`imageMonoIsoSource_inv_ι`, cancels the tensor-power comparison, and uses
`unit_leftAdjointUniq_hom_app` to recover precisely the canonical unit in the statement.

Added one generic comparison module, `Sheaf.AlgebraicGeometry.IdealTensorImageComparison`,
for the missing identification of the adjoint ideal image with `IdealSheafData.comap`,
tensored with an invertible module. It does not assert restriction bijectivity or use
component-cover hypotheses. Its statement includes the exact inclusion equality needed
by the main proof, for arbitrary ambient linear isomorphisms and adjunctions.
Updated the conductor and image-comparison node proofs and dependencies. No existing statement or definition changed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.conductor_sections_restriction`
(node `lem-sc-conductor-sections-restriction`).

Added one hole:
`AlgebraicGeometry.Scheme.Modules.ideal_tensor_image_comparison`
(node `lem-sc-ideal-tensor-image-comparison`).
Its proof is exactly `by sorry`; its docstring and node give the complete affine
image calculation and monic-image/tensor transport argument. No holes remain in the item's module or in its private
helper. This is a decomposition, not a claim of a fully axiom-free conductor theorem:
one original hole closed, one strictly partial image-comparison hole added. The existing
zero-intersection theorem still supplies the geometrical restriction bijection.
Both delivered files compile without warnings using `lcompile.py --all`.

No arbitrary data is constructed from a mere unproved existence assertion.
The comparison q is determined by its displayed equality: the target ideal multiplication
is monic because its ambient module is isomorphic to the invertible P. Thus any two
choices agree pointwise, and the additive equivalence agrees by extensionality.
The source tensor-power and adjunction comparisons used as data are already proved.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ConductorIdealRestriction`
  (`lem-sc-conductor-ideal-restriction`): the target needs an image identification,
  without requiring the pulled-back ideal itself to be isomorphic to that image.
- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
  (`lem-weil-pbc-invertible-pullback-tensor`): its large bundled theorem is replaced
  by the source library's proved pullback-invertibility instance and tensor-power comparison.

Retained `WeilConjectures.AlgebraicGeometry.Modules.Dual` because its mono tensoring
instance is necessary. Added the proof import of ProjectionFormula for the already proved
tensor-power comparison and the new comparison module. Existing public imports are retained
for the original statement and its definitions. No unit statement or realized step is
bypassed: this item is below the unit level, and is not listed in the unit's realized fields.
The old DAG dependency `lem-weil-pbc-module-pullback-tensor` is also unnecessary:
the Lean proof calls the proved source `nonempty_pullback_tensorPow_iso`, not the
canonical section-compatible `Sheaf.AlgebraicGeometry.ModulePullbackTensor` theorem.
That source theorem is now recorded by `lem-sc-pullback-tensor-power-iso`.
The new comparison plan no longer needs
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`: once its ideal-image
identification is established, tensor functoriality and the monic-image isomorphism
supply the remaining comparison directly.
The removed modules may still be reached through other routes; no global unreachability
is claimed here.

## Where the brief, the DAG or earlier work was wrong

The plan correctly identifies the image-comparison gap, but the existing conductor ideal
restriction theorem does not itself identify its image with `I.comap f`. Its conclusion
is about the corestriction being an isomorphism; the gap is the identification of two
representations of the extended ideal. The new lemma isolates exactly this gap. The
adjunction choices are not assumed equal: the main proof explicitly uses their comparison
and its unit equation.

Checked the source on the Stacks pages for Tags 09NW and 09NX. The displayed equality in
09NX uses the ideal-product representation supplied by 09NW; the new lemma is the generic
representation comparison, while zero intersection remains in the original dependency.
The new lemma also allows nonflat morphisms: it concerns the image of the pulled-back
ideal, not injectivity of its pullback. Edge cases checked mathematically: zero ideal,
unit ideal, empty source scheme, identity morphism, arbitrary linear automorphism e,
and a quotient ring map. For a quotient A to A/J the image is (I+J)/J, regardless of
whether I meets J nontrivially; no zero-intersection assertion is used in this lemma.
The main proof works for m=0 and empty components through the same categorical formulas.

## New nodes

`lem-sc-ideal-tensor-image-comparison` is the generic image-to-extended-ideal tensor
comparison. It inherits the item's chapter and unit and cites the same blueprint sentence.
The statement has no conductor cover and supplies no section restriction map from Y.
Thus it is strictly the identification step of the original proof, and does not restate
the theorem under a new name. Mathlib was searched by grep, LeanFinder and LeanSearch;
LeanSearch returned Internal Server Error, recorded as unavailable. Searches of existing
ideal-module, ideal-pullback, ideal-product, and image modules found no exact comparison.
No change record or forced adaptation is needed.


`lem-sc-pullback-tensor-power-iso` records the existing proved
`AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorPow_iso` in
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`. It adds no Lean module,
no theorem and no hole. The source proof uses the monoidal unit comparison at zero
and the monoidal binary comparison inductively. This record replaces the unused
canonical tensor-pullback theorem in the conductor node's dependencies.

## Second reading by K1

1. **Unchanged interface — pass.** Read the complete repository/sandbox diff of
   `ConductorSectionsRestriction.lean`. The sole original declaration's signature,
   from `theorem` to `:= by`, is byte-for-byte identical after removing an extra
   space introduced by the first worker. All original public imports remain;
   additions are proof-only imports and a private recursive isomorphism.
   No definition or target statement changed, and no change record is needed.

2. **Proof and axioms — pass as a decomposition.** Both delivered modules compile
   locally in import order without warnings. The main module contains no `sorry`;
   the sole new hole is exactly the named theorem
   `ideal_tensor_image_comparison`. No prohibited declarations or hollow definitions
   occur. The private `tensorPowCongr` is a real recursive construction: unit at zero,
   tensor of the given isomorphism with the induction comparison at successor.
   Scratch `#print axioms` checks are recorded below. The main theorem still relies
   on the existing zero-intersection hole and the new comparison hole; this is not
   an axiom-free conductor proof. Adjunction and source tensor comparisons used as
   data are proved. The image comparison's inclusion equation uniquely determines
   q, since N₁ is invertible via e and its ideal multiplication is monic.

3. **Split statement — true and strictly partial.** Read the new statement,
   its node, ideal-module inclusion/range declarations, and `ideal_comap_appLE`.
   Read [Stacks 09NW](https://stacks.math.columbia.edu/tag/09NW),
   [09NX](https://stacks.math.columbia.edu/tag/09NX) and
   [01CD](https://stacks.math.columbia.edu/tag/01CD). The conductor hypotheses match
   09NW's reduced-union argument; no Noetherian, separated, or dimension assumption
   of the larger ampleness lemma is needed for its conductor equality. The new
   lemma isolates the generic representation identification and asserts no
   restriction bijection from Y. On affine U=Spec B over V=Spec A, the canonical
   adjoint sends b⊗a to b f♯(a), with image I(V)B. For a changed adjunction,
   φ=c_I.hom≫φ₀, so the image is unchanged. This is a statement about the image,
   valid without flatness. Once identified with K=I.comap f, tensor with the
   ambient linear isomorphism e.inv≫c_N.hom and use naturality of the left unitor;
   monicity gives both image-source isomorphisms and uniqueness. I rewrote the
   docstring and node's second step to give this direct argument.
   Tested zero/unit ideals, empty scheme, identity, and a nonflat quotient:
   A=Z/4, B=Z/2, I=(2) has nonzero B⊗_A I but zero image and zero extended ideal;
   both sides of the comparison are zero. Thus no injectivity of ideal pullback
   was silently used. Arbitrary linear e and adjunction comparisons preserve
   ideal scalar multiples and their inverses supply the reverse inclusion.
   Independent LeanFinder search for extension-of-scalars ranges found
   `Submodule.map_range_rTensor_subtype_lid` and `Ideal.smul_top_eq_map`;
   Loogle found comap's Galois-connection and subscheme-base-change interfaces.
   Grep of Mathlib, repository Sheaf and source WeilConjectures found no theorem
   already supplying this sheaf comparison. Read `modulePullbackIdealQuotient`:
   its conclusion is a quotient/kernel identification for quasi-coherent modules,
   not the required adjoint ideal image inclusion square. Closing the new hole
   needs that sheaf image identification, not a short existing-lemma application.

4. **Route and pruning — pass after metadata repair.** Followed p, ρ and q in
   the compiled proof. p is evaluation of `(imageMonoIsoSource μ).symm`; ρ and its
   bijection/square are precisely the existing `conductorIdealZeroIntersection`
   clauses for the constructed e; q is the new representation comparison.
   The final calculation uses the evaluated square, `imageMonoIsoSource_inv_ι`,
   `e.hom_inv_id`, and `unit_leftAdjointUniq_hom_app` in the correct direction,
   yielding exactly the statement's canonical res₁. Invertibility comes from
   the source pullback instance transported by d; tensor-power invertibility
   supplies the mono instance from Dual. In particular m=0 uses the unit
   comparison, and empty index types cause no illicit chosen component (a is
   already an explicit hypothesis). Imports used only in proofs are plain.
   All five public imports of the new module supply signature constructions.
   Compared old proof_deps: both old unused nodes are listed under No longer
   needed. Also removed the worker-added but unused canonical tensor comparison
   dependency. Read `dag/units/sk-thm-curveestimate.json`: its realized statement
   is `thm-sc-proper-cohomology`, with no realized steps; neither this item nor
   any pruned dependency realizes a fixed unit step. The unit route is kept.

5. **DAG agreement — pass after repair.** The conductor proof now records the
   exact proved source tensor-power comparison, rather than the unused
   section-compatible `module_pullback_tensor`. Added the existing-declaration
   node `lem-sc-pullback-tensor-power-iso`, with source, complete induction proof,
   three searches (LeanSearch unavailable), origin, blueprint, creation and Lean
   records. The new image-comparison node now cites the already proved
   `lem-pc-ideal-sheaf-comap-affine-extension`, whose `ideal_comap_appLE` actually
   supplies the affine ideal equality. Removed its unnecessary bundled
   ideal-product affine-sections dependency. All three proof_deps sets are
   exactly the unions of their steps' uses, and the new holed theorem's node
   signature matches Lean. The original statement and stmt_deps are unchanged.

Changes by the second reader: corrected the stale conductor proof docstring;
expanded the new lemma's adjunction, nonflat-image and tensor-naturality argument;
added source/blueprint module documentation; restored exact signature whitespace;
repaired DAG dependency records and recorded the existing source tensor-power
comparison. No mathematical statement or executable proof was rewritten.


Verification results: scratch `#print axioms conductor_sections_restriction` and
`#print axioms ideal_tensor_image_comparison` each show exactly
`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
`#print axioms nonempty_pullback_tensorPow_iso` shows exactly the three standard
axioms, without `sorryAx`. The launcher dry run compiled both files, ran the
all-declaration axiom probe, and passed preflight with review class CODEX
(new holed theorem and nodes). Original holes closed: 1 of 1; new holes added: 1;
net holes closed in this local reduction: 0. No global pruning or ledger net is
claimed; dependency imports and the named unused proof-dependency nodes are pruned.
