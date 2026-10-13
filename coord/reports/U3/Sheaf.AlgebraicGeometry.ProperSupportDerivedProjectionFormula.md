## What changed

Replaced the sole sorry in ProperSupportDerivedProjectionFormula by a complete Lean reduction.
The public theorem's signature and docstring are unchanged. Its proof constructs the finite
union of proper cohomological supports over the bounded integer interval, proves that its
reduced closed subscheme is compact, and shrinks its closed immersion to a compact open U.
It proves local Noetherianity, quasi-compactness and quasi-separatedness of U -> S,
quasi-coherence of the restricted E, and quasi-coherence of F[0]. Finally it tensors the
supported E comparison with the identity of F[0] and composes the qcqs projection isomorphism
with the inverse supported tensor-input comparison.

Added OpenDerivedCategorySmall with a fully proved construction of a derived localization
on an arbitrary open in the ambient Hom universe. This uses fully faithful derived direct
image and Mathlib's locally-small localization construction; it assumes no global family of
localizations. Added SupportedOpenTensorDirectImageComparisons and
QCqsDerivedProjectionIsoUniverses to isolate the two remaining mathematical arguments.
Every new module uses ordinary proof imports and public imports only for its statement.
No existing statement, definition, visibility, or target binder changes.

The finite interval can be empty (including a > b). Its support union is then bottom and
all stalks vanish. The support-comparison statement allows zero E or K, empty U or T, and
T = X with U = X. Its tensor input need not be bounded or coherent: restriction of its
first factor vanishes outside T. The qcqs projection statement allows unbounded E and K,
and places no Noetherian or proper-support condition on either factor.

## Proved and sorry left

Closed AlgebraicGeometry.Scheme.nonempty_properSupport_derivedProjection_iso
(lem-pc-proper-support-derived-projection-formula). No sorry remains in the item's module.
Its private zero-stalk, compact-open-support and degree-zero quasi-coherence lemmas are proved.
Also proved AlgebraicGeometry.Scheme.nonempty_openHasDerivedCategory
(lem-pc-open-derived-category-small).

Two new holes remain, each in a separate module with its source and proof in words:

- AlgebraicGeometry.supportedOpen_tensor_directImage_comparisons
  (lem-pc-supported-open-tensor-direct-image-comparisons).
- AlgebraicGeometry.nonempty_qcqs_derivedProjection_iso_universes
  (lem-pc-qcqs-derived-projection-iso-universes).

This is a decomposition: one upper hole closed and two lower holes added. It is not a
sorry-free proof of the import closure and is not claimed as positive net hole reduction.
The lower statements are distinct parts of the source argument: supported restriction and
projection on a qcqs morphism. Neither repeats the proper-support theorem's hypotheses and
conclusion. All files compile together through lcompile.py.

## No longer needed

No original public import was removed; they supply the unchanged statement's notions.
The proof does not import DirectImageQCSupportReduction
(lem-pc-direct-image-qc-support-reduction): its finite-support geometry is implemented
explicitly and the needed supported comparisons are separated from geometry.
It does not import the recorded module WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
for lem-pc-projection-formula: that Lean declaration concerns invertible coefficients and
higher direct images, not the unbounded derived qcqs formula used here.
The complete old-minus-new direct proof-dependency list is:

- lem-pc-direct-image-qc-support-reduction (DirectImageQCSupportReduction);
- lem-pc-projection-formula (WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections);
- lem-pc-derived-pullback-tensor-qcoh (DerivedPullbackTensorQCoh);
- lem-pc-supported-open-pushforward (SupportedOpenPushforward);
- lem-pc-ringed-spaces-derived-direct-image-composition
  (Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition).

The last three move below the new comparison statements' proof plans; they are removed
only as direct dependencies of this item, not claimed absent from the eventual import
closure.

The coherent/finite-type equivalence is retained. SupportedOpenPushforward, derived tensor
and pullback restriction, and derived direct-image composition remain dependencies of the
supported-comparison node. DerivedPullbackTensorQCoh remains in the qcqs formula's proof
plan. They are not claimed pruned transitively. No unit statement or realized unit step is
bypassed, and no whole-library pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The recorded Lean declaration of lem-pc-projection-formula proves only the higher-direct-image
formula with an invertible module. It cannot provide the stated general D_QCoh formula for
a quasi-coherent coefficient. DirectImageQCSupportReduction requires a localization family
for all schemes, whereas the item assumes only the two ambient localizations. The proved
open-localization construction resolves that mismatch without strengthening the item.

A newer candidate QCqsDerivedProjectionMate is present in the source but absent from the
shared compiled library (lcompile reports its missing object file). Its signature also
requires globally compact quasi-separated source and target plus an adjunction and tensor
comparison. The delivered general qcqs statement follows Tag 08EU; its proof plan specifies
the affine-local generation argument. The candidate can shorten the affine step once it is
available in the shared green build. No unavailable source module was copied or compiled.

Mathlib searches were run with msearch.py: LeanSearch is unavailable, Loogle found generic
zero preservation and locally-small faithful functors, and grep/LeanFinder found no matching
scheme-derived projection/support theorem. Source Tags 08EU, 08EV, 08DF, 08DX, 08DW and 08FE
were read on the Stacks site because literature files are not materialized in this clone.

## New nodes

lem-pc-open-derived-category-small: OpenDerivedCategorySmall, proved. Constructs the
auxiliary open localization by a faithful derived embedding and shrinking Hom sets.

lem-pc-supported-open-tensor-direct-image-comparisons:
SupportedOpenTensorDirectImageComparisons, sorry. Gives the two direct-image comparisons
for a fixed closed support and an arbitrary derived coefficient. It makes no projection
claim and assumes none of the parent's Noetherianity, coherence, boundedness or properness.

lem-pc-qcqs-derived-projection-iso-universes: QCqsDerivedProjectionIsoUniverses, sorry.
States only the objectwise isomorphism needed from Tag 08EU for a qcqs morphism and arbitrary
quasi-coherent derived factors. It requires no proper-support or finiteness assumptions.

The parent node's proof, proof_deps and proof_origin track the implemented reduction.
No change record is required: no existing interface is changed.


## Second reading by U3

1. PASS: diffed every delivered module against the repository. Only the item already
   exists. Its public theorem signature and docstring are byte-for-byte unchanged;
   new imports are plain proof imports. No existing definition, visibility, or target
   statement changes, and no change record is needed.
2. PASS: compiled all four modules in import order with lcompile.py. Exactly the two
   reported named public theorems have sorry. No definition contains sorry and no
   forbidden declaration occurs. A scratch-copy #print axioms check of all four public
   theorems shows only propext, Classical.choice, Quot.sound, and sorryAx on the three
   theorems with open dependencies. nonempty_openHasDerivedCategory has no sorryAx:
   its localization is constructed using a faithful derived embedding and Mathlib's
   Hom shrinking, not selected from an unproved existence assertion.
3. PASS: read both new holes against Stacks Tags 08EU and 08DF and the restriction
   compatibilities. Checked zero factors, empty schemes/opens, T empty, U=X, and an
   empty bounded interval. Closed support makes the supported-open comparison true
   even for arbitrary unbounded tensor inputs; the qcqs theorem has exactly the
   quasi-coherence needed for the coproduct argument. Neither is a restatement of the
   item. Their docstrings give complete mathematical arguments and their nodes match
   their Lean signatures. Independent LeanFinder, Loogle and grep searches, and rg
   searches of the scheme-derived library, found no exact existing theorem. Also
   inspected RightAdjointTensorComparisonProjection: it requires a proper morphism,
   Noetherian schemes, a monoidal pullback and adjunction, so cannot close the general
   qcqs hole. The existing QCqsDerivedProjectionMate additionally requires compact
   quasi-separated schemes and supplied adjunction/tensor comparison.
4. PASS: traced the finite-support construction, exact restriction of quasi-coherent
   homology, degree-zero homology calculation, and final three-isomorphism composition.
   Each added import supplies a named proof ingredient or an instance used by it.
   The original public imports supply the unchanged signature. No shorter available
   route closes either new hole in a few minutes. The unit sk-thm-picard-duality has
   empty realized statement/step arrays: no designated unit node is bypassed. The
   decomposition keeps the source's support reduction followed by qcqs projection.
   Checked all six old proof_deps: the coherent equivalence remains direct; the other
   five are now explicitly listed under No longer needed. This is one upper hole
   closed, two lower holes added, not positive net hole progress or global pruning.
5. PASS: compared the parent proof/proof_deps/proof_origin with the actual proof and
   inspected all three new nodes' source, search, creation, blueprint, unit, chapter,
   Lean signature and dependency records. Each proof_deps list is the union of its
   proof steps' uses. Only the permitted parent fields changed.

Second reading changed only this report: completed the old direct-dependency list and
recorded the independent checks. No Lean or node repair was required.
