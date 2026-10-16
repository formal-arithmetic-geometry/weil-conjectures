## What changed

Replaced the sole sorry in `ContinuousFiniteEtaleLatticeDescent.lean` by a complete Lean proof
from strictly intermediate finite-sheet coordinates of the two canonical maps. The existing theorem's signature, universe,
visibility, hypotheses and conclusion are unchanged. No existing definition is changed and no
consumer adaptation is needed.

Constructed the candidate lattice explicitly in `ContinuousLatticeIntersection.lean`: it is the
pullback, along the restricted rational adjunction unit, of the image of the pushed lattice
embedding. The construction takes the given rationalization isomorphism as input; it chooses no
object from an unproved existence theorem. Its inclusion and rationalization morphism are actual
categorical maps. Proved its rationalization is invertible using ordinary qcqs filtered-colimit
continuity, module localization telescopes, the localization counit and the specified pushforward
mate. These are implemented in `CondensedUnderivedPushforwardContinuity.lean`,
`ContinuousIntegralLocalizationCounit.lean`,
`ContinuousIntegralUnderivedPushComparison.lean` and
`ContinuousLatticeIntersectionRationalization.lean`.

Proved continuous finite-matrix denominator clearing on compact schemes in
`ContinuousFiniteFreeDenominators.lean`, including the regular-module comparison and the finite
maximum of the entrywise exponents. Proved monicity of the finite-free localization unit and
conversion of an epi rational matrix kernel to an integral matrix kernel in
`ContinuousFiniteFreeKernelModel.lean`. Proved local finite freeness of integral matrix kernels
with locally free rational cokernel by strengthening the existing pivot induction in
`IntegralMatrixKernelLocallyFree.lean`; its rational-epi corollary is what the item uses.
`ContinuousLatticeIntersectionLocalModel.lean` proves the integral matrix model from the
rational model and these denominator/kernel results. `ContinuousLatticeIntersectionRationalModel.lean`
proves that rational kernel model from the split finite-sheet image-pullback comparison, using the
proved abelian-category `imagePullbackIsoKernel` and preservation of cokernels by restriction.

The new proof-only `import all` of `ContinuousIntegralPushComparison` reuses its two proved
private generic telescope/mate helpers. The proof-only imports of `IntegralConstructibleKernels`
and `CondensedConstructibleSerre` reuse their proved pivot-cokernel and local-freeness transport
helpers. No existing declaration is redefined or exposed differently. No target statement or
unit realization is changed; this remains the finite-etale descent step below the same unit.

Validation: all thirteen delivered modules compile cleanly in import order through
`lcompile.py --all`; each single-file compile takes at most fourteen seconds in the first second-reader pass. The overlay import
graph has no cycle and reaches every delivered module. The original theorem signature is
byte-for-byte unchanged.

## Proved and sorry left

Original holes: 1. The hole in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_finiteEtale_lattice` is closed in its
module. Its proof constructs the lattice, proves rationalization, derives local freeness from
integral matrix kernels, transports coefficient normalization and binds the covering families.

Added holes: 1, exactly the named public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.continuousLatticeIntersection_splitData` in
`ContinuousLatticeIntersectionSplitData.lean`, node
`lem-weil-pbc-continuous-lattice-intersection-split-data`. It still needs the internal-module
weakly-etale base-change and finite-disjoint-union pushforward identifications, simultaneous
trivialization of P and the sheet lattices on a compact refinement, and transport of the
two canonical map equations under those comparisons. Exact image-pullback preservation and
isomorphism transport are proved in `imagePullbackMapIso` and `imagePullbackCongr`; the
split model now follows from them with a complete Lean proof. Its docstring and node spell out the diagonal,
its chosen-sheet splitting, the free cokernel basis, and the empty/singleton-sheet cases. It
asserts neither a kernel model, local freeness of the intersection, nor its rationalization.
Those are separately proved. In particular no equality between the sheet ranks is needed.
This is a decomposition: one original hole closed and one strictly lower hole added, net zero
direct holes. It is not an axiom-free proof of lattice descent yet.

All other delivered declarations are proved, including:

- `CategoryTheory.Limits.imagePullbackι_map_isIso`,
  `CategoryTheory.Limits.imagePullbackMapIso`, `CategoryTheory.Limits.imagePullbackCongr`,
  `CategoryTheory.Limits.imagePullbackIsoKernel`, and
  `CategoryTheory.Adjunction.pushHomOfComapIso_homEquiv`;
- `latticePushedEmbedding_rationalization`, `latticePushedEmbedding_map_isIso`, and
  `latticeIntersectionRationalization_isIso_of_map_isIso`;
- `CategoryTheory.Functor.singleComplexRightDerivedZeroIso` and
  `lowerStar_preservesFilteredColimit`;
- `integralLocalization_zero_isIso`, `integralScalarCounit_isIso`, and
  `integralScalarUnderivedPushHom_isIso`;
- `continuousLatticeIntersectionRationalization_isIso`;
- `integralRegular_clear_denominators`, `integralFiniteFree_clear_denominators`,
  `integralFiniteFree_unit_mono`, and `integralFiniteFree_kernel_model`;
- `integralMatrixKernel_locallyFree`,
  `integralMatrixKernel_locallyFree_of_rational_epi`, and
  `continuousLatticeIntersection_localModel`, `continuousLatticeIntersection_rationalModel`,
  and `continuousLatticeIntersection_splitModel`.

These proofs use the existing project theorems as intended by stage 3, including their remaining
upstream holes. No sorry occurs in any delivered definition or private helper.

## No longer needed

Removed all ten former proof-only imports from the item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`;
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`;
- `Sheaf.CategoryTheory.RingedSiteModules`;
- `Sheaf.CategoryTheory.SiteCoveringAxioms`;
- `Sheaf.CategoryTheory.SiteModuleSheafGluing`;
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`;
- `Sheaf.Paper.FiniteEtaleEtaleLocalSplit`;
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`;
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`;
- `Sheaf.Paper.ContinuousCoefficientRealizations`.

The new route needs no conversion to section-ring sheaf modules, no sheaf sum of the sheet
lattices inside P, no DVR basis for that sum, no enumeration/permutation cocycle and no sheaf gluing.
In particular its proof no longer uses the old intermediate nodes
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`lem-weil-pbc-site-module-sheaf-gluing`, `lem-sc-dvr-fg-torsionfree-free`,
`lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-l-adic-extension-absolute-value`,
`lem-weil-pbc-proetale-restriction-injectives`, or the site-comparison/open-immersion conversion
steps of the old route. The parent node's old proof edges are replaced by the four actual new
proof inputs. Removed its two obsolete direct `tool_uses` approvals; no approvals were added.

Finite-etale local splitting and continuous coefficient realizations remain needed lower down:
the former in the remaining finite-sheet coordinate proof plan (now retained by a proof-only
import in SplitData), the latter in the proved continuous matrix argument. Their removal as direct imports is not a claim that the project can prune
them globally. Coefficient definitions, module-category definitions, inverse image, tensor and
covering APIs likewise remain in use through the actual internal-module library. Global pruning
of modules also reached by other targets is for the maintainer's closure calculation.

For completeness, the other old direct proof edges have these dispositions:
`def-pur-sheaf-tensor-product` is replaced by internal scalar-extension APIs;
`def-weil-pbc-condensed-e-module-category`,
`def-weil-pbc-continuous-integral-coefficients`,
`def-weil-sheaf-of-modules-category` and `def-weil-proetale-inverse-image` still supply
statement or construction data;
`def-weil-pbc-sites-and-cohomology` still supplies the underlying covering operations;
`def-weil-pbc-etale-site`, `def-weil-pbc-site-comparison-morphism` and
`lem-weil-pbc-open-immersion-etale` are not used for an etale/pro-etale sheaf-module
conversion in this route. Scheme etale/open-cover geometry itself remains needed.

The existing `DirectImageSplitCoverProduct` theorem is for etale sheaves with constant
`ModuleCat` coefficients, so it cannot supply the remaining internal condensed-module
comparison directly. `ProEtale.BaseChange.WeaklyEtale` proves the abelian-sheaf base-change
map is invertible. `ProfinitePointPullback` supplies the module/abelian forgetful pullback
comparison and unit/composition coherence. Lifting and combining those maps with the
finite-sheet product comparison is precisely part of the remaining geometric obligation.

## Where the brief, the DAG or earlier work was wrong

The original DAG's sum-and-gluing argument was a valid possible route, but its internal-to-section
module comparison and all its specific compatibilities had not been formalized. They are not
needed for this internal image-pullback route. No mathematical statement is disputed.

Bhatt--Scholze Lemma 6.8.13 first paragraph actually uses continuous fundamental-group
representations and compactness to obtain a stable lattice. The intersection and matrix
presentation here are an agent variant of that finite-etale descent argument. Every new node
records this provenance rather than attributing the explicit categorical proof to the paper.
Hemo--Richarz--Scholbach Lemma 5.3(1) supplies the continuity input via the already stated project
theorem; the degree-zero and scalar-telescope consequences are proved here.

The remaining finite-sheet coordinate statement is substantially lower than the original
existence statement: the candidate integral object, its inclusion, its rationalization, the analytic denominator step,
both categorical kernel comparisons, exact image-pullback transport and the local-freeness
induction are all supplied independently. The split model itself is now proved too. The
remaining content is finite-cover geometry and the associated internal-module map comparisons.

## New nodes

`def-weil-pbc-continuous-lattice-intersection`: explicit categorical construction of the
intersection, canonical maps, mapped-pullback criterion, exact image-pullback preservation,
transport under commuting isomorphisms, and mates formulas; implemented in
`ContinuousLatticeIntersection.lean` with no holes.

`lem-weil-pbc-condensed-underived-pushforward-continuity`: degree-zero consequence of the existing
qcqs derived continuity theorem; implemented in `CondensedUnderivedPushforwardContinuity.lean`
with no holes.

`lem-weil-pbc-integral-localization-counit`: localization acts identically on rational modules;
implemented in `ContinuousIntegralLocalizationCounit.lean` with no holes.

`lem-weil-pbc-integral-underived-push-comparison`: the actual ordinary coefficient/pushforward
mate is invertible for qcqs maps and all integral modules; implemented in
`ContinuousIntegralUnderivedPushComparison.lean` with no holes.

`lem-weil-pbc-continuous-lattice-intersection-rationalization`: rationalization of the canonical
intersection for qcqs p; implemented in `ContinuousLatticeIntersectionRationalization.lean`
with no holes.

`lem-weil-pbc-integral-matrix-kernel-locally-free`: the pivot induction with locally finite free
kernel conclusion, and its rational-epi corollary; implemented in
`IntegralMatrixKernelLocallyFree.lean` with no holes.

`lem-weil-pbc-continuous-finite-free-denominators`: integral numerators for finite rational
matrices on compact schemes; implemented in `ContinuousFiniteFreeDenominators.lean` with no holes.

`lem-weil-pbc-continuous-finite-free-kernel-model`: finite-free unit monicity and the integral
kernel comparison after denominator clearing; implemented in `ContinuousFiniteFreeKernelModel.lean`
with no holes.

`lem-weil-pbc-continuous-lattice-intersection-rational-model`: the rational kernel presentation
proved from the split model using `imagePullbackIsoKernel`, the restriction/cokernel comparison
and the free cokernel basis; implemented in `ContinuousLatticeIntersectionRationalModel.lean`
with no holes.

`lem-weil-pbc-continuous-lattice-intersection-split-model`: the split model proved from the
finite-sheet coordinates, exact image-pullback preservation and isomorphism transport;
implemented in `ContinuousLatticeIntersectionSplitModel.lean` with no holes.

`lem-weil-pbc-continuous-lattice-intersection-split-data`: the one remaining finite-cover
comparison obligation for three objects and two maps, precisely identified above; implemented
as a named public sorry in `ContinuousLatticeIntersectionSplitData.lean`. It mentions no
intersection object and does not assert a kernel presentation or local-freeness conclusion.

`lem-weil-pbc-continuous-lattice-intersection-local-model`: the integral matrix model obtained
from that rational presentation by the proved denominator and kernel constructions; implemented
in `ContinuousLatticeIntersectionLocalModel.lean` with no holes.

All nodes inherit the item's chapter/unit, have searched blueprint ancestry, complete natural
language statements and proofs, three kinds of recorded Mathlib search, and exact Lean
attachments. There are no change records because no existing definition or statement changed.

## Second reading by E2

1. **Visible statements: PASS.** Independently diffed every delivered Lean file against the
   shared repository. The item is the only existing Lean module in this set. Its complete
   theorem signature, universe, visibility and public imports are byte-for-byte unchanged;
   only its proof, proof-only imports and proof description differ. The other twelve modules
   are new. No existing definition, target, or consumer changes, so no change record is needed.
   The existing node changes only proof, proof_deps, proof_origin and removal of the two
   obsolete tool_uses entries.

2. **Proof and construction: PASS as a decomposition.** Read all thirteen modules, including
   the categorical intersection and the telescope/mate arguments, then compiled the whole
   set in dependency order with lcompile.py. There are no errors or warnings. The only new
   hole is the public continuousLatticeIntersection_splitData, with body exactly `by sorry`.
   No forbidden declaration, private hole, anonymous hole or hole in a definition occurs.
   The lattice, inclusion, rationalization morphism and all comparison isomorphisms are
   categorical constructions from explicit maps or their universal properties. No arbitrary
   witness is extracted from splitData to define a public object. Checked axioms in a scratch
   module for every node-attached declaration (35 names), and the delivery probe checks all
   declarations. The printed axiom sets contain only propext, Classical.choice, Quot.sound
   and upstream/open sorryAx; this is not an axiom-free proof of descent. The explicit
   lattice construction and its rationalization theorem themselves have no sorryAx.

3. **Remaining statement: PASS.** Read splitData and its complete docstring argument separately
   from its consumers. Finite-etale local splitting, simultaneous finite refinement of the
   supplied bases, and affine refinement give its compact covering members. On a nonempty
   member at least one sheet exists; projecting to it splits the rational diagonal, and
   subtracting that coordinate gives the free rational cokernel. The two equations are the
   adjunction unit and coefficient-change mate equations in these coordinates. Rank zero,
   an empty base, singleton sheets, varying sheet ranks, and cover degree divisible by ell
   cause no exception. The statement describes three objects and two maps, without asserting
   an intersection property, rationalization of the intersection, or descent. Thus it is a
   true, strictly lower geometric part of the argument, not a renamed descent theorem.
   Independent LeanFinder, Loogle and grep queries used different terms (recorded in the
   node). Read DirectImageSplitCoverProduct, FiniteEtaleEtaleLocalSplit, ProfinitePointPullback,
   the abelian WeaklyEtale base-change source and Adic.BaseChange: none directly states the
   required internal continuous-coefficient comparison. Closing this hole requires the
   geometric comparisons and their map coherence, not a short application of an existing
   declaration.

4. **Route and pruning: PASS after import bookkeeping repair.** The top proof constructs N,
   applies its independently proved rationalization, and derives local freeness from the
   integral matrix kernel theorem through the local model. The intermediate categorical
   kernel comparison, denominator construction and pivot induction are substantive proofs.
   Checked every old proof_deps edge against `No longer needed`; that section distinguishes
   removal of direct imports from global closure pruning. No global module pruning is claimed.
   Read dag/units/sk-thm-properbasechange.json and its realized statement/steps; this item is
   below those realizations and the delivery changes or bypasses none of them. Proof-only
   import all is used for proved generic private helpers, never for public signatures or
   public definition bodies.

5. **Nodes: PASS after metadata correction.** Read all thirteen delivered node records,
   checked their Lean attachments verbatim, dependency unions, chapter/unit, blueprint
   ancestry, source/proof_origin and new-node creation/search records. The parent now names
   the actual remaining coordinate hole rather than the already proved split-model theorem.
   New nodes correspond to the explicit construction and the intermediate proofs as written.
   The open coordinate node contains the independent search results.

**Changes in this second reading.** Added four proof-only plan imports to
ContinuousLatticeIntersectionSplitData: FiniteEtaleEtaleLocalSplit,
RegularExtensionComparison, ContinuousIntegralUnderivedPushComparison and
ProfinitePointPullback. These retain the actual inputs needed by its unresolved geometric
proof rather than inadvertently pruning them from that module's import closure. Corrected
the parent's proof_origin and the report's compile-time wording, and recorded the new searches.
No theorem proof or signature needed repair; holes closed/added remain 1/1 (net zero).

A direct proof-only import of the existing abelian BaseChange.WeaklyEtale module was also
tried and removed: its cached artifact imports the former UpperLowerStar.Defs and collides
with the current FiniteCoefficient.UpperLowerStar.Defs at the generated notation declaration
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. The source theorem remains a valid proof-plan
reference, but its current cached artifact cannot be combined with this library. This is a
follow-up build/API issue for formalizing splitData, not a hidden additional hole in the
present Lean proofs. The compatible four plan imports compile in the delivered set.
