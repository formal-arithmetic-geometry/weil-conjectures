## What changed

Replaced the single sorry in `AlgebraicGeometry.affine_koszul_scalar_ext_comparison`
with a compiling proof from the existing Koszul quotient augmentation and three
intermediate results. The original signature, universes, hypotheses, conclusion,
and docstring are unchanged. All new comparison imports in the item are private.

Added five modules, one public theorem per module:

- `Sheaf.AlgebraicGeometry.AffineKoszulFiniteFreeResolution`: proved the actual
  integer-indexed sheafified Koszul complex is bounded above, termwise finite free,
  and admits a quasi-isomorphism to the restricted pushforward single complex.
  The private quotient presentation is constructed from the surjective sections
  map and its kernel lift. Wedge bases prove freeness; exactness of tilde uses the shared finite-limit theorem.
- `Sheaf.AlgebraicGeometry.AffineKoszulHomCoordinates`: proved the passage from
  the complex comparison to associated module homology. The proof uses
  the shared finite-limit theorem and the source library's mapHomologicalComplexHomologyIso.
- `Sheaf.AlgebraicGeometry.LocalFiniteFreeScalarHomology`: the remaining local
  derived-Hom comparison, with no affine or Koszul hypotheses.
- `Sheaf.AlgebraicGeometry.AffineKoszulHomComplexIso`: the remaining ordinary
  complex coordinate isomorphism, with no regularity, closed immersion,
  generation or augmentation hypothesis.

- `Sheaf.AlgebraicGeometry.TildePreservesFiniteLimits`: proved the stronger
  shared finite-limit preservation theorem. Removed both copies of the private
  `tilde_preservesKernel` helper; both consumers now import and apply this result.

Repair of the returned point: the cited theorem in
`AffineDerivedTildeHomologyComparison` is private, so importing it cannot expose
it. Generalized the helper to all finite limits in one new module, with a proved
local kernel argument, and replaced both copies. No existing library module or
signature was changed.

The main proof obtains the augmentation from
`ExteriorAlgebra.exists_koszul_quotient_augmentation`, extracts the resolution's
bounds, bases and augmentation, applies the local Hom comparison, and composes
with the over-site inverse applied to the coordinate homology isomorphism.
No data is chosen from an unproved existence theorem in a definition: no new
definitions are introduced. Every private helper is proved.

Validation: all six delivered modules compile in import order via lcompile.py.
The theorem types were elaborated with autoImplicit=false. The finite free
resolution and exact-homology steps were compiled repeatedly while repairing
instances and quotient/chart transport. The new statements include n=0, rank
zero, the zero ring, empty opens and every integer degree. For n=0 the two
Koszul models have only the degree-zero unit; negative Hom degrees are zero.
For an empty open, the module category is zero. The local lemma's E=0 case
forces K|U=0 through its quasi-isomorphism, so both Hom homologies are zero.

Sources read: Stacks Project https://stacks.math.columbia.edu/tag/0BQZ,
https://stacks.math.columbia.edu/tag/08DM and
https://stacks.math.columbia.edu/tag/08DL, as well as Tags
068C, 01I9, 01IB and 01HV. Tag 01HV is the precise source for exactness of
associated sheaves; Tag 01I9(2) is used for the affine pushforward dictionary.
Mathlib and existing project theorem
signatures were read before creating the intermediate statements. Searches
are recorded in searches.jsonl; LeanSearch returned Internal Server Error and
is explicitly recorded as unavailable, never as evidence of absence.

## Proved and sorry left

Closed the item's original hole:
`AlgebraicGeometry.affine_koszul_scalar_ext_comparison`
(node `lem-sc-affine-koszul-scalar-ext-comparison`).

New proved declarations:
`AlgebraicGeometry.affine_koszul_finite_free_resolution`
(node `lem-sc-affine-koszul-finite-free-resolution`) and
`AlgebraicGeometry.affine_koszul_hom_coordinates`
(node `lem-sc-affine-koszul-hom-coordinates`).

Additional proved repair declaration:
`AlgebraicGeometry.tilde_preserves_finite_limits`
(node `lem-sc-tilde-preserves-finite-limits`), with no new holes.

Every new sorry, and the only sorries in the delivered files:

- `AlgebraicGeometry.local_finite_free_scalar_homology`
  (`lem-sc-local-finite-free-scalar-homology`). Remaining work is the exact
  over-site/opens-site Hom transport and comparison through a common K-injective
  model in arbitrary ambient derived universes. The finite free model and open
  restriction theorems exist, but do not directly express this universe/site glue.
- `AlgebraicGeometry.affine_koszul_hom_complex_iso`
  (`lem-sc-affine-koszul-hom-complex-iso`). Remaining work is to construct the
  termwise finite free coordinate maps and prove the total Hom sign and chain
  compatibility. Exact homology transport has already been proved separately.

This is a decomposition, not a sorry-free proof of the target closure:
one upper hole closed and two strictly smaller holes added (net one additional
hole before any whole-library pruning). The existing Koszul
augmentation and quotient module identification are used without copying their
proof obligations. No other existing hole was changed.

## No longer needed

Removed both duplicated private kernel declarations. Their proofs are now
factored through `TildePreservesFiniteLimits`. Retained the consumers' imports of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` because they
provide `Scheme.Modules.preservesLimitsOfSize_restrictFunctor`, required for the
chart restriction. No additional modules are globally pruned by this repair.

Removed the item's three direct proof imports:
`Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`,
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`, and
`Sheaf.Paper.DerivedInternalHomRestrictOpen`.

The nonnegative-chain interface
`AlgebraicGeometry.exists_affine_quotient_sheafified_resolution`
(node `lem-sc-affine-quotient-resolution-sheafification`, module
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`)
is no longer used by this route. The augmentation is mapped directly in integer
cochain degrees, avoiding a chain/cochain exchange comparison. Its smaller
quotient module identification (`lem-sc-affine-quotient-restricted-iso`) and
quasi-coherent kernel theorem remain needed and are imported in the proved
resolution module. This does not assert the old module is globally unreachable;
other targets may still use it.

`lem-sc-derived-hom-finite-free-model` and
`lem-sc-derived-internal-hom-restrict-open` remain mathematical dependencies of
the named local comparison obligation; they have not been pruned from its plan.
Their unused imports are absent from that statement module until its proof is
written. The old direct proof dependency `def-pur-derived-internal-hom` is also
absent from the item's new `proof_deps`: it remains a statement dependency and
a proof dependency of the local comparison, so its module remains imported.
This is relocation of the direct edge, not global pruning. No unit statement or unit proof step has been bypassed: the unit's
realized arrays are empty, and this reduction stays inside the same affine
Koszul resolution / finite free Hom / exact sheafification argument.

## Where the brief, the DAG or earlier work was wrong

The returned landing check correctly found duplicate private kernel theorems.
The prior search missed these helpers; the statement that whole-library searches
found no duplicate concerned the four public intermediate conclusions, not the
helpers. Both duplicates have now been removed, and their shared generalization
is explicit.

The existing proof plan suppresses two substantial glue operations: transporting
Hom through the over-site equivalence while retaining an arbitrary ambient
derived universe, and identifying the sheafified Koszul Hom differentials with
the signed algebraic dual complex. The existing dependency signatures do not
supply either as a ready-to-apply theorem. These operations are now explicit,
independent named obligations, rather than an unstated one-line transport.

The exact quotient sheafification lemma is indexed by nonnegative chains, whereas
the available Koszul augmentation is already integer-indexed. A direct exact
functor calculation removes that mismatch, and is proved in the delivery.
The static ancestor helper prints None for this item's created.item chain;
the existing item's explicit blueprint field records lem-sc-finite-duality, which
is retained for the new nodes. Whole-blueprint searches for Koszul Hom,
Koszul resolution and finite free Hom found no duplicate of the new statements.
No existing interface or statement has changed. No forced adaptations.

## New nodes

`lem-sc-local-finite-free-scalar-homology` is the generic open-local comparison
of scalar derived Hom homology with a supplied finite free resolution. It has
no closed immersion, affine chart or Koszul sequence in its signature.

`lem-sc-affine-koszul-finite-free-resolution` records the proved sheafified
augmentation, bounded-above property and finite free terms. It takes an
already supplied algebraic augmentation and has no derived Hom assertion.

`lem-sc-affine-koszul-hom-complex-iso` records the ordinary complex coordinate
isomorphism for an arbitrary finite sequence. It has no regularity,
augmentation or derived category in its signature.

`lem-sc-affine-koszul-hom-coordinates` records the proved exact-homology
consequence of that complex comparison. There is no closed immersion or
regularity hypothesis. All five new nodes are in sec-picard-framework and retain
the parent's unit. No change records are required.

`lem-sc-tilde-preserves-finite-limits` records the proved shared generalization
from preservation of individual kernels to all finite limits, for arbitrary
commutative rings. Its consumers are the finite free resolution and homology
coordinates modules. Their proof dependencies now point to this node.

The following second reading predates this repair and must be repeated by the
independent reader for the changed proof factoring and the sixth module.

## Earlier second reading (a previous round; superseded)

1. PASS. Compared the existing module with the repository using diff: only its
   private proof imports and the original sorry body change. The theorem signature,
   universes, visibility, hypotheses, conclusion and docstring are byte-for-byte
   unchanged. The only existing node edits are proof, proof_deps and proof_origin.
   All four new node Lean signatures agree verbatim with their module declarations.
2. PASS. Independently compiled all five modules in dependency order with lcompile.py.
   Inspected every proof and private helper: no new data definitions, arbitrary
   witness definitions, forbidden declarations or concealed holes. The two named
   sorries are exactly the reported local and ordinary-complex comparisons. Explicit
   axiom printing and the delivery probe check the allowed axiom set, including
   sorryAx from the reported obligations and existing open dependencies. The
   resolution theorem prints exactly propext, Classical.choice and Quot.sound;
   the other four declarations additionally print sorryAx and no other axiom.
3. PASS after a documentation repair. Both open statements are genuine, strictly
   smaller parts of the original argument. The local statement has no affine,
   immersion, regularity or Koszul condition; the ordinary complex statement has
   no derived Hom, augmentation or regularity condition. Checked the degree-zero
   empty sequence, a one-element sequence (d^0 is negative precomposition),
   negative degrees, zero rings, rank-zero terms, zero resolutions and empty opens.
   The generic local statement needs bounded-above, not bounded, freeness: choose
   a bounded-below injective resolution and truncate the source sufficiently far
   below for each fixed cohomology degree. Clarified this in its proof and node;
   Tag 08DM alone concerns strictly perfect complexes. Repeated semantic, Loogle
   and grep searches with different wording; found freeHomEquiv, homObjFreeIso,
   the proved open-restriction and finite-free model interfaces, but no complete
   substitute for either remaining comparison. The affineFiniteProjectiveHomModel
   statement is broader, remains sorry and supplies a derived replacement rather
   than this ordinary Koszul complex isomorphism. Neither hole closes in a few
   minutes from these interfaces.
4. PASS. Read the old planned dependencies and their actual declarations. The
   integer-indexed augmentation avoids the unnecessary nonnegative-chain
   sheafification interface. The remaining Hom transport and sign calculation
   are needed. The unit sk-thm-picard-duality has empty realized arrays; its route
   is unchanged and no unit step is replaced. Completed the report's accounting
   for the old direct def-pur-derived-internal-hom edge. Removed the redundant
   HomologySequence import from the new local statement. Tested removal of the
   coordinates module's private PreservesQuasiIso import: compilation showed
   mapHomologicalComplexHomologyIso is unavailable without it, so retained it.
   Existing public imports are unchanged.
5. PASS. Read all five nodes against the Lean. The supplied augmentation, explicit
   quotient presentation, exterior-power bases, quasi-coherent kernel argument,
   exact homology transport and composition are recorded correctly. Each new
   node has source, proof, dependency union, provenance, searches, creation,
   blueprint, chapter, unit and exact Lean records. The local proof record now
   explicitly chooses a bounded-below injective representative. No change record
   is required because no existing statement, definition or public import changed.

Changes by this reader: clarified the bounded-below representative/truncation
argument and its source scope; removed one redundant import in a new module;
completed direct-edge pruning accounting. No proof body was rewritten. This is
one original hole closed out of one, two new holes left, and two additional new
intermediate theorems proved; it remains a decomposition with net +1 hole before
pruning, not a claim of an axiom-free target closure.


## Second reading by N1

1. PASS. Independently diffed every delivered module against the repository.
   Only AffineKoszulScalarExtComparison already exists: its public imports,
   declaration signature, universes, hypotheses, conclusion and docstring are
   byte-for-byte unchanged. Its private proof imports and proof body change.
   No existing definition or other module is adapted. The existing node changes
   only proof, proof_deps and proof_origin; no change record is required.
2. PASS. Independently compiled all six modules in dependency order with
   lcompile.py, without errors or warnings. Read every proof and helper and
   scanned forbidden declarations: no new data definitions, arbitrary witness
   definitions, concealed holes or forbidden axioms. The only two sorries are
   the named local_finite_free_scalar_homology and affine_koszul_hom_complex_iso.
   Explicit #print axioms in scratchpad/lean/AxiomCheck.lean shows exactly
   propext, Classical.choice and Quot.sound for affine_koszul_finite_free_resolution
   and tilde_preserves_finite_limits. The other four public declarations add
   only sorryAx from the recorded open obligations and existing dependencies.
3. PASS. The two open statements are proper parts of the original argument:
   generic open-local derived Hom transport and ordinary finite free coordinate
   comparison. Neither restates scalar Ext for a regular closed immersion.
   Checked empty sequences, one generator, negative degrees, rank-zero terms,
   zero rings, empty charts and zero resolutions. In the one-generator case
   the Hom differential in degree zero is minus precomposition, matching the
   signed algebraic dual. For bounded-above E and bounded-below injective I,
   only finitely many source degrees contribute in each fixed Hom degree;
   truncating sufficiently far below preserves the adjacent terms needed to
   compute that cohomology. No lower bound on E is implicitly assumed.
   Re-read the existing derivedInternalHom_of_boundedAbove_finiteFree,
   derivedInternalHom_restrict_open and affineFiniteProjectiveHomModel interfaces.
   Repeated LeanFinder, Loogle and grep searches with internal sheaf Hom,
   associated exterior powers, finite duals and single complexes. Found
   freeHomEquiv and the project's homObjFreeIso, but neither supplies the
   over-site/universe comparison or the entire signed complex isomorphism.
   Neither remaining hole closes in a few minutes from these interfaces.
   Verified sources directly: [08DL](https://stacks.math.columbia.edu/tag/08DL),
   [08DM](https://stacks.math.columbia.edu/tag/08DM),
   [0BQZ](https://stacks.math.columbia.edu/tag/0BQZ), and
   [01HV](https://stacks.math.columbia.edu/tag/01HV).
   A broader local search also found an exact finite-limit conclusion in the
   private helper of AffineProjectiveSectionsSheafification. It is inaccessible
   through an ordinary import, just like the previously reported kernel helper.
   Recorded that overlap in the new node; the present public interface can
   support future consolidation, without adapting unrelated claimed modules.
4. PASS after an import visibility repair. Read the proof top down against all
   old proof_deps. The integer-indexed augmentation bypasses the nonnegative
   chain interface; the finite free bases and exact homology transport are
   actual proofs. The report accounts for every old direct dependency removed
   or relocated. The unit sk-thm-picard-duality has empty realized arrays; this
   reduction keeps its affine Koszul/finite free Hom route. Changed the new
   finite-limit module's Preadditive.LeftExact import from public to private:
   only its proof needs that module. The resulting file compiles. Other imports
   support statement notation, explicit proof lemmas, or chart exactness
   instances; retained the private PreservesQuasiIso import for the homology
   comparison theorem.
5. PASS after a provenance repair. Compared all six Lean signatures verbatim
   with their nodes and checked each proof_deps equals the union of step uses.
   Every dependency id exists. Read the proof steps against the augmentation,
   explicit quotient construction, wedge bases, shared kernel limit argument,
   complex comparison and homology composition. All five new nodes have source,
   complete proof plans, search records, creation, blueprint, chapter, unit and
   matching Lean records. Corrected the shared finite-limit node's proof_origin
   source from the copied Koszul citation to Schemes, Tag 01HV.

Changes by this reader: made Preadditive.LeftExact a private proof import,
corrected the finite-limit node's source provenance, and recorded its existing
private finite-limit overlap. No theorem statement or proof body changed.
This delivery closes the one original hole and adds two strictly smaller holes:
a decomposition with net +1 hole before whole-library pruning. No global module
pruning is claimed; the direct AffineQuotientResolutionSheafification import is
removed, while its smaller quotient identification remains used.
