## What changed

Kept the signature, visibility, universes and public imports of
`AlgebraicGeometry.properFlat_single_derivedDirectImage_perfect` unchanged.
Replaced its sorry by a complete Lean reduction: choose an affine neighbourhood;
transport the supplied open-site derived localization to the open subscheme and
its open sites by exact equivalences; obtain pseudo-coherence and finite Tor
dimension of the same restricted direct image; apply the existing
pseudo-coherent finite-Tor perfectness criterion; recover the ambient strictly
perfect witness using `Scheme.open_restriction_perfect_local_models`.
The localization transport is proved in two private helpers, with no sorry.
Only proof imports were added.

Added `Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent` and
`Sheaf.AlgebraicGeometry.ProperFlatSingleLocalFiniteTor`, one strictly smaller
claim in each module, and updated the parent's proof dependency record.
Pseudo-coherence provides bounded-above finite-free models but no lower bound.
The Tor claim supplies bounds for tensor cohomology but no finite-free models.
Their combination uses the existing criterion, rather than renaming perfection.

Sources read: the official Stacks pages
[0A1H](https://stacks.math.columbia.edu/tag/0A1H),
[0B91](https://stacks.math.columbia.edu/tag/0B91),
[08EV](https://stacks.math.columbia.edu/tag/08EV),
[08E7](https://stacks.math.columbia.edu/tag/08E7),
[01XD](https://stacks.math.columbia.edu/tag/01XD), and
[08CQ](https://stacks.math.columbia.edu/tag/08CQ).
The decomposition retains the coherence unit's Noetherian approximation and
proper-coherence route for pseudo-coherence, and its finite flat Cech model
for Tor bounds. It changes no unit statement or unit proof step.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.properFlat_single_derivedDirectImage_perfect`
(node `lem-pc-proper-flat-single-derived-direct-image-perfect`).
No sorry remains in the item's module.

Added two holes:

- `AlgebraicGeometry.properFlat_single_open_isPseudoCoherent`, node
  `lem-pc-proper-flat-single-open-pseudo-coherent`.
- `AlgebraicGeometry.properFlat_single_local_hasFiniteTorDimension`, node
  `lem-pc-proper-flat-single-local-finite-tor`.

This is a decomposition, not an unconditional proof or a positive net decrease:
one original hole closed and two new holes added. The already existing generic
perfectness criterion still contains its own sorry; it was not created here.
Both new declarations have source citations, complete proof descriptions, and
proof bodies exactly `:= by sorry`.

All three modules compile together without errors or warnings. Small cases were
checked against the statements: an empty base or open gives a vacuous
pseudo-coherence assertion and a zero Tor model; a zero module gives zero models;
identity morphisms reduce to finitely presented flat modules, which are locally
finite projective. No flatness of f is needed. U may be non-affine in the
pseudo-coherence lemma; its argument is pointwise affine-local. The Tor lemma
requires U affine so its inverse image has one finite affine cover and one bound.
It does not assert a uniform Tor interval on a non-quasi-compact base (disjoint
unions of projective spaces of increasing dimension forbid that).

## No longer needed

No original import was removed: the original file contained statement imports
only. No unneeded proof import was added.

The original parent's direct dependency
`lem-pc-noetherian-perfect-direct-image`
(`Sheaf.AlgebraicGeometry.NoetherianPerfectDirectImage`) is no longer used.
The proof now uses bounded coherence and pseudo-coherence at the Noetherian stage
inside the new pseudo-coherence claim, and combines pseudo-coherence with Tor
bounds at the original affine neighbourhood. The stronger tensor perfect-image
theorem is unnecessary for this argument.

`lem-pc-noetherian-approximation-data` and `lem-pc-rf-base-change-complex` are
removed from the parent's immediate proof dependencies but retained in the new
pseudo-coherence node's plan. They are not claimed as globally pruned.
`def-pc-perfect-complex` remains a statement dependency and is used downstream.
No deletion of any node or library module is proposed.

## Where the brief, the DAG or earlier work was wrong

The planned approximation and relatively flat derived-base-change declarations
require global families of scheme localizations in a common morphism universe.
The item's signature supplies only independent source and target localizations
and target open-site localizations. They cannot be applied directly with those
binders. The delivery preserves the item's signature and explicitly constructs
only the localizations it needs using exact equivalences.

More seriously, importing the planned Noetherian perfect-image module closes an
import cycle through `BoundedCoherentFiniteTorDirectImagePerfect`,
`DirectImageBoundedCoherent`, `CoherentSupportProperHigherDirectImage`,
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`,
`ProperFlatCechModel`, `ProperFlatCohomologyModel`,
`ProperFlatCohomologyProperties`, `ProperFlatFinitePresentationModel`,
`ProperFlatBoundedPresentationModel`, `ProperFlatAffineCechPerfectModel`,
`FiniteAffineCechModelPerfect`, back to this item. The approximation module also
reaches this item through its broad public import of source DirectImage.
Neither is imported here. Future work on the pseudo-coherence claim must use
lower Noetherian coherence/approximation interfaces without importing this
cycle. Its DAG plan is acyclic; this is a Lean import/interface issue.

A further finite-Tor proof attempt is saved in the scratchpad: it constructs a
finite affine Cech cover, uses existing bounds and flatness, proves K-flatness,
and composes the exact-open and restriction-single comparisons. Its tensor
vanishing glue compiles. The final named Cech derived comparison has landed in
source but its compiled artifact is not yet in the last green cache. The
scratchpad is not delivered; no partial sorry is left in a delivered proof.

The LeanSearch service returned Internal Server Error, recorded as unavailable;
LeanFinder and actual Mathlib grep searches returned no matching theorem.
No statement correction, forced adaptation, or definition change was made.

## New nodes

`lem-pc-proper-flat-single-open-pseudo-coherent`, in
`dag/nodes/sec-picard-framework/`, states pseudo-coherence of an arbitrary open
restriction with the supplied localizations. It isolates the Noetherian
approximation, bounded proper coherence, finite-free upper resolution, and
relative-flat base-change argument. Neither the criterion for perfection nor
the original theorem is a dependency of this new claim.

`lem-pc-proper-flat-single-local-finite-tor`, in the same directory, states finite
Tor dimension of each affine-open restriction. Its proof uses the bounded flat
Cech model, derived comparison, K-flatness, and tensor vanishing. It needs no
Noetherian approximation and no pseudo-coherence. Each node inherits the
parent's chapter, unit and nearest blueprint ancestor, records the actual three
search kinds, and names its own new Lean module and verbatim signature.


## Second reading by C1

1. Compared every delivered module with the repository. Only the parent existed;
   its existing declaration signature, universes, visibility, docstring and public
   imports are unchanged. The other two modules are new and have no definitions.
   No change record or forced adaptation is needed. Restored the single space
   before the parent's `:=` so the existing signature is byte-for-byte preserved.
   Verdict: pass.
2. Compiled all three modules in import order with lcompile.py, without errors or
   warnings. Read every proof and scanned for forbidden declarations. The only
   new sorry bodies are precisely the two named public split-off theorems listed
   above. Explicit scratch-copy `#print axioms` checks of the parent, both private
   helpers and both split-off theorems gave only propext, Classical.choice,
   Quot.sound, and (for the parent and open statements) sorryAx. Neither private
   helper uses sorryAx. The equivalence and localization data are constructed
   explicitly: choice extracts the proved Nonempty of that actual construction,
   not an arbitrary witness of an unproved existence claim. Verdict: pass.
3. Read the definitions of pseudo-coherence, finite Tor dimension, and perfectness
   and checked the source arguments in official Stacks Tags
   [0A1H](https://stacks.math.columbia.edu/tag/0A1H),
   [0B91](https://stacks.math.columbia.edu/tag/0B91), and
   [08CG](https://stacks.math.columbia.edu/tag/08CG).
   The split claims are true, complementary parts of the argument: finite Tor
   bounds give no finite-free models, while pseudo-coherence gives no lower bound.
   Empty schemes, empty opens, zero modules and identity morphisms cause no
   exception. Bounds are asserted only on affine opens, avoiding the unbounded
   disjoint-union example. Independently searched LeanFinder for "proper
   pushforward flat coherent sheaf bounded Tor amplitude pseudo coherent complex",
   Loogle for HasDerivedCategory, Mathlib grep for PseudoCoherent, and the project
   for pseudo-coherent/finite-Tor direct-image declarations. No usable duplicate
   or shorter theorem with these independent localizations was found. Reviewed
   the saved Tor proof: its required finiteAffineCechModel_derivedComparison is
   present in source but absent from the green compiled cache. Did not duplicate
   that declaration or compile a replacement outside the contract. Both new
   holes retain source-backed complete proof docstrings and matching nodes.
   Verdict: pass, two genuine split-off holes remain.
4. Read the proof from the parent downward. Its five added plain imports support
   the two split claims, the existing criterion, the proved open locality lemma,
   and localization transport. Original public imports support the unchanged
   statement. No proof-only public import was added. All four old proof_deps are
   accounted for under No longer needed: the perfect-complex definition remains
   a statement dependency, approximation and base change move to the new plan,
   and the stronger Noetherian perfect-image result is unused. This does not
   establish global pruning of any module. Read sk-thm-picard-coherence.json:
   its realized fields are already empty and remain unchanged; the new plans
   retain Noetherian approximation/proper coherence and the bounded flat Cech
   route of its step. Verdict: pass; decomposition, not positive net progress.
5. Read all three node records against their Lean declarations and proof plans.
   The parent's proof_deps are exactly the localization, two split claims,
   criterion and locality route. Each new node has the required source,
   searches, provenance, chapter/unit/blueprint ancestry and verbatim Lean
   signature. The new nodes are genuine parts of the argument, not renamed
   perfection claims. Verdict: pass.

Second reading changed only the parent's pre-proof whitespace and added this
review record. No mathematical proof or statement repair was necessary.
