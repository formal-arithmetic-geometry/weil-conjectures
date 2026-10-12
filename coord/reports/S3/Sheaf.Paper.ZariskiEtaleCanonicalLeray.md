## What changed

Replaced the sole hole of `Sheaf.Paper.ZariskiEtaleCanonicalLeray` with a complete
Lean reduction following the direct injective-resolution proof of Stacks 0733(1).
The existing theorem signature and all six public imports are unchanged.

Two new proof-only imports expose strictly smaller intermediate statements:
`Sheaf.Paper.ZariskiEtalePushedResolution` covers the exact inverse image and
quasi-isomorphism of the fixed pushed augmentation (original DAG steps 1–3);
`Sheaf.Paper.ZariskiEtaleResolutionMap` covers the explicit resolution formula
for the canonical pullback followed by counit (original DAG step 4).
Neither statement asserts the target's isomorphism conclusion.

The target constructs `I := InjectiveResolution.of F` using Mathlib's affine-etale
Grothendieck-category instance. It constructs the actual pushed complex `R`, with
augmentation the inverse single-complex comparison followed by `G.map I.ι`.
Termwise injectivity is proved by the adjunction with exact left adjoint, using
`Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits`. Only the proof
that this specific augmentation is a quasi-isomorphism remains in the first split.
The identity of `R.cocomplex` satisfies the comparison's augmentation equation by
`singleMapHomologicalComplex_inv_app_self`. The second split represents the
specified canonical map by homology of that evaluated identity. The target proves
injectivity and surjectivity explicitly through the two additive equivalences.
No definition is added, and no complex is chosen from a mere existence theorem.

Read Stacks 072W, 0730, 0733(1), 09AX, 01F7, 01F8 and 01FB online because their
TeX files are absent in this read-only clone. The source statement 0733 allows the
direct resolution argument. The unit `sk-thm-p1` and all its realized steps stay:
this item is below those realized nodes, and no unit-level route is bypassed.

LeanFinder located `InjectiveResolution.extAddEquivCohomologyClass`, but no complete
canonical comparison. LeanSearch returned Internal Server Error. Loogle on
`Sheaf.H` did not resolve that identifier. Grep and direct signature inspection
found the existing Leray theorem, source-library global-cohomology maps,
`CohomologyRightDerivedSections`, and `CohomologyDerivedEvaluation`; none gives the
required arbitrary-Ext-universe objectwise canonical comparison. Search records
are included in both new nodes. Whole-blueprint searches for `Leray`,
`resolution comparison`, and `0733` found no duplicate: the imported Leray nodes
concern compositions or other sites, not either new resolution interface.

Edge checks: zero F gives zero section-complex homology; empty V uses its actual
zero evaluation and does not require nonemptiness; q=0 is included by the
augmentation equation and the triangle identity. The first split treats general
i(top), whose underlying scheme is X but whose structural morphism need not be
identity; localization at that etale object followed by exact extension by zero
is required. The second split does not assume vanishing and applies to every
augmentation-compatible complex map, including a noninvertible one. Its Ext
universe remains arbitrary, with only coefficient-universe section homology.

Compiled all three delivery modules in import order with `lcompile.py --all`.
The final compile has no errors or warnings. The target signature was compared
verbatim with the repository declaration, and both new-node signatures were
compared verbatim with their modules. No new dependency edge closes a cycle.
The import-direction checker accepts
the source-library injective-preservation import. The final dry run is the
validation required for this delivery; nothing is pushed by the worker.

## Proved and sorry left

Closed: `zariski_etale_canonical_leray`, node
`lem-weil-pbc-zariski-etale-canonical-leray`: 1 of the item's 1 holes closed.
Its proof is complete relative to the following two intermediate theorems.

Added and left with exactly `:= by sorry`:

- `zariski_etale_pushed_resolution`, node
  `lem-weil-pbc-zariski-etale-pushed-resolution`, module
  `Sheaf.Paper.ZariskiEtalePushedResolution`.
- `zariski_etale_resolution_map`, node
  `lem-weil-pbc-zariski-etale-resolution-map`, module
  `Sheaf.Paper.ZariskiEtaleResolutionMap`.

This is a decomposition: one upper hole closed and two strictly smaller holes
added, not an independent proof or a positive net hole count. No sorry remains
in the item's module, and the delivery adds no other holes. The maintainer's
pinned-baseline ledger decides the import-closure progress.

## No longer needed

Removed every original proof import:

- `Mathlib.CategoryTheory.Sites.LocallyBijective`.
- `Sheaf.CategoryTheory.SiteLerayDegenerate`, node
  `lem-weil-pbc-site-leray-degenerate`.
- `Sheaf.CategoryTheory.SiteCohomologyPullback`, node
  `lem-weil-pbc-site-cohomology-pullback`.
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`, node
  `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`.
- `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`, node
  `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`.

The other old `proof_deps` entries removed from the target node are
`def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-site-sheafification-iso-locally-bijective`, and
`def-weil-pbc-sheafification`. Their notions remain in the public statement API
or in the smaller bridges; none is a direct proof dependency of the new target
reduction. This completes the old-to-new dependency accounting, including nodes
whose imports were already supplied transitively.

The unspecified existential Leray family is eliminated entirely from this route:
its existence does not identify the target's canonical composite. The other
removed declarations are not applied in the target's new proof; their mathematical
content remains relevant to proving the new bridges, and is cited there in the
DAG. Likewise the locally-bijective sheafification leaf and exact sheafification
remain in the first bridge's plan, rather than pretending to be direct Lean
applications in the target. No global pruning count is asserted for a module
that another target or another remaining proof may still reach. All original
public imports remain because they describe the existing statement's API.

## Where the brief, the DAG or earlier work was wrong

The DAG correctly warned that `siteLeray_degenerate` has only an existential family
and leaves the canonical-map identification to this bridge. Reading its signature
confirms that a direct `exact siteLeray_degenerate ...` cannot prove this target.

The existing general site lemmas use equal small-category/coefficient/Ext
universes and additional precoverage hypotheses. The target deliberately has an
arbitrary Ext universe. The new resolution representation preserves this instead
of adding sheafification assumptions in that universe or changing the target.

For enough injectives, importing the project's older essentially-small-site
helper would impose an unnecessary larger coefficient universe. Mathlib's
`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology` in
`Mathlib.AlgebraicGeometry.Sites.AffineEtale` works at precisely the coefficient
universe already in the target, so this part is proved by existing instances.

The first bridge uses `lem-weil-pbc-site-extension-by-zero-exact` as a tool from
`sk-prop-cd`: exactness of extension by zero for localization at an arbitrary
etale object supplies the general-i factorization. The usual inclusion's
existential theorem does not state it for arbitrary i. No `tool_uses` maintainer
field is written by the worker.

## New nodes

`lem-weil-pbc-zariski-etale-pushed-resolution` isolates exactness of abelian inverse
image and local-vanishing-to-QuasiIso for the actual pushed augmentation. It has
no fstar parameter or cohomology-comparison isomorphism conclusion. The source,
complete proof, and three search kinds are in its node and new module.

`lem-weil-pbc-zariski-etale-resolution-map` isolates the canonical resolution
formula, with any supplied I, R and augmentation-compatible a. It assumes
neither local vanishing nor an isomorphism a, and concludes an equation under
additive equivalences, rather than invertibility. Its proof records the needed
Ext/section-complex and delta-functor compatibility. Its source, complete proof,
and three search kinds are in its node and new module.

Updated only `proof`, `proof_deps`, and `proof_origin` of the item's existing node.
No statement, definition, target signature, unit record, or change record changes.

## Second reading by S3

1. Compared the delivered target module with the repository using `diff`, and
   compared the entire theorem signature byte for byte: identical. Changes are
   confined to proof-only imports and the proof body. The six original public
   imports, definitions, and existing docstring are unchanged. The existing node
   differs only in `proof`, `proof_deps`, and `proof_origin`. Verdict: pass.

2. Independently compiled all three modules in import order with `lcompile.py`.
   Scratch copies with `#print axioms` for all three declarations show only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The only two source
   holes are the named new bridge theorems, each exactly `:= by sorry`. There are
   no definitions, arbitrary witness constructions, or forbidden declarations.
   The target builds the actual pushed complex and its actual augmentation;
   its use of the existential additive equivalences eliminates them only into
   the proposition `IsIso`. Verdict: pass, conditional on the two reported holes.

3. Read both new signatures and their full docstring proofs. The first fixes an
   arbitrary injective resolution and its pushed augmentation, and contains no
   canonical-map conclusion. The second concerns any augmentation-compatible
   complex map, assumes no vanishing, and gives the resolution formula rather
   than invertibility. These are separate strict parts of the argument, not
   a renamed target. Checked degree zero (unit/counit triangle and augmentation),
   zero coefficients, the empty open, and arbitrary i(top): localization followed
   by exact extension by zero handles a nonidentity structural morphism. For
   general a, termwise injectivity of i_*I follows from exact inverse image;
   homotopy uniqueness of lifts from the resolution R identifies its induced
   cohomology map. Universal delta-functor uniqueness applies objectwise in V
   because hfstar supplies coefficient naturality and all connecting maps.
   Read Stacks [0733](https://stacks.math.columbia.edu/tag/0733),
   [01FB](https://stacks.math.columbia.edu/tag/01FB), and
   [03DJ](https://stacks.math.columbia.edu/tag/03DJ) independently.
   A fresh LeanFinder query for a sheaf cohomology comparison computed by a chain
   map found right-derived resolution naturality lemmas, not this objectwise
   arbitrary-Ext-universe interface. Grep with `resolution comparison` and
   `extAddEquivCohomologyClass` found `CohomologyDerivedEvaluation` (terminal
   object, global H, fixed Ext universe) and scheme module-section comparisons,
   neither an exact match. Generic Mathlib pullback left-exactness requires
   representable flatness and left-Kan finite-limit preservation, so does not
   close the arbitrary-i bridge by an immediate instance. Verdict: pass;
   neither bridge can be closed by a few-minute application of these results.

4. Read the reduction from the target downward: enough injectives comes from
   Mathlib, preservation of injectives from the adjunction, and the final
   argument is direct transport of bijectivity of the evaluated identity.
   The new imports are used for these instances or the two bridges; the new
   modules' public imports supply their signatures. All seven old DAG proof
   dependencies are now accounted for in `No longer needed`. Inspected
   `dag/units/sk-thm-p1.json` realized statement and all four step lists: this
   item lies below them and none is replaced or bypassed. Verdict: pass.

5. Checked the new nodes' required fields, declaration signatures against Lean,
   sources, search records, and proof-step dependency unions. The target node
   records the two applied bridges, injective-resolution construction, existing
   Mathlib enough-injectives leaf, and concrete bijectivity argument. The bridge
   nodes retain the source's smaller resolution and canonical-identification
   obligations with their natural-language proofs. Verdict: pass.

Second reading changed only this report: completed the missing old-node pruning
accounting and added this independent review. No Lean or node repair was needed.
The result remains a decomposition (one hole closed, two added), not a net proof.
