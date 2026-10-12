## What changed

Replaced the sole sorry in `Sheaf.Paper.ZariskiEtaleResolutionHomologyDataExists`
with a complete Lean reduction to two separate comparison statements. The original
signature, universes, visibility and public imports are unchanged. The upper proof
uses Mathlib `InjectiveResolution.extMk_surjective` to represent an arbitrary Ext
class by a cocycle. It explicitly constructs the transported etale cocycle by
inverting the sheafification/free-abelian/Yoneda section equivalence. Naturality
with respect to composition, preservation of zero, and `b.comm` prove its cocycle
condition. Its identity-generator section equals the image section by the actual
inverse-equivalence law. Substituting the pullback-counit cocycle identity and
applying the cocycle-homology identity proves the required equation.

Added `Sheaf.Paper.ZariskiEtaleResolutionCocycleHomology` and
`Sheaf.Paper.ZariskiEtaleResolutionPullbackCocycle`, one public theorem each.
Updated the original node's proof, proof dependencies and proof origin to match
this reduction. The supplied injective resolutions are used throughout: there is
no new enough-injectives hypothesis and no construction chosen from a sorried
mere-existence theorem in a definition. The only new definition in the upper
module is a private, explicit composition of three existing adjunction equivalences.
The new nodes stay within the original unit `sk-thm-p1`; none of its realized
statement or proof-step nodes is bypassed.

All three delivered modules compiled in import order with the prescribed launcher.
The final delivery dry run also runs the project's static and axiom checks.

## Proved and sorry left

Closed: `zariski_etale_resolution_homology_data_exists`
(node `lem-zariski-etale-resolution-homology-data-exists`). No sorry remains in
its module or in its private section-equivalence helpers.

Added and left:

- `zariski_etale_resolution_cocycle_homology`
  (`lem-weil-pbc-zariski-etale-resolution-cocycle-homology`), in
  `Sheaf.Paper.ZariskiEtaleResolutionCocycleHomology`.
- `zariski_etale_resolution_pullback_cocycle`
  (`lem-weil-pbc-zariski-etale-resolution-pullback-cocycle`), in
  `Sheaf.Paper.ZariskiEtaleResolutionPullbackCocycle`.

This is a decomposition, not a sorry-free proof of the mathematical theorem:
one upper hole closed, two lower holes added, net minus one in the delivered
portion of the target closure. The two obligations are different parts of the
argument. The first has no fstar, augmentation or exact-inverse-image assumption:
it compares Ext cocycle representatives with section homology for any chain map.
The second contains no homology equivalences: it identifies the characterized
pullback-counit on the Ext class of a cocycle whose image section is specified.
The Lean proof constructs that image cocycle and combines the two results.
Neither new theorem is the upper statement under another name.

Edge cases checked in the statements and proof: q=0 is included by Mathlib's
extMk surjectivity with successor 1 and by the same chain equation; neither an
empty V nor the zero sheaf is excluded; no quasi-isomorphism or exactness of the
pushed resolution GI is assumed. There is no restriction on the chosen HasExt
universe beyond the unchanged original signature.

## No longer needed

Removed the upper module's proof imports:

- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`.
- `Sheaf.CategoryTheory.SiteCohomologyPullback`.
- `Sheaf.Paper.ZariskiEtaleResolutionHomologyIndependent`.

These are replaced by the two new cocycle-comparison imports. The old dependencies
`lem-weil-pbc-right-derived-universal-delta-functor`,
`lem-weil-pbc-site-cohomology-pullback` and
`lem-weil-pbc-zariski-etale-resolution-homology-independent` are no longer direct
proof dependencies of the upper node. Their mathematical role remains in the
lower pullback-cocycle argument and is recorded in its node; they are not reported
as globally obsolete. The new statement modules import only what their signatures
need and the Mathlib Ext cocycle API. No existing module is claimed globally
pruned, and no unit-level node is removed.

The existing `ObjectCohomologyPresheafResolution` theorem was read but is not
imported: its existential presheaf isomorphism does not assert the needed
compatibility on extMk cocycle representatives. The existing
`ExtPullbackResolutionSections` theorem was read but is not imported: its statement
concerns global etale cohomology for a scheme morphism and chosen resolutions,
rather than object cohomology for the continuous Zariski-to-etale functor supplied
here. The proved `ExtRightDerivedHom` theorem was also read; it supplies an
existential natural isomorphism without the required cocycle normalization.

## Where the brief, the DAG or earlier work was wrong

The DAG's numbered steps describe the mathematical argument but its existing
proof-dependency declarations do not directly provide the objectwise Ext-to-section
cocycle normalization or the pullback-counit identity for the arbitrary fstar of
this signature. Those two missing bridges are now separate, precise statements;
the representative and transported-cocycle glue is proved in Lean.

The old source citation to Cohomology on Sites Tag 0733(1) concerns degeneration
of the Leray spectral sequence under vanishing of higher direct images, not the
Ext-to-section normalization needed here. The new cocycle-homology node cites
Section 01FT (`equation-cohomology-object-site`) and Derived Categories Tag 06XR(1)
(`lemma-compute-ext-resolutions`). The pullback-cocycle node cites Cohomology Tags
01F8 and 01FB (`lemma-functoriality`, `remark-explain-arrow`), Derived Categories
013P and 015B(4) (`lemma-morphisms-lift`, `lemma-higher-derived-functors`), and
Section 01FT with Tag 0730 for preservation of injectives. The original signature
and node statement have not been changed. Original Stacks .tex sources were
fetched read-only into the sandbox scratchpad because the repository's literature
checkout is absent on this machine.

LeanSearch returned Internal Server Error and is recorded as unavailable, not as
absence. LeanFinder and Loogle found Mathlib's extMk, extMk_surjective,
extEquivCohomologyClass_extMk and extAddEquivCohomologyClass; grep confirmed these
APIs and the homology-map APIs. Blueprint searches for cocycles and 0733 found no
existing blueprint statement that gives either new bridge.

## New nodes

`lem-weil-pbc-zariski-etale-resolution-cocycle-homology` is the termwise
free-representable section comparison, with compatibility on specified cocycles
under any cochain map. Its proof constructs the two equivalences from adjunctions,
resolution Ext and homology; the final compatibility is just the induced map on
cycle classes. It is stated by `zariski_etale_resolution_cocycle_homology` in
`lean/Sheaf/Paper/ZariskiEtaleResolutionCocycleHomology.lean`.

`lem-weil-pbc-zariski-etale-resolution-pullback-cocycle` is the cocycle-class
identity for a characterized fstar followed by the counit. Its proof uses unit
comparison lifts, effaceability and dimension shifting, then the augmentation
triangle identity and homotopy independence. It is stated by
`zariski_etale_resolution_pullback_cocycle` in
`lean/Sheaf/Paper/ZariskiEtaleResolutionPullbackCocycle.lean`.

No definition or existing statement changed; no change record or forced adaptation
is needed.

## Second reading by E3

1. **Visible changes.** Compared each delivered module with the repository version.
   The existing target signature is byte-for-byte unchanged; only its proof and
   proof-only imports changed. The two additional files are new split-off theorem
   modules, and the node edits record their proof routes.

2. **Compilation and axioms.** Compiled all three modules in import order with the
   prescribed launcher. There are no errors, forbidden declarations, or sorry values
   in definitions. The two remaining theorem sorries are exactly the named split-off
   obligations. The axiom probe confines `sorryAx` to those open theorem statements.

3. **Statements.** Read both new theorem statements against their proofs and the
   target. The cocycle-homology statement is a termwise comparison under an arbitrary
   cochain map and has no augmentation or exactness hypothesis. The pullback-cocycle
   statement is the characterized counit identity for specified cocycles. They are
   strictly smaller than the target, have source citations and complete proof
   descriptions, and each has a matching DAG node. No existing declaration duplicates
   either statement.

4. **Pruning and route.** The target proof uses the explicit section equivalence,
   `InjectiveResolution.extMk_surjective`, the cocycle equation, and the two split
   obligations. The former right-derived, site-pullback, and homology-independence
   imports are no longer needed directly and are removed; the unit `sk-thm-p1` route
   and its realized steps remain represented in the new nodes.

5. **DAG agreement.** Checked theorem names, signatures, proof dependencies and proof
   origins in all three node files against the Lean code. The target node remains
   unchanged in statement and records the two genuine intermediate obligations. No
   definition or public existing interface changed.

Changed only this report section during second reading; no Lean proof, statement,
import, node statement, or definition was altered.
