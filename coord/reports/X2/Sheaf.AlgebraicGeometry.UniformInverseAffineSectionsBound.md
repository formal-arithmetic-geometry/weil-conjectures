## What changed

Replaced the earlier failed candidate. The original signature and all five public imports
of `UniformInverseAffineSectionsBound` stay unchanged. Its proof now chooses neighbourhood
bounds uniform in the coefficient module, extracts a finite subcover using compactness,
takes `max 1 (t.sup n)`, proves global higher-direct-image vanishing by the existing proved
`Scheme.Modules.isZero_of_iSup_eq_top`, and transports zero sections across an affine-open
Leray comparison.

Added two modules, each with one strictly lower statement:
`LocalUniformHigherDirectImageBound` (a neighbourhood bound, without compactness of the base)
and `AffineOpenHigherDirectImageSectionsIso` (a fixed-degree comparison, without a vanishing
bound). Updated the original node's proof, proof dependencies and proof origin accordingly.
No existing statement, definition or target interface changes; no forced adaptations.

The old `UniformHigherDirectImageBoundForBaseChange` and
`OpenSectionsVanishingOfHigherDirectImageBound` candidates and their nodes are removed from
this sandbox; they were rejected and never landed. The new comparison explicitly assumes
both `QuasiCompact f` and `QuasiSeparated f`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_uniform_inverse_affine_sections_bound`
(node `lem-pc-uniform-inverse-affine-sections-bound`). Its combination proof contains no sorry.

Added exactly two named holes:

- `AlgebraicGeometry.exists_local_uniform_higherDirectImage_bound`, node
  `lem-pc-local-uniform-higher-direct-image-bound`.
- `AlgebraicGeometry.nonempty_affineOpen_higherDirectImage_sections_iso`, node
  `lem-pc-affine-open-higher-direct-image-sections-iso`.

Each is in its own new module, with proof exactly `:= by sorry`, a source and complete proof
in words. This is a decomposition: one upper hole closed, two lower holes added, raw net -1;
it is not an axiom-free proof of the mathematical theorem. Classical selection of bounds
occurs only inside a proposition's proof; no definition chooses an arbitrary unproved witness.

The three modules compile together in import order. Edge cases checked against the argument:
empty base gives an empty finite subcover with supremum zero and final bound 1; empty source
or inverse-image open gives zero groups; the local bound permits n=0 only where its quantified
vanishing holds; the affine comparison includes p=0 as the ordinary section identity. No
assumption of separatedness of f, quasi-separatedness of the whole base, or quasi-coherence
of arbitrary higher direct images is silently introduced.

## No longer needed

Removed these direct proof imports from the item's module:
`Sheaf.AlgebraicGeometry.LerayDegenerateSections`,
`Sheaf.Topology.RestrictInjectiveResolution`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`.
Their corresponding nodes remain needed in the two lower statements' plans and their modules
are imported there. They are therefore not globally pruned.

The original arbitrary-base-change uniform-bound declaration
`Scheme.Modules.exists_isZero_higherDirectImage_of_isPullback` in
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective` is not used or imported on this route.
The DAG node `lem-pc-finite-support-hi` is still cited by the comparison for clause (1),
quasi-coherence alone; its global uniform-bound clauses (2) and (3) are not needed by the
combination proof. There is no claim that this multi-clause node is globally pruned.

The original nodes for affine vanishing, Leray and restriction of injective resolutions stay
needed below the comparison. No additional existing DAG node or library module can be
certified globally unreachable from this item's delivery alone. Global modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The earlier split-off bound copied the entire existing arbitrary-base-change theorem; this
attempt does not deliver that duplicate. The original planned import is cyclic:
Projective -> DirectImage.Sections -> DerivedDirectImagePreservesDirectSums ->
DerivedDirectImageCohomologyCoproduct -> DerivedDirectImageCoproductAffineTruncation ->
DerivedDirectImageUniformAffineTruncation -> DerivedDirectImageUniformTruncationBound ->
UniformDirectImageBoundCore -> UniformInverseAffineSectionsBound. We do not adapt those
unclaimed modules. Instead we expose the local affine-base argument as a separate part and
write the finite-subcover/global-vanishing argument here.

The earlier comparison omitted qcqs assumptions needed for quasi-coherence of higher direct
images. Both are present now. Existing `DirectImage.Sections` local-bound and affine-section
statements assume IsSeparated and/or fix one coefficient module before choosing the bound;
they do not give either new signature. The two new statements have complete sourced plans;
future workers must use the existing quasi-coherence clause, not duplicate it.

Read the source directly from the Stacks Project:
[01XJ](https://stacks.math.columbia.edu/tag/01XJ),
[01XK](https://stacks.math.columbia.edu/tag/01XK),
[071L](https://stacks.math.columbia.edu/tag/071L), and
[01E4](https://stacks.math.columbia.edu/tag/01E4).
The quantitative finite-cover lemma for general qcqs schemes is 071L, not 01XI (the latter
requires affine diagonal). The local plan uses quasi-compact-open induction, affine vanishing
and Mayer-Vietoris, which are already stated, and then the existing cohomology-presheaf
identification. The unit `sk-thm-picard-duality` has no realized nodes naming this item; its
statement, steps and route are unchanged.

LeanSearch returned Internal Server Error; LeanFinder and Loogle plus local source searches
found no direct usable theorem. Blueprint searches found no matching new local uniform bound
or qcqs affine-open comparison. A transient compilation-overlay FileExistsError disappeared
on retry; no tool was edited or bypassed.

## New nodes

`lem-pc-local-uniform-higher-direct-image-bound` records the affine-base/local portion of
Tag 01XJ: one neighbourhood and bound chosen before the module. It is distinct from the
full uniform bound under arbitrary base changes. Its plan uses the existing open induction,
affine vanishing, Mayer-Vietoris, open-resolution restriction and higher-direct-image
presheaf nodes.

`lem-pc-affine-open-higher-direct-image-sections-iso` records the Tag 01XK comparison with
both sides expressed using the original resolution on X. It makes no existence or vanishing
claim. Its plan uses quasi-coherence (clause (1) of finite-support-hi), affine vanishing,
Leray degeneration, open-resolution restriction and the cohomology presheaf identification.
Both nodes record all three search kinds and inherit the item's chapter/unit and blueprint
ancestor. There are no change records because no existing interface changes.


## Second reading by X2

1. **Interfaces — PASS.** Compared every delivered module with the repository. The two
   lower modules are new. The existing theorem signature is byte-for-byte unchanged;
   its five public imports remain unchanged. Its docstring explains the new route.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   No definition, target statement, or other group's module is changed.
2. **Kernel checks — PASS as a decomposition.** All three modules compile in dependency
   order with lcompile.py. A scratch module's `#print axioms` for all three declarations
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The only two
   syntactic sorries are the two reported named lower theorems. No forbidden declaration
   or hollow definition is present. Selection of neighbourhoods and bounds is confined
   to the proposition proof. The upper theorem is not claimed axiom-free.
3. **Lower statements — PASS.** Independently read Stacks Tags 01XJ, 01XK and 071L.
   The local bound follows from affine-base finite-cover induction with bounds chosen
   before both affine base change and coefficient module. Sheafification/stalk detection
   then gives the displayed local zero object. The comparison follows from qcqs
   quasi-coherence and affine vanishing followed by Leray, with open-resolution
   comparisons on both sides. Checked degree zero, empty inverse images and opens,
   the empty base, and the union step at p = max(a,b,c)+1. Neither statement restates
   the upper theorem: the first omits compactness and only bounds a neighbourhood;
   the second has no bound or vanishing conclusion. New LeanFinder searches for
   affine-target derived pushforward cohomology found only scheme-localization facts;
   msearch grep for cohomological dimension/higher-image vanishing found no match.
   Local rg and direct reading confirmed that DirectImage.Sections' comparisons
   assume IsSeparated and its local bound fixes the module before the bound.
   QuasicoherentFiniteCohomologicalDimension assumes a field and affine diagonal;
   FiniteAffineCoverRestrictionBound concerns etale sheaves and separated morphisms.
   None supplies these signatures. The stronger Projective theorem is import-cyclic.
   Neither remaining hole can be closed by a short application of existing results.
4. **Route and pruning — PASS.** Read the finite-subcover argument from the upper
   theorem downwards: finite supremum bounds each member, the cover is top, local
   zero restrictions imply a global zero sheaf, and additive sections plus the
   comparison give exactly the requested vanishing. All removed original proof
   dependencies are accounted for under No longer needed. They remain needed below
   the comparison/local bound; no global module pruning is claimed. The unit record
   has empty realized statement and step lists, and no unit statement, step or route
   is altered. Existing public imports supply signature types and resolution instances;
   new proof imports remain plain imports.
5. **DAG agreement — PASS.** Read all three nodes against their declarations and
   natural-language arguments. New nodes include sources, complete proof steps,
   exact Lean signatures, searches, creation, chapter/unit and blueprint ancestry.
   Their proof_deps equal the unions of step uses. The upper node records precisely
   the two lower applications and elementary finite-cover/zero-object reasoning.
   The comparison uses only the quasi-coherence argument of finite-support-hi;
   its uniform-bound declaration cannot be imported here because of the documented
   cycle. That unresolved clause is part of the lower proof plan, not an assertion
   that the upper Lean proof applies the cyclic theorem.

Second-reader repair: added the missing plain proof import
`Sheaf.Paper.HigherDirectImagePresheaf` to
`AffineOpenHigherDirectImageSectionsIso`, matching its last proof-plan step and node.
No theorem statement or proof body needed repair. Closed one original hole, added two
strictly lower holes: decomposition, net -1; global modules pruned: none.
