## What changed

Proved the existing signature of
`AlgebraicGeometry.Scheme.exists_affine_freeSheaf_stalk_realization` from explicit
standard basis germs, their bijectivity and their matrix action. This is a decomposition,
with two remaining regular-module comparisons; it is not a sorry-free proof.
All work is in the sandbox and no existing definition or signature was changed.

Added five modules. AffineFreeBasisGerms constructs the regular sheaf isomorphism,
the actual unit germ, coordinate inclusions and projections, basis germs, scalar
endomorphisms, and their linear combination maps. Its additivity and basis evaluation
proofs are complete. AffineFreeStalkComparisonBijective proves arbitrary finite-rank
bijectivity using the regular-module comparison, coordinate projections, and the
reconstruction identity. AffineFreeBasisGermMap proves the complete matrix-action
formula using additivity and a single scalar compatibility statement. The original
module builds its isomorphisms from bijectivity and proves equality on a basis.

AffineRegularStalkComparisonBijective and AffineRegularStalkScalar state the two
remaining parts. Both concern only the regular coordinate module, have no arbitrary
matrix or rank parameters, and have explicit constructions as their objects. No
existence theorem supplies arbitrary definition data. LinearEquiv.ofBijective only
inverts a specified bijective linear map, so its inverse is uniquely determined.

Compilation: all six modules compile cleanly in import order with lcompile.py.
Edge cases: rank zero follows from the empty coordinate reconstruction identity;
empty source makes the matrix statement vacuous; empty target gives the empty sum;
empty U admits no x with hxU; neither scalar compatibility nor regular bijectivity
requires quasi-compactness. Scalar zero and one satisfy the intended formulas.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_affine_freeSheaf_stalk_realization`
(node lem-sc-affine-free-sheaf-stalk-realization). There are no sorries left in the
item's module.

Added exactly two holes:

- `AlgebraicGeometry.Scheme.affineRegularStalkComparison_bijective`
  (lem-sc-affine-regular-stalk-comparison-bijective).
- `AlgebraicGeometry.Scheme.affineRegularStalkGerm_scalar`
  (lem-sc-affine-regular-stalk-scalar).

The new statements `affineFreeStalkComparison_bijective` and
`affineFreeBasisGerm_map` are proved from those two smaller statements.
The finite basis algebra, additivity, and original naturality assembly are proved.
Thus this delivery closes one upper hole and adds two strictly smaller holes;
it is a decomposition, not a net decrease in holes.

## No longer needed

The old proof_deps entries absent from the new direct proof_deps are all four of
`lem-weil-pbc-spec-tilde-stalk-localization`, `def-weil-sheaf-of-modules-category`,
`lem-pc-affine-perfect-module-model`, and `def-pc-module-stalk-functor`. The first two
are no longer used directly; the latter two remain dependencies through the explicit
basis-germ construction and supply definitions in the original signature. This does
not assert that their modules leave the targets' import closure.

No original imports removed: the four original public imports supply the existing
statement's objects and preserve its visibility. The proof no longer directly uses
lem-weil-pbc-spec-tilde-stalk-localization or def-weil-sheaf-of-modules-category;
the regular-module bijectivity can be proved using the explicit sheaf isomorphism
and cofinal neighbourhoods, without localizing arbitrary modules.
No tilde-stalk-localization module was added. The original dependencies
lem-pc-affine-perfect-module-model and def-pc-module-stalk-functor remain needed for
its actual functor and definitions; their modules remain public imports.
No blueprint unit step is bypassed (the unit's realized entries are empty, and this
is below its level).

## Where the brief, the DAG or earlier work was wrong

No disputed statement or interface correction. The old proof plan describes the
right mathematics but its localization lemma alone does not expose compatibility
with the explicit chart, overEquiv inverse, and ordinary open direct image. Those
compatibilities are now isolated on the regular module; all finite matrix algebra
and finite-rank assembly are written in Lean.

The literature files are not present in this remote clone; I checked the source tags
at the official Stacks pages: https://stacks.math.columbia.edu/tag/01HV,
https://stacks.math.columbia.edu/tag/01IB,
https://stacks.math.columbia.edu/tag/01C6 and
https://stacks.math.columbia.edu/tag/0098. Tag 0098 is the pullback stalk tensor
formula (used for chart restriction), not by itself the ordinary direct-image
comparison, which needs cofinal neighbourhoods contained in U.

The blueprint ancestor tool reports None for this item; the new nodes inherit the
existing item's explicit ancestor thm-sc-theorem-of-cube and add this item to via.
Blueprint search for basis germ, free stalk comparison and coordinate module found
no matching blueprint node. Searches ran through msearch.py: LeanFinder and Loogle
find tilde localization, and grep finds its pinned implementations. LeanSearch is
unavailable (HTTP Internal Server Error), recorded as unavailable rather than absence.

## New nodes

`def-sc-affine-free-basis-germs`: explicit regular isomorphism, unit germ, coordinate
maps, basis germs and their linear combination maps. Includes proved additivity
and basis evaluation; the source is the item's Tags 01HV, 01IB, 01C6 and 0098.

`lem-sc-affine-regular-stalk-comparison-bijective`: multiplication by the constructed
regular unit germ is bijective. Its proof is the slice-site unit comparison followed
by cofinal neighbourhood stalk comparison. This is one remaining hole.

`lem-sc-affine-regular-stalk-scalar`: sheafified multiplication by a acts on the
constructed unit germ by germ(a). Its proof uses the chart's sections map and the
germ scalar identity. This is the other remaining hole.

`lem-sc-affine-free-stalk-comparison-bijective`: proved finite coordinate comparison;
injectivity and surjectivity reduce to the regular-module comparison using the
coordinate reconstruction identity.

`lem-sc-affine-free-basis-germ-map`: proved matrix-action formula; the coordinate
map is decomposed into scalar endomorphisms and target coordinate inclusions.
All search records come from the executed searches.jsonl; no change records required.

Second-reader import pruning: removed the redundant public import
`Mathlib.LinearAlgebra.Pi` from the new AffineFreeBasisGerms module. Its declarations
are already available through the required public imports. No project module becomes
unreachable as a result of this redundant-import removal.


## Second reading by W2

1. Compared every delivered Lean file with the repository. The five supporting
   modules are new. In the existing module the complete theorem signature and
   docstring are byte-for-byte unchanged; the only additions are two private proved
   helpers, two proof-only imports, and the proof body. No existing definition,
   public visibility, hypothesis or conclusion changed; no change record is needed.
2. Compiled all six modules locally in dependency order. Inspected every definition:
   the regular sheaf isomorphism, unit germ, coordinate maps and comparisons are
   explicit constructions. No arbitrary existence witness supplies data. The only
   inverse chosen is that of a specified bijective map. There are exactly two
   `sorry`s, in the reported named regular-module theorems, and no forbidden
   declarations or options. Appended `#print axioms` in scratch copies for all
   declarations: definitions and elementary proofs use only the standard axioms;
   the upper proofs additionally use `sorryAx` through the two reported holes.
3. Read the two remaining statements with their constructions and complete prose
   proofs. Regular comparison is the pushforward and stalk of the explicit regular
   sheaf isomorphism, combined with cofinal neighbourhoods contained in U. Scalar
   compatibility follows from tilde functoriality, the canonical chart sections
   map and germ_smul. Neither restates the item: they have no finite-rank or matrix
   parameters, and the finite-coordinate assembly is proved. Checked rank zero,
   empty source/target coordinates, the vacuous empty-open case and scalars 0 and 1.
   Renewed Loogle search for pushforward/stalk, LeanFinder search for open-inclusion
   structure-sheaf stalks, and grep for restrictUnitIso, overEquiv unit comparison,
   stalkPushforward_iso_of_isInducing and germ_smul. These provide building blocks,
   not the exact slice-site comparison; no quick replacement closes either hole.
   Checked the cited Stacks tags at their official pages; 0098 concerns pullback,
   so cofinal-neighbourhood reasoning is explicitly supplied for direct image.
4. Read the proof downward: specified basis-germ comparison, bijectivity via
   projections/reconstruction, and matrix action via the scalar formula. This is
   a real reduction, not a renamed application of the original assertion. Removed
   redundant Mathlib.LinearAlgebra.Pi from the new construction module; retained
   original public imports used by its unchanged signature. All old proof_deps
   removed from the direct list are accounted for above, including those retained
   transitively. Read sk-prop-av-cube's realized record: this item is below the unit
   route and no realized statement or step is replaced.
5. Checked all six node records against the declarations and proof steps; all new
   nodes have source, creation, blueprint, search, chapter/unit and Lean records.
   Corrected new lean.statement fields to verbatim signatures, starting at the
   declaration keyword as required by the preflight parser (which excludes the
   noncomputable modifier). Added the explicit construction and proved functor
   additivity steps to the basis-germ definition node, whose proof had been empty.
   The other proof/proof_deps/proof_origin records describe the actual reduction.

Changes by this reader: redundant import removed; verbatim new-node signatures and
basis-germ construction/additivity DAG proof repaired; pruning report clarified.
No proof or statement required repair. Closed one original hole and added two
strictly smaller holes: this remains a decomposition, with net holes +1.
