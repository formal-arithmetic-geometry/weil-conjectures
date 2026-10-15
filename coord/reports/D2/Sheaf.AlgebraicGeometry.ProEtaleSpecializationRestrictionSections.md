## What changed

Repair of the landing return at head `69b26541a`: removed the duplicate private
`AlgebraicGeometry.Scheme.AffineProEt.cover_split` and its proof from
`ProEtaleSpecializationCounit`. A proof-only
`import all Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation`
now makes the existing private helper available, and the counit theorem applies
that existing theorem at the original call site. Lean's module system supports
this import without changing the helper's visibility or its source module.
The counit node now records this existing dependency. No existing library
module beyond the item is adapted; no signatures or definitions change.


The second reading rejected the first worker's pointwise bijectivity split: it
was equivalent to the entire original assertion and left all seven geometric
steps unproved. That new declaration and its unlanded node were removed.

The existing declaration
`AlgebraicGeometry.Scheme.isIso_proEtaleUnit_sections_of_specialization`
keeps its signature and original docstring byte for byte. Its proof now uses
the explicit ring `A = Γ(V.left, ⊤)`, the kernel of the global-sections map of
`pullback.fst V.hom i`, and the identity affine basis object over `Spec A`.
It combines coordinate transport, the proved geometric counit theorem, and
comparison with the actual inverse-image unit.

Added three modules, all under `Sheaf.AlgebraicGeometry`:

- `ProEtaleSpecializationAffineCoordinates`: transports the two hypotheses to
  the canonical affine model; this remains a documented theorem with `sorry`.
- `ProEtaleSpecializationCounit`: proves invertibility of the affine closed-site
  counit using flat generalization lifting, the singleton covering theorem,
  subcanonical Yoneda, weak contractibility and the adjunction Hom equivalence.
- `ProEtaleSpecializationUnitComparison`: identifies the actual unit from an
  invertible affine counit; this remains a documented theorem with `sorry`.

All added imports used only for proofs are plain imports. The canonical ring,
ideal, and basis object are explicit constructions. No definition, witness
selection definition, or public data object is added. The proof can use any
adjunction between the fixed lift and base-change functors; its comparison lemma
quantifies over every such adjunction.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.isIso_proEtaleUnit_sections_of_specialization`.

Also proved
`AlgebraicGeometry.Scheme.AffineProEt.isIso_closedSiteCounit_of_specialization`
(node `new-lem-weil-pbc-specialization-closed-site-counit`). This is the actual
geometric surjectivity, splitting and uniqueness argument, not just categorical
assembly of bijective components.

Added exactly two named holes:

- `AlgebraicGeometry.Scheme.specialization_affine_coordinates`, node
  `new-lem-weil-pbc-specialization-affine-coordinates`.
- `AlgebraicGeometry.Scheme.isIso_proEtaleUnit_sections_of_closedSiteCounit`, node
  `new-lem-weil-pbc-specialization-unit-comparison`.

The rejected unlanded
`AlgebraicGeometry.Scheme.proEtaleUnit_sections_bijective_of_specialization`
is absent. Relative to the repository this delivery closes one existing hole
and adds two. This is a decomposition, with local net -1, not a complete proof
of the item. Axiom inspection of the geometric middle step shows only the
three permitted standard axioms in the currently compiled library. No closure or whole-library
ledger improvement is claimed.

All four delivered modules compile without errors or warnings. Axiom inspection
permits only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the
two reported holes; the counit theorem itself uses only the standard axioms.

## No longer needed

The current second reading also removed two redundant proof imports from
`ProEtaleSpecializationCounit`: `WeilConjectures.AlgebraicGeometry.ProEtale.Replete`
and `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`. Its unchanged proof
compiles without them. Their modules are not claimed globally pruned.

The copied private `cover_split` proof is removed entirely. Its separate Yoneda
and singleton-cover argument is no longer repeated in this delivery; the
existing helper in `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation`
is reused. On the counit node the direct proof dependencies
`lem-galois-yoneda-hom-bijection` and `def-weil-pbc-proetale-covering` are
replaced by `lem-weil-pbc-affine-closed-inverse-image-evaluation`; the existing
helper owns those steps. No further module is claimed to leave the import closure.


The original module's direct proof dependencies are now exactly the three new
nodes and `lem-weil-pbc-affine-closed-site-functor-properties`. Every other old
proof dependency is removed from its direct `proof_deps`:

- `def-weil-closed-immersion`
- `def-weil-pbc-ind-etale-basis`
- `def-weil-pbc-proetale-covering`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-proetale-inverse-image`
- `def-weil-weakly-etale-morphism`
- `lem-pc-fppf-dense-sheaf-equivalence`
- `lem-sc-flat-going-down`
- `lem-weil-pbc-affine-closed-inverse-image-evaluation`
- `lem-weil-pbc-closed-immersion-base-change`
- `lem-weil-pbc-flat-morphism-affine-criterion`
- `lem-weil-pbc-ind-etale-basis`
- `lem-weil-pbc-ind-etale-stability`
- `lem-weil-pbc-proetale-finite-coproduct-evaluation`
- `lem-weil-pbc-proetale-subcanonical`
- `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`
- `lem-weil-pbc-site-sheafification-sections-local`
- `lem-weil-proetale-weakly-etale-localization`

Their uses in the remaining arguments are recorded on the new nodes; this is
redistribution, not a claim that all those nodes are globally pruned. In the
proved counit argument `Flat.generalizingMap` directly replaces the old route
through the affine flatness criterion and ring going-down.

The original module removes these direct proof imports:

- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv`
- `Mathlib.RingTheory.Ideal.GoingDown`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`
- `Mathlib.CategoryTheory.Sites.LocallySurjective`
- `Sheaf.Paper.SiteSheafificationSectionsLocal`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`

The affine closed-site functor-properties import stays in the original module.
Imports needed for the new proofs and their stated plans are retained in their
own modules. No module is asserted to leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The returned counit module copied `cover_split` word for word from
`AffineClosedInverseImageEvaluation`. Its private visibility did not require
copying it: `import all` permits this proof to reuse the original. The repair
removes the duplicate and follows the maintainer's requested existing-theorem route.


The first worker's natural-isomorphism assembly moved the whole problem to an
equivalent statement. Its report called that strictly smaller, incorrectly.
The second reading replaces that split with separate affine hypothesis transport
and actual-unit comparison, and proves the intervening geometric counit result.
The original node's seven-step route is retained below the unit level. No target
statement or definition changes, no change record or forced adaptation is needed.

## New nodes

`new-lem-weil-pbc-specialization-affine-coordinates` records only hypothesis
transport to the explicit affine ring, kernel ideal and identity basis object.
Its conclusion does not assert the target isomorphism.

`new-lem-weil-pbc-specialization-closed-site-counit` records the proved geometric
steps 2 and 3. The code uses the adjunction to supply the omitted uniqueness.

`new-lem-weil-pbc-specialization-unit-comparison` records the sheaf calculation,
including weak contractibility of the closed identity object and identification
of the actual unit. It assumes the counit is already invertible and has no
specialization hypothesis. It does not contain the geometric counit argument.

## Earlier second reading (a previous round; superseded)

1. Compared the entire original item module against the repository using diff
   and checked its existing declaration's raw signature. Verdict: unchanged.
   Restored its original declaration docstring, which the first worker had
   changed into an ordinary comment. No existing definition or statement changes.
2. Compiled all four final modules in dependency order through lcompile.py.
   Inspected all delivered source for forbidden declarations and definitions
   containing holes. Checked axioms and the delivery tool's complete probe.
   Verdict: valid conditional proofs, with exactly the two named holes above.
3. Rejected and removed the equivalent pointwise restatement. Independently
   searched LeanFinder, Loogle, Mathlib grep and the library for the replacement
   statements. LeanSearch was also attempted and returned Internal Server Error;
   this is recorded as unavailable, not as a no-match verdict. Existing affine-basis restriction and inverse-image evaluation
   supply infrastructure, but not these actual transport/unit statements.
   Checked the zero ring, empty object and empty finite covering: no extra
   nonemptiness assumption is needed. Verdict: the two remaining statements are
   true, needed, strictly separate parts of the original argument, each with
   a source, a full natural-language proof and its own module/node.
4. Reviewed from the item downward. Used Flat.generalizingMap directly and the
   upstream singleton-cover theorem; preserved the affine closed-site route.
   Removed unused direct imports and recorded every removed old proof dependency.
   Read dag/units/sk-thm-properbasechange.json: this item is not a unit realization;
   none of the unit's statement or realized steps is bypassed. Verdict: route kept.
5. Compared each new node's Lean statement with its actual theorem, and the
   parent's proof/proof_deps/proof_origin with its three-stage code. Checked
   new-node sources, searches, creation records, chapter and unit. Verdict: agree.

Changed after the first reading: removed the equivalent split, restored the
original docstring, proved the geometric counit lemma, split the two remaining
transport/comparison tasks, and replaced the nodes, imports and report accordingly.


## Second reading by D2

1. Compared each delivered file with the read-only repository. The three helper
   modules are new. The existing item's original theorem signature and docstring
   are byte-for-byte identical, and its public imports are unchanged. No other
   existing module, definition or statement is altered. Verdict: pass.
2. Compiled all four modules in import order with lcompile.py. Scanned the complete
   delivered sources: exactly the two named theorem holes reported above, no
   definitions containing holes, and no forbidden declarations. Explicit
   `#print axioms` checks show only propext, Classical.choice and Quot.sound for
   the counit; the original theorem and the two open helpers additionally use
   sorryAx. Verdict: valid decomposition, not a completed proof or net hole gain.
3. Read both open helpers and their complete informal proofs, then independently
   searched LeanFinder for projectivity in slice topoi, Loogle for continuous
   sheaf-pushforward unit formulas, Mathlib Sites via msearch grep, and the
   repository Lean sources. The results give generic projectivity and adjunction
   infrastructure, not either helper. Neither hole is a renamed restatement:
   coordinate transport concludes only the two affine hypotheses; unit comparison
   assumes the geometric counit conclusion and has no specialization assumption.
   Checked empty schemes, the zero ring, I = top, I = bottom and empty finite
   covers. In the nonempty I = top case an invertible counit cannot hold; no false
   conclusion follows. Verdict: true, needed, strictly separate pieces.
4. Read the argument from the original theorem downward. The geometric proof
   uses Flat.generalizingMap and the existing private cover_split helper via
   import all; no duplicate of that helper remains. Reviewed the existing affine
   inverse-image evaluation and the fixed lift/base-change definitions. Verified
   the source arguments in [Stacks 09AC](https://stacks.math.columbia.edu/tag/09AC),
   [09BK](https://stacks.math.columbia.edu/tag/09BK) and
   [09BL](https://stacks.math.columbia.edu/tag/09BL), and localization in
   [03CF](https://stacks.math.columbia.edu/tag/03CF). The two remaining transports
   require substantial formal infrastructure and do not close in a few minutes.
   Checked every old proof dependency removed from the parent against the
   report's No longer needed list. Read the unit's realized table: this node is
   not a unit realization and no required unit step is bypassed. Verdict: pass.
5. Compared each new node's recorded Lean signature verbatim with its source;
   the existing node's signature agrees after whitespace normalization. Checked
   that proof_deps is the union of the proof steps' uses in every delivered node,
   and that the parent proof and counit proof describe the code. All new nodes
   have their source, searches, creation record, blueprint origin, chapter, unit
   and Lean record. Only proof, proof_deps and proof_origin change on the existing
   node. Verdict: agree.

Changed in this reading: removed the two redundant counit proof imports listed
above and recorded this independent review. The existing-helper repair, the
proved geometric argument and both remaining named holes are retained. Holes
closed: isIso_proEtaleUnit_sections_of_specialization (one original hole).
Holes added: specialization_affine_coordinates and
isIso_proEtaleUnit_sections_of_closedSiteCounit (two). This remains a decomposition
with local net -1; no module is claimed to leave the targets' import closure.
