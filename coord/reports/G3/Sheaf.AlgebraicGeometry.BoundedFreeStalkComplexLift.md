## What changed

Completed the proof of `AlgebraicGeometry.Scheme.exists_boundedFree_stalk_complex_lift`
in `Sheaf.AlgebraicGeometry.BoundedFreeStalkComplexLift`, preserving its signature and
public imports. The proof establishes that the ranks vanish outside the supplied bounds,
constructs a complex with standard free terms by conjugating the differentials, and
proves the resulting isomorphism of complexes. It applies the new affine-local matrix
lift, constructs the global complex by ordinary direct image, proves its boundedness,
and combines the restriction counit isomorphisms with the local free-term isomorphisms.
A private, completely proved helper shows the restriction counit is invertible on opens.

Added `Sheaf.AlgebraicGeometry.BoundedFreeStalkComplexLocalLift`, containing one remaining
matrix-spreading theorem and a completely proved zero-morphism preservation instance for
ordinary open direct image. Its input has standard free terms and an explicit rank-support
condition; its output is a complex on the slice site over an affine open. This is strictly
the local construction step, rather than a renamed global conclusion: the caller proves
rank support, changes bases, constructs the global object and verifies its properties.
No object-valued definition is obtained by choosing an arbitrary witness from a sorry.
The witnesses to the local existence theorem are eliminated only inside the final proof.

Updated the parent node's proof, proof dependencies and proof origin to match this route.
Both delivered modules compile together, without warnings, using `lcompile.py --all`.
Only the single named theorem in the new module contains `sorry`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_boundedFree_stalk_complex_lift`
(node `lem-sc-bounded-free-stalk-complex-lift`). Its proof body is complete.

Added one hole:
`AlgebraicGeometry.Scheme.exists_boundedFree_stalk_complex_local_lift`
(node `lem-sc-bounded-free-stalk-complex-local-lift`). It remains exactly `:= by sorry`,
with its full finite-matrix construction and source in its docstring. This delivery is
a decomposition: one hole closed, one simpler hole added, net zero holes closed. The
rank-support argument, conjugation of complexes, direct-image zero preservation,
restriction isomorphism and global boundedness are actually proved. The existing
`ModuleCat.finitePresentation_descent_directedColimit` remains unchanged in the library;
it is part of the remaining local theorem's planned dependencies, not a new hole.

## No longer needed

Removed direct proof imports of `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`
and `Sheaf.Algebra.FinitePresentationColimit` from the item. These modules and their nodes
`lem-weil-pbc-localization-colimit-principal-localizations` and
`lem-pc-fp-module-map-descent-affine` are retained as dependencies of the local matrix
construction and imported by its new module. They are not pruned from the transitive
closure. No mathematical node or module is claimed pruned. The earlier undelivered
sandbox module `OpenModuleDirectImage` has been replaced by a private proved helper;
there is no extra public restriction lemma or extra hole for this elementary part.
All existing public imports of the item are retained. In the new local module, the
second reading replaced `Sheaf.AlgebraicGeometry.DerivedCategory` with the narrower
`Mathlib.AlgebraicGeometry.AffineScheme` and `Sheaf.Paper.DerivedHomMayerVietoris`
imports, which provide `IsAffineOpen` and `moduleRings` used by its signature.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had not reduced the item's hole and left an unused public
helper module without a matching node. Its restriction proof was usable after replacing
a proposition-valued `letI` with `let` to satisfy the style linter. It is now a private
helper in the item, used by the complete final proof. The plan's mathematical route is
retained; the two stated algebra descent declarations alone do not expose the affine
scheme/free-sheaf/stalk interface needed to perform the whole matrix lift directly.
That interface is the remaining local theorem. No existing statement or definition
was changed. No forced adaptations are needed.

The source tex files are absent on this machine. Read the official Stacks pages
[0BCD](https://stacks.math.columbia.edu/tag/0BCD),
[0BC7](https://stacks.math.columbia.edu/tag/0BC7), and
[00CR](https://stacks.math.columbia.edu/tag/00CR).
The new theorem expands the finite-matrix part of their spreading argument, without
adding a comparison to a prescribed derived object. The unit record
`dag/units/sk-prop-av-cube.json` has no realized node requiring a different route;
its statement and all its steps are untouched.

Checked the empty interval, zero ranks and empty-scheme cases: rank support forces every
term to be zero for an empty interval; a zero rank adds no entries or equations; an empty
scheme supplies no point x. The direct-image argument uses neither quasi-compactness
nor extension by zero. The local theorem can use the stalk of ordinary direct image
because neighbourhoods inside U are cofinal at x. Lean checks the original theorem's
bound and rank-support proof for arbitrary integers a,b, including b<a.

Searches: LeanFinder returned eight unrelated affine/stalk facts; Loogle returned no
cochain-complex/stalk match; grep found stalkwise exactness, not complex lifting.
LeanSearch returned Internal Server Error and is recorded as unavailable. Searched the
source and statement libraries as well as the imported blueprint; the blueprint search
for "bounded free stalk complex" returned zero matches. The adjacent finite-free
chain-map lifting results start with existing complexes and do not construct this one.

## New nodes

`lem-sc-bounded-free-stalk-complex-local-lift` records the local finite-matrix construction
for a complex with standard free stalk terms and ranks zero outside specified bounds.
Its new module is `lean/Sheaf/AlgebraicGeometry/BoundedFreeStalkComplexLocalLift.lean`.
The statement, docstring, three-step DAG plan, source and logged searches agree. It
inherits the parent's chapter, unit and blueprint ancestry. No change record is needed:
existing signatures, definitions, instances and public-import visibility are unchanged.


## Second reading by G3

1. Compared the delivered item against the repository with `diff`, and checked its
   original theorem signature byte for byte. Pass: no existing signature, definition,
   docstring or public import changed. The only added public declarations are the
   local theorem and its proved direct-image zero-preservation instance. No change
   record or forced adaptation is required.
2. Compiled both modules in dependency order with `lcompile.py --all`, without errors
   or warnings. Inspected every proof and scanned for forbidden declarations: one
   named theorem has the whole proof `by sorry`; there are no data definitions with
   holes and no chosen arbitrary witnesses stored as definitions. A scratch axiom
   check shows only propext, Classical.choice, Quot.sound and sorryAx for the two
   existence theorems, and only the three permitted axioms for the zero-preservation
   instance. The delivery tool also probes every generated constant.
3. Read the local theorem, its full docstring construction and node against Stacks
   [0BCD](https://stacks.math.columbia.edu/tag/0BCD),
   [0BC7](https://stacks.math.columbia.edu/tag/0BC7) and
   [00CR](https://stacks.math.columbia.edu/tag/00CR). Pass: finitely many coefficients
   and consecutive-composition equations spread after a finite shrinking. Checked
   zero ranks, empty/reversed bounds, a single supported degree and the absence of
   points on an empty scheme. The ambient stalk of ordinary direct image agrees
   with the local stalk since neighbourhoods inside U are cofinal. Independent
   LeanFinder search for matrices satisfying polynomial relations gave eight
   unrelated presentation lemmas; Loogle for stalk and free gave three rank/free-locus
   facts. Source grep and reading the adjacent chain-map lifting module confirmed
   that those results require already constructed complexes and do not construct L.
   The remaining theorem is strictly the affine-local construction step; the item
   actually proves normalization and globalization. It is a decomposition, net zero.
4. Checked the argument from the original theorem downward. Pass: the proved
   rank-support argument and conjugated complex feed the local construction; the
   proved restriction counit and zero preservation then globalize it. The local
   matrix construction cannot be closed by the adjacent chain-map theorems in a
   few minutes. The report lists both old algebra dependencies removed from the
   parent's direct proof; they remain planned dependencies of the local theorem,
   so no transitive module is claimed pruned. The unit's realized fields are empty;
   its statement and steps are untouched. Narrowed the new module's derived-category
   import to AffineScheme and DerivedHomMayerVietoris, both needed by its signature.
   PushforwardContinuous is a public import because pushforward and pushforwardOver
   occur in the new public signatures; the two algebra descent imports remain plain
   proof imports. Existing public imports are preserved.
5. Compared both nodes with their Lean statements verbatim and checked each step's
   uses against proof_deps. Pass: the parent records the actual rank support,
   conjugation, local lift and direct-image route; the new node records exactly the
   remaining finite-matrix step, with source, searches, ancestry, creation and Lean
   records. No existing non-owned node field is changed.

Changes by the second reader: narrowed imports of the new local module and expanded
this report. No mathematical statement or proof body was changed.
