## What changed

Proved `AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage_large`
in its original module, with exactly its original signature and visibility.
The large-universe continuity helper combines the existing free-sheaf/derived-sections
and module/abelian-cohomology comparison isomorphisms with the existing large filtered
abelian-cohomology theorem. Negative degrees follow from t-structure orthogonality.
Inverse image preserves colimits by its module-valued adjunction.

The final argument restricts the raw presheaf to the affine étale site. Pointwise
continuity and the dense-subsite sheafification compatibility give preservation for
its sheafification. The canonical raw-to-higher-image comparison is naturally an
isomorphism after sheafification; coefficient forgetting reflects colimits.
This replaces the planned local-section injectivity/surjectivity chase with proved
Mathlib infrastructure, without bypassing any realized statement or step of the unit
`sk-lem-universal-datum` (its realized lists are empty). All private helpers are proved.
The node's proof, proof dependencies and proof origin now describe this argument.

Added a proof import of the source `HigherDirectImage.FilteredColimit` module and
uses its existing `Etale.compactSpace_and_quasiSeparatedSpace_pullback` theorem for
the qcqs pullback fact. The former private duplicate helper `compact_pullback` was
removed. Dense-subsite sheaf equivalence and zero-functor preservation are
available transitively; the second reader removed their redundant direct imports.
The current second reading additionally removed the redundant direct proof imports of
`HigherDirectImage.FreeSheaf` and `Mathlib.AlgebraicGeometry.Sites.AffineEtale`,
both publicly imported by `HigherDirectImage.FilteredColimit`.
Existing public imports are unchanged. No other module is adapted, and no new
declaration is exposed.

The mathematical sources are [Stacks 0739](https://stacks.math.columbia.edu/tag/0739)
for filtered cohomology continuity, [Stacks 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
for the higher-image cohomology presheaf, and the fixed-scheme case of
[Stacks 09Z1](https://stacks.math.columbia.edu/tag/09Z1).
The signature keeps schemes in universe u and coefficients and the filtered category
in universe u+1; it never replaces the category with Type 0. The zero ring, empty
schemes, q=0, q<0 and singleton filtered categories require no extra assumption.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage_large`
(node `lem-sbc-higher-direct-image-large-filtered-colimit`).
Added 0 holes. No sorry remains in the delivered module, and no new modules or nodes
are added. The proof uses the existing dependency declarations; it does not claim to
close all transitively reachable sorries below them.

## No longer needed

Removed the import `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits` and the dependency
node `lem-weil-pbc-inverse-image-preserves-colimits` from this proof. Its abelian-valued
statement is unnecessary: the module-valued inverse-image adjunction directly supplies
colimit preservation.

Removed `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` from this node's
proof dependencies. The final proof does not use exactness of sheaf colimits or the
filtered-colimit representative/equality lemmas; pointwise preservation, sheafification
and dense-site equivalence suffice. Its generic Mathlib infrastructure may of course
remain imported transitively elsewhere.

The source `HigherDirectImage.FilteredColimit` module is now imported privately so
the existing `Etale.compactSpace_and_quasiSeparatedSpace_pullback` theorem is reused.
The duplicate private `compact_pullback` helper is therefore pruned. The source
module's other declarations are not re-proved here. No claim is made that removed
dependencies are unreachable from all other targets; the maintainer's closure ledger
determines that.

The second reader also removed redundant direct proof imports of
`Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero`. Both APIs remain available
transitively; these removals prune import edges, not globally unreachable modules.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface repair is needed. The source-library higher-image
filtered-colimit theorem only handles Type 0 indexing, so it cannot itself prove this
coefficient-universe statement. The original DAG's section chase is valid but is
unnecessary: Mathlib already supplies the dense-subsite sheafification compatibility
and reflection through the affine-site equivalence. The final node records that route.

Compilation requires explicit universe choices for affine-site sheafification and
limits, because the affine-site object universe and coefficient universe differ from
the standard affine-site instance's parameters. The implementation supplies these
instances explicitly; it changes no definitions or global instances.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module and node against their repository versions with
   `diff`. The sole existing theorem signature is byte for byte unchanged, as are
   both public imports, the universe, namespace and visibility. All three added
   helpers are private proved propositions. No definition or existing statement is
   changed, and no change record or forced adaptation is needed. Verdict: pass.
2. Compiled the delivered file locally through `lcompile.py` without errors or
   warnings. A scratch copy checked `#print axioms` for the main theorem and all
   three helpers: `compact_pullback` uses only `propext`, `Classical.choice` and
   `Quot.sound`; the other three also use `sorryAx` from existing dependencies.
   No delivered declaration contains `sorry`, an axiom declaration, `unsafe`,
   `opaque`, `implemented_by` or `extern`; no data definition is added. Choices of
   comparison isomorphisms occur only inside a proof of a proposition and define
   no library data. Verdict: pass, with existing downstream holes still open.
3. No statement is split off and no new hole or node is added. Read the continuity
   and comparison declarations used by the proof. The qcqs hypothesis is supplied
   only on affine pullbacks by base-change permanence. Negative degrees are handled
   by t-structure orthogonality; degree zero, zero coefficients, empty schemes and
   singleton filtered categories require no stronger assumption. Verdict: pass.
4. Searched both Lean roots for higher-image colimit preservation and independently
   searched Loogle for preservation and higherDirectImage (zero matches). The
   upstream preservation theorem is indexed by `J : Type`, so it cannot replace
   this theorem for `J : Type (u + 1)`. Read the affine-site equivalence and canonical
   sheafified comparison APIs: the proof uses pointwise preservation and transports
   it through genuine natural isomorphisms, then reflects it through equivalences
   and coefficient forgetting. The unit `sk-lem-universal-datum` has no realized
   statement nodes or step nodes to bypass. Every old dependency absent from the
   new `proof_deps` is listed in `## No longer needed`; the cohomology-presheaf node
   remains used transitively. Verdict: pass after import pruning.
5. Compared the node diff: only `proof`, `proof_deps` and `proof_origin` change.
   The four recorded steps follow the actual continuity, affine-evaluation,
   dense-subsite sheafification and canonical comparison argument; their `uses`
   union equals `proof_deps`. The node statement and Lean record remain unchanged.
   The qcqs dependency is an existing Mathlib leaf. Verdict: pass.

Changed the proof import set to include the source theorem module and removed the
duplicate helper; this report records the repair.
A scratch copy without both imports compiled successfully (41.9 seconds); the
axiom-checking copy without the zero-functor import also compiled (42.0 seconds).
The delivered proof closes the one original hole and adds zero holes; it does not
claim the transitively dependent theorem is yet free of `sorryAx`.


## Second reading by H2

1. Compared the entire delivered Lean module with the repository using `diff` and
   verified the existing theorem signature byte for byte with a Python assertion.
   The ring and filtered category remain in Type(u+1), schemes in universe u,
   q in Z, with the same qcqs assumptions and conclusion. Public imports and
   visibility are unchanged. There are exactly two new private proved theorem
   helpers, no data definitions, new public statements or change records. Pass.
2. Compiled the submitted proof through lcompile.py (50.1 seconds), then compiled
   a scratch copy of the final pruned proof with `#print axioms` for both helpers
   and the main theorem (48.9 seconds). All three use only propext, Classical.choice,
   Quot.sound and sorryAx from existing dependencies. No sorry or prohibited
   declaration occurs in the delivered file. The choices of comparison isomorphisms
   are local to proposition proofs and define no library data. Pass.
3. No statement is split off: one existing hole closed, zero added. Read the large
   filtered-cohomology theorem, both comparison isomorphisms, the shifted-Hom
   pullback isomorphism, the qcqs pullback lemma, and the sheafified comparison
   theorem with their hypotheses. Compactness and quasi-separatedness are needed
   only on the affine pullback; the terminal free-sheaf comparison needs neither.
   The negative-degree branch uses t-structure orthogonality with 0 < -q.
   Zero coefficients, empty schemes, q=0 and singleton filtered categories impose
   no extra conditions. Pass.
4. Independently searched both Lean roots for higherDirectImage/colimit and
   shiftedHom/large, and ran msearch Loogle for higherDirectImage and
   PreservesColimitsOfShape (zero hits). The upstream higher-image result accepts
   J : Type, so cannot replace this coefficient-size theorem. Checked the affine
   dense-subsite instances and Mathlib's sheafification compatibility API: the
   proof transports actual natural isomorphisms and reflects colimits through
   an equivalence and coefficient forgetting. The unit's realized statement and
   step lists are empty. Both removed old proof dependencies are reported above.
   Removed two further redundant direct proof imports, FreeSheaf and AffineEtale,
   because FilteredColimit publicly imports both. The pruned proof compiled in
   the axiom-checking scratch copy. Pass.
5. Compared the node JSON files: only proof, proof_deps and proof_origin differ.
   Asserted that the union of step uses equals proof_deps. The four steps describe
   the actual continuity, affine pullback, dense-site sheafification and canonical
   natural comparison argument. Step 3 uses existing Mathlib infrastructure;
   it does not introduce a new unproved mathematical assertion. The old statement,
   source, unit and Lean record are unchanged. Pass.

Changes in this reading: removed the redundant direct proof imports of
HigherDirectImage.FreeSheaf and Mathlib.AlgebraicGeometry.Sites.AffineEtale;
updated this report. No mathematical proof or statement repair was necessary.
