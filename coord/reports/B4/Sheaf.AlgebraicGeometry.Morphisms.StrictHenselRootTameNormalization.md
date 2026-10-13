## What changed

Repair of the returned landing: removed the duplicate private
`AlgebraicGeometry.Scheme.root_pow` from the new finiteness module. Both uses now
specialize the existing Mathlib theorem `AdjoinRoot.eval₂_root` locally. The
same-named theorem in `StrictHenselRootPurityData` is private, and that module
imports this item, so importing it here would create a cycle. No existing module,
public signature, import, or hole count changes in this repair. The delivery tool
rebases the repaired sandbox on the freshly fetched `sheaf-dag` for its dry run.

Proved `AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_tame_normalization`
with its original signature and docstring unchanged. The proof explicitly constructs
`a.normalization`, where `a` is the punctured pullback projection followed by the open
inclusion. It uses no existence theorem to choose normalization data.

The private pullback argument `finite_etale_over_basicOpen` proves that the punctured
projection is finite and etale from the supplied beta and projection equation.
The private `normalization_restrict_iso` constructs its restriction isomorphism using
Mathlib's smooth normalization base change and the integral-morphism normalization
isomorphism. Its projection identity is proved, and etaleness over the puncture follows
by composition with this isomorphism.

Added two proof-only imports and their modules:

- `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite`: proved
  finiteness of the explicit relative normalization from existing named declarations.
  The proof constructs the root quotient equivalence, proves that the root algebra
  is local, applies regularity at the root to its maximal ideal, and obtains normality.
  The existing finite-etale-open integral-closure theorem then proves finiteness on
  affine charts. No new hole remains in this module.
- `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale`: the
  remaining Abhyankar argument, for the same explicit normalization and with its
  finiteness as an input. Its sole conclusion is an etale neighborhood of the supplied
  divisor generic point. It asserts neither finiteness nor a cover identification.

Updated the item's DAG proof and added matching nodes for both modules. The unit's
root-extension and generic-ramification argument remains; only the finiteness
subargument uses the existing generic integral-closure tool.

All three modules compile together, without compiler warnings, through `lcompile.py`.
The proof is a reduction from named statements, not an axiom-free completion of the
transitive dependency closure.

## Proved and sorry left

Closed the item's only local hole:
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_tame_normalization`
(node `lem-sbc-strict-hensel-root-tame-normalization`). The item contains no `sorry`.

Added and proved, from existing library lemmas:
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_finite`
(node `lem-sbc-strict-hensel-root-normalization-finite`). This module contains no `sorry`,
including its private helpers.

The delivery adds exactly one hole:
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_generic_etale`
(node `lem-sbc-strict-hensel-root-normalization-generic-etale`). Its proof is exactly
`:= by sorry`; its docstring gives the source and the complete ramification/open-locus
argument. This is a decomposition: one upper hole closed and one strictly smaller hole
added. Existing imported holes are untouched, including strict-hensel quotient
regularity and the finite-etale generic-algebra input to the integral-closure theorem.
No claim of positive net hole reduction is made.

Edge cases: the group order is positive since G is a group. The nonunit image g
excludes a zero strict-hensel ring and an empty divisor quotient. The root quotient
maps are constructed and checked on coefficients and the root. The finiteness tool
allows the empty punctured cover; no nonemptiness is added for it. The remaining
etaleness statement concerns the canonical normalization, not an arbitrary finite
model, and assumes its finiteness explicitly.

## No longer needed

Removed the duplicate private `root_pow` helper; its argument is supplied by
Mathlib's polynomial root evaluation theorem. No additional module is needed.

No import was removed from the item's module, and no node or module is claimed pruned.
The old direct proof dependencies
`lem-sbc-strict-hensel-regular-divisor-quotient`,
`lem-sbc-affine-strict-henselization-structural-flat`, and
`lem-sbc-root-algebra-regular-at-root` are now used inside the lower finiteness and
ramification statements, so moving them out of the direct proof is not pruning.
Every other old dependency remains a direct dependency of the item.

The new finiteness module needs neither the EffectiveCartier nor the scheme-Regular
public import copied in its initial scaffold; both were removed before its final
compile. The group-order unit and beta projection equation are not needed for this
finiteness subargument (their binders are named `_hG` and `_hβ`); both remain necessary
for the original theorem's generic-etaleness argument.

## Where the brief, the DAG or earlier work was wrong

The item's original DAG lists regularity and definition nodes, but its remaining
ramification and tame-normalization steps do not have Lean declarations that directly
supply their conclusions. Existing regularity lemmas alone cannot finish this item.
The remaining ramification step is now a specific theorem about the constructed
normalization, with finiteness separated as an input.

Finiteness does not need the full tame-normalization theorem once the root spectrum
is shown integral, normal and Noetherian. The existing
`finiteEtale_open_integralClosure_finite` supplies it using separable generic algebras.
The sources read were [0EYG](https://stacks.math.columbia.edu/tag/0EYG),
[0EYH](https://stacks.math.columbia.edu/tag/0EYH),
[09EB](https://stacks.math.columbia.edu/tag/09EB),
[0BRM](https://stacks.math.columbia.edu/tag/0BRM), and
[032L](https://stacks.math.columbia.edu/tag/032L).

The below-unit finiteness proof uses
`lem-weil-pbc-strict-henselization-local-structure`,
`lem-weil-pbc-regular-local-localization`, and
`lem-weil-pbc-regular-ring-normal` as generic tools from the proper-base-change chapter.
They supply only local structure, regular localization and normality, and replace no
step of the spreading unit's route. The maintainer may record these as tool uses;
this delivery does not modify the maintainer's `tool_uses` fields.

An intermediate draft tried to identify an arbitrary finite etale model with the
punctured cover; that is false (the empty model is a counterexample). It was discarded
before the delivered statements were written. Both delivered lower statements refer
to Mathlib's concrete relative normalization.

LeanSearch was attempted for both new nodes and returned an Internal Server Error;
the search records mark it unavailable. Loogle, LeanFinder and source grep ran.

## New nodes

`lem-sbc-strict-hensel-root-normalization-finite` records the proved finiteness
subargument for the explicit normalization. Its proof dependencies follow the actual
Lean imports: strict-hensel local structure and regular quotient, structural flatness,
regularity at the root, regular localization, normality, the finite-etale-open
integral-closure theorem, and Mathlib relative normalization. Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/StrictHenselRootNormalizationFinite.lean`.

`lem-sbc-strict-hensel-root-normalization-generic-etale` records the remaining
ramification/open-neighborhood argument. It assumes finiteness of the explicit
normalization and concludes only its etaleness on an open containing j(eta). Its module
is `lean/Sheaf/AlgebraicGeometry/Morphisms/StrictHenselRootNormalizationGenericEtale.lean`.

No existing definition or statement changed, no adapted module is delivered, and no
change record is required.


## Earlier second reading (a previous round; superseded)

1. Interface preservation: compared the delivered item with the repository using
   `diff -u`, and checked its existing theorem signature byte for byte. It and the
   original docstring are unchanged. The other two modules are new. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`. No definition or
   statement change record, forced adaptation, or target change is needed. PASS.

2. Proof checking: compiled all three modules in import order with `lcompile.py`,
   without errors or warnings (about 7, 4, and 6 seconds respectively). Compiled
   temporary copies with `#print axioms` for each public declaration: all three
   list only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter
   is expected from the reported remaining generic-etaleness hole and existing
   lower holes. The only delivered `sorry` is the named generic-etaleness theorem;
   no forbidden declaration, hidden hole, or hollow definition occurs. Read the
   quotient equivalence, pullback inverse, normalization restriction isomorphism,
   and its projection identity. They construct data explicitly. PASS as a
   decomposition, not as an axiom-free completion.

3. Remaining statement: read its docstring and node against
   [09EB](https://stacks.math.columbia.edu/tag/09EB),
   [0BRM](https://stacks.math.columbia.edu/tag/0BRM), and the root argument of
   [0EYG](https://stacks.math.columbia.edu/tag/0EYG). The height-one base ring at
   (g) is a DVR; the root has ramification index |G|. Each generic torsor component
   is Galois for a subgroup, so its ramification and inseparable residue degrees
   have no residue-characteristic factors. Abhyankar applies to every component.
   Localization of the integral closure identifies the concrete normalization
   with the DVR integral closures, and finite presentation plus finiteness removes
   the image of its closed nonetale locus. This proves precisely the asserted
   neighborhood, without asserting purity or choosing another model. The finite
   statement is separately proved via the existing integral-closure tool; [032L](https://stacks.math.columbia.edu/tag/032L) supports that tool's finiteness input.
   Checked |G|=1, nonunit g, the exclusion of the zero divisor quotient, and a
   split cover: these give the expected trivial or unramified normalization.
   Neither statement requires an extra nonemptiness hypothesis. The generic
   statement is a strict part of the old argument: it supplies no model,
   finiteness proof, or cover isomorphism. PASS.

   Independent searches used LeanFinder for "normalization becomes unramified
   after a Kummer base change along a discrete valuation ring", Loogle for
   `Ideal.ramificationIdx`, and grep for finite separable integral closures.
   These found algebraic ingredients, not an existing generic-etaleness theorem.
   Source searches also found `StrictHenselRootFiniteEtaleModel` and
   `RegularDivisorStrictHenselRootSection`; their import chain goes through
   `StrictHenselRootPurityData` back to this item, so they cannot be used here.
   The root-quotient equivalence in `RootAlgebraRegularAtRoot` is private, so
   it cannot replace the local explicit helper. No hole can be closed by a
   short existing theorem without an import cycle.

4. Top-down route and imports: the proof first establishes the punctured
   projection's properties, constructs the relative normalization, proves its
   finiteness using existing regularity and finite integral-closure tools, and
   isolates only generic ramification. All public imports of the new modules
   support their signatures; imports for proved subarguments are plain imports.
   All three old regularity dependencies moved out of the upper node are named
   under No longer needed and remain used below. No module is claimed pruned.
   Read `dag/units/sk-prop-input-spreading.json`: its `realized` entries are empty
   in the baseline, and this delivery does not change them. The trait's root and
   tame-ramification route remains intact; the shorter finiteness tool is below
   the unit. PASS after the dependency-import repair described below.

5. DAG consistency: checked every new node's chapter, unit, blueprint provenance,
   creation record, searches, and Lean record. Each `lean.statement` occurs
   verbatim in its module, and each `proof_deps` equals the union of its proof
   steps' `uses`. The finiteness node follows the actual local-ring, localization,
   normal-stalk and affine integral-closure proof. The generic-etaleness node
   records the sourced unfinished ramification argument. The upper node records
   the actual constructed normalization and restriction isomorphism. PASS after
   adding its missing torsor dependency.

Second reading changed: added the three plain imports for the generic-etaleness
node's regular-divisor quotient, structural flatness, and root-regularity proof
plan; restored `def-sbc-normal-dominant-galois` to the upper node's first step and
`proof_deps`, since `W.isFinite` and `W.etale` are used; explicitly listed the three
old dependencies moved below; removed two duplicate blank lines in the new finite
module. No proof body, declaration signature, or hole count changed. The result
still closes one original hole and adds one smaller hole: net zero, decomposition.

## Second reading by B4

1. Interface preservation: read all three delivered modules and compared the upper
   module with the repository using diff. The original theorem signature and docstring
   are byte for byte unchanged. The other two modules are new; there are no adapted
   modules or change records. Compared the existing node as JSON: only proof,
   proof_deps and proof_origin differ. PASS.

2. Proof: compiled the three modules in import order with lcompile.py, without errors
   or warnings. Read both quotient maps and their inverse equations, the maximal-ideal
   contraction argument, regularity at the maximal ideal, and the affine integral-closure
   finiteness proof. The root relation now specializes AdjoinRoot.eval₂_root; the returned
   duplicate root_pow is absent. The normalization is Mathlib's explicit construction,
   and the quotient equivalence is built from ring homomorphisms, not an arbitrary
   witness of unproved existence. There is exactly one delivered sorry, the named
   generic-etaleness theorem with its sourced proof docstring and node. No forbidden
   declaration or hollow definition occurs. PASS as a decomposition, with net zero holes.

3. Split statements: read [09EB](https://stacks.math.columbia.edu/tag/09EB),
   [0BRM](https://stacks.math.columbia.edu/tag/0BRM),
   [0EYG](https://stacks.math.columbia.edu/tag/0EYG), and
   [0EYH](https://stacks.math.columbia.edu/tag/0EYH). The generic-etaleness lemma assumes
   finiteness of the fixed normalization and supplies only its neighborhood at j(eta).
   The regular quotient makes (g) a height-one prime; its localization is a DVR.
   The root coordinate is a uniformizer at (t), with g=t^|G|. Stabilizer Galois degrees
   divide |G|, excluding wild and inseparable residue factors, so 0BRM applies.
   Localization of the integral closure gives etaleness above this generic point;
   finite presentation and the closed image of the nonetale locus give O.
   The Cartier centre is reduced and has the same support, hence the same generic
   point. Checked the trivial group, split torsor, empty finite-etale source, nonunit
   equation, and exclusion of a zero quotient: no extra nonemptiness is needed.
   The finite lemma proves a separate proper part of the argument and has no local hole.
   Independent LeanFinder search for a normalization becoming unramified after a
   uniformizer root returned unramified-at and ramification-index ingredients only.
   Loogle search AdjoinRoot.eval₂_root and source rg searches were also run. The first
   Loogle query AdjoinRoot, Ideal.Quotient reported an unknown identifier, not a match.
   Searched Sheaf, WeilConjectures, and the upstream checkout. The root finite-etale
   model and purity-data statements depend back on this item and cannot close this
   hole without a cycle. The private quotient equivalences cannot be imported for use.
   PASS: one strictly smaller unresolved ramification statement, not a relabelled item.

4. Top-down route and pruning: retained the actual punctured projection proof and
   explicit normalization, then finiteness and the generic ramification step. Found
   the existing upstream pullbackFromNormalizationIso and its projection formula in
   ExtendOverInertia and used them instead of the local reimplementation. Its import
   is plain, since only proofs need it. All public imports support public signatures.
   The old three dependencies moved below are explicitly listed under No longer needed;
   no module or node is claimed pruned. The unit sk-prop-input-spreading has empty
   realized entries in the baseline; the delivery leaves them intact and retains its
   root-extension and generic-ramification route. PASS.

5. DAG: checked all node files, the new provenance, creation, search, source, chapter,
   unit and Lean records. Each lean.statement occurs verbatim in its module; each
   proof_deps is exactly the union of the proof steps' uses. The finite proof follows
   the local structure, regular quotient, flatness, root regularity, regular localization,
   normality and finite integral-closure declarations actually applied. Updated the
   upper final step to record the upstream restriction-isomorphism specialization.
   The generic-etaleness node agrees with its sourced remaining hole. PASS.

Second reading changed: replaced the local integral-pullback instance and normalization
base-change reimplementation with upstream pullbackFromNormalizationIso and its projection
formula; added its plain ExtendOverInertia import; updated the matching DAG step and report.
No existing signature, definition, or hole count changed. Proved 1 of 1 original local
holes, added 1 unresolved split statement; net zero, decomposition; pruned no modules.
