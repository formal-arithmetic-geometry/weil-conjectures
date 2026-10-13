## What changed

Replaced the sorry in `AlgebraicGeometry.standardSingleFlatCounitUnionTriangles`
without changing its signature or any existing definition. The proof separates
three arguments: restriction and invertibility of the local comparisons,
a short exact geometric comparison, and transport of the associated triangles.

The private, proved restriction helpers identify literal tensor pullback with
ordinary open restriction by uniqueness of left adjoints. Relative flatness is
checked on affine images, using the compatibility of `appLE` and `appIso`, then
transferred across the module isomorphism. Quasi-coherence transfers across the
same isomorphism. Each supplied flat presentation gives a bounded-above flat
complex; the existing K-flat and pinned-counit theorems prove invertibility of
its canonical comparison.

Added `Sheaf.AlgebraicGeometry.StandardSingleUnionSESPresentation`, which isolates
the construction of the short exact cover comparison. It assumes neither the
three flat presentations nor flatness, quasi-coherence, compactness or
invertibility. Its output is two short exact complexes, a strict morphism, six
localized vertex identifications and three component identities. It does not
assert distinguished triangles or a connecting-square identity.

A proved generic private helper conjugates Mathlib's `triangleOfSES` and
`triangleOfSES.map`. It constructs the six differentials, proves the two
triangles distinguished and establishes the exact three components. In
particular the third square follows from short-exact boundary naturality,
not from the first two squares. The item's proof combines this with the three
local isomorphism proofs.

Proof imports added: `IsomorphismPullbackCounit`,
`BoundedAboveFlatRingedSpaceKFlat`, and `StandardSingleUnionSESPresentation`.
The existing node's proof route now records this assembly. The generic transport
helper and explicit vertex arguments keep elaboration from unfolding the large
tensor and derived-category models. No declaration attributes change.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.standardSingleFlatCounitUnionTriangles`
(`new-pc-standard-single-flat-counit-union-triangles`).

Added one named hole:
`AlgebraicGeometry.standardSingle_union_ses_presentation`
(`new-pc-standard-single-union-ses-presentation`), in its own module.
This is the short exact geometric comparison from steps 2–3 of the original
plan. It is a strict part of the argument: the restriction, K-flat counit,
distinguishedness, transport and boundary-square assembly are proved in the
item, rather than assumed in this new statement.

This delivery is a decomposition, with one hole closed and one added, hence
net zero holes before any change in the targets' import closure. It does not
claim a completed geometric proof. There are no sorries in private helpers or
definitions, and no other new holes. Existing imported theorem holes remain
with their existing nodes.

Edge cases checked against the new construction: if either open is empty its
term vanishes; repeated or contained opens give the split restriction sequence;
zero modules give zero complexes. Arbitrary base changes are permitted: only
pullback along the source-open inclusions is used as exact restriction.
Existential witnesses of the new theorem define no library data.

## No longer needed

The following old `proof_deps` are no longer direct dependencies of the item's
proved assembly; each is retained as a dependency of the new geometric
presentation node, so this is dependency relocation, not module pruning:

- `prop-pur-kinjective-resolutions-exist`;
- `lem-pc-kinjective-mayer-vietoris-presentation`;
- `lem-pc-derived-direct-image-composition`;
- `def-pc-derived-pullback`;
- `lem-pc-mayer-vietoris-underived-open-counit-square`.

No original import was removed. The trial proof import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` was not retained;
the required restriction and quasi-coherence API is already available. No original dependency module is claimed to
leave the targets' closure. The geometric K-injective, direct-image composition,
derived-pullback and underived-open-counit dependencies now belong to the new
short exact comparison node; they remain mathematically needed there.

The compact-open theorem `singleComplexOpenComparison_union_triangles` and its
module `Sheaf.AlgebraicGeometry.SingleComplexOpenUnionTriangles` were considered
and are not imported: the item's opens are arbitrary. Its short exact
presentation also assumes compact opens and is not used. The generic cylinder lemma is recorded as a tool use, without using its
scheme-specific semicon parent. No unit-level step is bypassed; the unit's `realized` record is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The existing geometric proof plan omits the
chain-level compatibility and transport glue needed to use the available
K-injective presentation with these literal vertices. The new node records that
remaining construction explicitly. The existing compact-open comparison cannot
be applied without adding hypotheses, so it was not substituted.

LeanSearch returned Internal Server Error. LeanFinder, Loogle and local searches
completed. The Stacks source pages 08BV, 08FE, 08HY, 0DJ9, 013N and 013O were read.

## New nodes

`new-pc-standard-single-union-ses-presentation` states the unrestricted
short exact complex comparison, sourced to Stacks Tags 08BV, 08FE, 08HY and
0DJ9, with the mapping-cylinder construction of 013N–013O. The node includes
the full Lean signature and a three-step proof plan using existing resolution,
Mayer–Vietoris, underived-counit and generic cylinder nodes. The theorem's
own docstring gives the construction and its empty/repeated/zero cases.
Mathlib searches found the generic site and short-exact-triangle APIs but no
geometric theorem with this unrestricted signature. No change record is needed:
no existing statement or definition changed and no other module was adapted.

## Second reading by Q4

1. **Interfaces: PASS.** Diffed both delivered paths against the repository.
   `StandardSingleUnionSESPresentation` is new; the existing item's only edits
   are three plain proof imports, five private proved helpers, elaboration
   options, and replacement of its proof. Extracted the existing theorem header
   through its conclusion and verified byte-for-byte equality. In particular
   qcqs `p`, affine `B,A`, arbitrary `g,U,V`, quasi-coherent `N`, relative flatness
   `hN`, and all three supplied presentation hypotheses remain unchanged. The
   literal tensor restrictions, six triangle vertices, three exact components
   and three local `IsIso` conclusions also remain unchanged. No existing
   definition, attribute or visibility changed; no change record is required.

2. **Proof and axioms: PASS as a decomposition.** Compiled both modules in import
   order through `lcompile.py`: 6.2 s and 10.9 s, without errors or warnings.
   Scratch copies with `#print axioms` compiled too. All five private helpers
   use only `propext`, `Classical.choice`, `Quot.sound`. The main theorem and
   `standardSingle_union_ses_presentation` additionally use `sorryAx`, exactly
   accounting for the latter's single named hole. The item contains zero
   `sorry` tokens; the new module contains one, at that public theorem. There
   are no definitions or forbidden escape declarations in the delivered files.
   The restriction proof checks affine images and the scalar-action equality;
   the presentation proof uses bounded-flat K-flatness and the pinned counit;
   the transport proof conjugates `triangleOfSES.map`, so its connecting square
   is established by boundary naturality rather than inferred from two squares.

3. **New statement: PASS.** Read its full signature, node, natural-language proof
   and the relevant existing presentation/cylinder modules. Its hypotheses are
   arbitrary `p,g,U,V,N`, without flatness, quasi-coherence or compactness. Its
   conclusion is precisely two short exact complex rows, a strict row morphism,
   six vertex identifications and three localized component equations. These
   provide the geometric part used once by the main proof, leaving restriction,
   K-flat invertibility and triangle transport genuinely proved outside the hole.
   It neither restates the flat target nor assumes its distinguishedness or local
   invertibility. On empty opens the corresponding term is zero; on repeated
   opens the row is diagonal/difference; on contained opens one restriction is
   identity and the row splits; zero coefficients give zero rows. Arbitrary base
   change does not require tensoring an arbitrary exact row underived: the source
   row is sent through derived pullback, and only open restriction is used as an
   exact underived functor. The witnesses construct no library definition.
   Read [08BV](https://stacks.math.columbia.edu/tag/08BV),
   [08HY](https://stacks.math.columbia.edu/tag/08HY),
   [0DJ9](https://stacks.math.columbia.edu/tag/0DJ9) and
   [013N](https://stacks.math.columbia.edu/tag/013N) against this construction.
   Independent LeanFinder search used natural transformations and sheaf gluing;
   Loogle checked `DerivedCategory.triangleOfSES.map`; launcher grep and local
   searches checked homotopy squares, cone presentations and open-union results.
   They found generic APIs and existing compact-open results, not this unrestricted
   geometric presentation. Closing this hole requires substantial geometric
   compatibility work, not a few-minute application of an existing declaration.

4. **Route and pruning: PASS after report repair.** Read the original proof plan,
   all old dependency names, the compact-open comparison, the arbitrary-open
   K-injective presentation, and the unit's `realized` record. The three flat
   local arguments and the geometric cover-comparison route are retained.
   `realized` is unchanged (its recorded statement/step lists are empty); no
   recorded unit realization is bypassed. Every direct import serves a public
   signature or proof; all newly added imports of the item are plain `import`.
   No original import or module is pruned. The five old dependencies relocated
   to the new node are now explicitly enumerated under `No longer needed`.

5. **DAG agreement: PASS.** JSON comparison shows the existing node changes only
   `proof`, `proof_deps`, `proof_origin`. Its three new proof steps match the
   restriction/K-flat argument, SES transport and triangle-map conjugation.
   The new node has its source, self-contained statement and statement
   dependencies, three-step proof and matching dependency union, search records,
   split status, worker/item/group/date, blueprint ancestry, chapter/unit,
   audit fields and full verbatim Lean signature. Its extra cylinder `tool_uses`
   entry names the generic construction, without bypassing a scheme unit.
   Both node signatures match their Lean declarations.

Changed in this second reading: completed the explicit relocated-dependency list
under `No longer needed` and added this review. No Lean proof, signature, import
or node was changed. The hole accounting remains one closed, one added, net zero:
this is a reviewed decomposition, not a completed proof of the geometric diagram.
