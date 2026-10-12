## What changed

Proved `AlgebraicGeometry.Scheme.zeroDimensional_sections_stalks` without changing its
statement. The proof constructs singleton open pieces, applies the existing disjoint-cover
sections theorem, identifies the local germs with isomorphisms, and factors the global germ
map into the resulting two isomorphisms. Naturality is proved componentwise using Mathlib's
`toPresheafFiber_naturality`.

Added two proved public helpers in new modules:
`ZeroDimensionalSingletonNeighbourhoods` constructs the strictly henselian singleton pieces,
and `AbelianStrictlyHenselianOpenGerm` derives the abelian germ comparison from the existing
set-valued theorem by preservation of filtered colimits and reflection of isomorphisms.
The latter is applied at universe `{u, (max u v) + 1}`; the filtered-colimit preservation
instance is explicitly shrunk to the neighbourhood category's universe.

Added proof-only imports to the original module. Its public imports and existing declaration
signature are unchanged. The parent DAG proof and dependency list follow the compiled proof.
The fixed unit `sk-thm-p1` and its realized statements and steps are preserved.

## Proved and sorry left

Proved the module's sole original sorry:
`AlgebraicGeometry.Scheme.zeroDimensional_sections_stalks`.
Also proved `AlgebraicGeometry.Scheme.zeroDimensional_singleton_neighbourhoods` and
`AlgebraicGeometry.Scheme.strictlyHenselianOpen_abelian_germ_isIso`.
No sorry remains in any delivered Lean module; no new sorry was introduced or split off.

The proof intentionally uses existing obligations:
`isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero`
(node `lem-weil-pbc-dimension-zero-local-strictly-henselian`) and
`AlgebraicGeometry.Scheme.strictlyHenselianOpen_toPresheafFiber_bijective`
(node `lem-weil-pbc-sets-strictly-henselian-open-sections-stalk`). These existing declarations
still contain sorry and become the next proof work; no claim of an axiom-free target is made.
The finiteness/discreteness geometry and the disjoint-cover sections theorem are already proved.

All three delivered modules compile without warnings through lcompile.py. The geometric
construction includes arbitrary nilpotents: no reducedness assumption was introduced.
Edge cases checked against the statements and proofs: empty C (empty functions, empty cover,
empty product), a single point, disconnected finite schemes, and algebraically closed Omega
larger than the residue field. The open germ helper permits an arbitrary ambient T.

## No longer needed

No original public import was removed: they support the statement and product types.
The following planned dependencies are avoided on this proof branch:

- `lem-weil-pbc-zero-dimensional-base-change-points` and its full
  `Sheaf.AlgebraicGeometry.ZeroDimensionalBaseChangePoints` module. Only the proved
  `new-zdbp-geometry` / `ZeroDimensionalBaseChangePointsGeometry` helper is needed.
  The field-extension fibre point, fibre topology and fibre homeomorphism modules are
  consequently unnecessary for this theorem.
- `lem-weil-pbc-strictly-henselian-sections-stalk` /
  `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`: use the existing set-valued
  strictly henselian open germ theorem instead, then forgetful-functor comparison.
- `lem-weil-pbc-etale-inverse-image-restriction` /
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` and
  `lem-weil-pbc-inverse-image-stalk-germ` / `Sheaf.Paper.InverseImageStalkGerm`:
  the direct open-germ theorem avoids transporting inverse image and its unit.
- `lem-weil-pbc-etale-composition-cancellation`: open inclusions are etale by Mathlib's
  existing instances; its bespoke planned invocation is unnecessary here.

These are branch-level pruning claims; other target branches may still use these nodes.
The dimension-zero strict henselianity node is retained. Definitions used by the statement
are retained. No unit-level statement or realized proof step is bypassed.

Complete audit of the old direct `proof_deps` removed from the parent node:

- `lem-weil-pbc-zero-dimensional-base-change-points`
- `def-weil-residue-field`
- `def-weil-open-immersion`
- `def-pc-scheme`
- `def-weil-affine-spectrum`
- `def-weil-algebraic-closure`
- `def-pc-separably-closed`
- `lem-weil-pbc-dimension-zero-local-strictly-henselian`
- `def-weil-pbc-henselian-terminology`
- `lem-weil-pbc-etale-composition-cancellation`
- `def-weil-pbc-etale-site`
- `def-pc-fibre-product`
- `def-weil-pbc-abelian-etale-sheaves`
- `def-weil-geometric-point`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-strictly-henselian-sections-stalk`
- `def-weil-pbc-geometric-stalks`
- `lem-weil-pbc-inverse-image-stalk-germ`

These are removed direct edges, not claims that all their modules are globally prunable.
The definition nodes still supply the signature and the helper statements; dimension-zero
strict henselianity is still a transitive proof dependency of the singleton helper.
The obsolete comparison lemmas and full base-change-points theorem are bypassed as above.
Removed the redundant proof-only `Mathlib.AlgebraicGeometry.Stalk` import from the singleton
helper; its declarations are already available through the remaining imports.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The DAG's inverse-image comparison route is longer than needed:
the existing theorem for set-valued sheaves on strictly henselian opens supplies the local
comparison directly. This is a generic tool from `sk-thm-iff`, used only to perform the
same local-germ step inside `sk-thm-p1`; it does not replace a unit-level route.

LeanSearch returned HTTP 500 for all three queries and is recorded as unavailable.
Loogle, LeanFinder and grep actually ran; their results are in searches.jsonl and the nodes.
The local checkout does not contain the Stacks tex files, so the source assertions were
checked against the official [03QO](https://stacks.math.columbia.edu/tag/03QO),
[06RS](https://stacks.math.columbia.edu/tag/06RS), and
[00KH](https://stacks.math.columbia.edu/tag/00KH) pages. The helper proof also reads Mathlib's
Nullstellensatz `residueFieldIsoBase`, singleton-affineness, and closed-point stalk isomorphism.

## New nodes

`lem-weil-pbc-zero-dimensional-singleton-neighbourhoods`:
proved structural construction of singleton open pieces and their geometric-point lifts,
with strictly henselian local coordinate rings. Its module is
`lean/Sheaf/AlgebraicGeometry/ZeroDimensionalSingletonNeighbourhoods.lean`.

`lem-weil-pbc-abelian-strictly-henselian-open-germ`:
proved transport from the existing set-valued open germ theorem to abelian groups.
Its module is `lean/Sheaf/AlgebraicGeometry/AbelianStrictlyHenselianOpenGerm.lean`.

`lem-weil-pbc-disjoint-etale-sections-product`:
records the already proved generic source theorem
`AlgebraicGeometry.Scheme.Etale.isIso_piLift_of_disjoint` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover`;
no Lean module is added for it. The original DAG had not attached this proved tool.

Blueprint searches for singleton neighbourhoods, abelian strictly henselian opens and
sheaves on disjoint covers found no duplicate blueprint statements. DAG and Lean searches
were also checked. No definition or existing statement changed, so no change record is needed.

## Second reading by N1

1. Compared the existing module with the repository using diff. Its sole existing theorem
   signature and all public imports are byte-for-byte unchanged; only proof imports,
   elaboration options and the proof were added. Both helper modules and three supporting
   nodes are new. No definition or existing statement changes, so no change record is needed.
2. Compiled all three modules with lcompile.py without warnings. Scanned all delivered Lean
   for sorry and forbidden declarations: none occur. Scratch copies with #print axioms for
   each of the three theorems report exactly propext, Classical.choice, Quot.sound and
   sorryAx. The last comes from the two explicitly reported existing open obligations;
   these are genuine reductions, not axiom-free closure. No definition is hollow.
3. No new sorry or split-off obligation. Read the helper signatures and every proof step:
   singleton opens are affine even with nilpotents; their coordinate rings are nonzero
   because each contains c, local because their prime spectrum is singleton, dimension
   zero, and have algebraically closed residue field by residueFieldIsoBase. The abelian
   helper uses the actual germ compatibility of presheafFiberCompIso, filtered-colimit
   preservation and reflection of isomorphisms, with the required universe shrink.
   Empty C requires no rings or points; Spec(k[epsilon]/epsilon^2), a disjoint pair of
   points and larger algebraically closed Omega all satisfy the same construction.
   A strictly henselian open in an arbitrary ambient scheme is allowed in the second
   helper. Read Stacks Tags [03QO](https://stacks.math.columbia.edu/tag/03QO),
   [06RS](https://stacks.math.columbia.edu/tag/06RS) and
   [00FV](https://stacks.math.columbia.edu/tag/00FV), and the cited Mathlib declarations.
   Independent rg searches using singleton/subsingleton, abelian germ, disjoint sections
   and presheafFiberCompIso found the underlying tools and no duplicate helper theorem
   in Sheaf or upstream. A fresh msearch Loogle query isIso_of_reflects_iso confirms the
   reflection tool. The disjoint-cover node records an existing proved source theorem.
4. The proof factors the global product germ through the disjoint-cover restriction
   isomorphism and the product of the local germ isomorphisms, then proves naturality
   componentwise. This is a real reduction, with no hypothesis or conclusion changed.
   No shorter existing whole-theorem proof was found. Proof-only imports remain private;
   removed one redundant Stalk import and recompiled. Read sk-thm-p1.json: none of the
   removed parent dependencies realizes a fixed unit step, and its realized fields and
   curve-calculation route remain unchanged. Completed the old direct dependency audit
   under No longer needed, distinguishing removed edges from retained transitive tools.
5. Read all four delivered nodes alongside Lean and checked proof_deps against the union
   of uses. The parent follows the compiled factorization; helper statements match their
   signatures and include complete docstring proofs, sources, blueprint, unit, chapter,
   searches, created and lean records. Corrected the singleton node's algebra-source
   document for the Nullstellensatz and henselianity steps. Corrected the disjoint-cover
   node's grep verdict and proof provenance: its Lean proof is existing upstream work.

Second reading changed only the redundant singleton-helper Stalk import, the complete
pruning audit and this review in the report, and those source/search/provenance metadata.
