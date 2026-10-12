## What changed

Replaced the sole hole in
`AlgebraicGeometry.Scheme.exists_normal_pointed_family_approximation` by a complete Lean
assembly of the existing absolute Noetherian approximation, two strictly smaller geometric
existence steps, and the actual cofiltered tail and pullback family constructions. The original
signature and all public imports are unchanged. No existing definition or statement was changed,
and no other existing module was adapted.

Added `Sheaf.AlgebraicGeometry.Morphisms.NormalNoetherianRefinement` and
`Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage`, one public named theorem in each.
The former concerns only the base, with no family, section or integer. The latter assumes an
already supplied base limit and constructs only a single pointed family model, without normality,
integrality, dominance, inverse family diagrams or limiting family cones.

The main proof restricts the base system to `Over i`, constructs the later families with
`baseChangeDiagram`, transports `baseChangeCone` through the actual cartesian comparison
isomorphism, and constructs the section natural transformation by `pullback.lift`. Its naturality,
comparison pullbacks, transition pullbacks, section equations, both limit proofs, inherited base
properties, the four base-changed morphism properties and invertibility of n are all proved.
Existential data are unpacked only inside this theorem's proof; no data definition chooses an
arbitrary witness from an unproved theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_normal_pointed_family_approximation`
(node `lem-sbc-normal-pointed-family-approximation`). No sorry remains in the item's module.

Added exactly two holes, each the entire proof of its public theorem, in separate modules:

- `AlgebraicGeometry.Scheme.exists_normal_noetherian_refinement`,
  node `lem-sbc-normal-noetherian-refinement`.
- `AlgebraicGeometry.Scheme.exists_pointed_smooth_family_stage`,
  node `lem-sbc-pointed-smooth-family-stage`.

This is a decomposition: one upper hole closed, two lower holes added, net -1; it is not a
sorry-free geometric proof. The two residual statements are strictly parts of the source argument.
Both carry their sources, complete proof explanations and matching DAG nodes.

Checked the residual statements on a single-stage system, on n = 1, and on an empty limit in the
single-stage descent statement. For a Noetherian normal integral S the first statement can use a
constant system. For a single-stage family the second can use the supplied family itself. For
n = 1 there is no invertibility obstruction. When the limit is empty and n = 0, the global-section
colimit and equality descent force a later zero ring, so the unit clause is consistent. The
normal-refinement statement assumes IsIntegral S and therefore has no empty-base case.

## No longer needed

Removed direct proof imports from the main module:
`Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite` and
`WeilConjectures.AlgebraicGeometry.Morphisms.Slicing`. These are relocated to the respective
residual modules and remain needed by their source arguments. The direct edges from the original
node to `lem-weil-pbc-finite-type-z-domain-normalization-finite`, `thm-pd-spreading-out` and
`lem-sbc-smooth-section-component-geometrically-irreducible` are replaced by edges to the two new
nodes; those existing dependencies remain beneath the appropriate residual node.

No existing node or module is globally pruned by this decomposition. In particular the absolute
Noetherian approximation and the unit's limit-reduction route remain in use.

## Where the brief, the DAG or earlier work was wrong

The sandbox from the earlier attempt contained only the unchanged original theorem and search
records. It had no proof reduction to preserve. The stated existing dependencies provide absolute
approximation, finite-presentation descent and the smooth section component separately; they do
not already assert the normalized base system or the combined single-stage pointed model.
These are the two source steps separated here, rather than a restatement of the whole theorem.

No mathematical error in the unit or existing statement was established. The unit
`sk-prop-input-spreading` keeps its limit-reduction route. LeanSearch returned Internal Server
Error for both searches; this is recorded as unavailable, not as evidence of absence. LeanFinder,
Loogle, direct Mathlib searches and source-library inspection found no exact residual interface.
The literature checkout is absent on this machine; the Stacks source pages for Tags 0EZJ, 01ZM,
0C0C and 055R were read directly online.

## New nodes

`lem-sbc-normal-noetherian-refinement` records the base-only normal approximation step of
Stacks Tag 0EZJ. Its module is `Sheaf.AlgebraicGeometry.Morphisms.NormalNoetherianRefinement`.
It uses the existing finite-normalization theorem rather than asking for new ring theory.

`lem-sbc-pointed-smooth-family-stage` records descent to one stage of the family, section,
section equation, smoothness, connected section component and invertible integer in Tag 0EZJ.
Its module is `Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage`. It uses existing
finite-presentation object/morphism/equality descent, the section-component theorem and the
Mathlib global-functions colimit node.

No change record is needed: all existing signatures, definitions and public visibility are
unchanged. The updated parent node records precisely the Lean assembly and its new dependencies.

## Second reading by S1

1. PASS. Read all three delivered modules and diffed the existing module against the
   repository. Extracted its declaration signature and checked byte-for-byte equality.
   All public imports and existing visibility are unchanged. The two added files contain
   only new theorem statements; no definition or target was changed, so no change record
   or forced adaptation is required.
2. PASS. Compiled the three modules together through lcompile.py in import order:
   3.5, 4.4 and 5.0 seconds, with no errors or warnings. Reviewed every construction in
   the parent proof, including initial restriction to Over i, transport of the limiting
   pullback cone, section naturality, cartesian cancellation, section compatibility and
   the unit ring map. Scratch copies with #print axioms show only propext, Classical.choice,
   Quot.sound and sorryAx for the parent and for each residual theorem. The two
   reported residuals are the only local sorries. No axiom, unsafe, opaque, implemented_by,
   extern, hollow definition or arbitrary existential witness in a data definition occurs.
3. PASS. Read the two residual docstring proofs against Stacks Tags 0EZJ, 055R and 0C0C.
   The first isolates normal base approximation, with no family or section; the second
   takes the supplied system and isolates descent to one stage, with no normality,
   dominance or family limit construction. Neither restates the parent. Checked constant
   normal Noetherian systems, single-stage models, n = 1, and the empty-limit/n = 0 case:
   global-section element and equality descent give a later zero ring in the last case.
   The integral-base residual excludes the empty scheme. Independent LeanFinder searches
   with different wording, a corrected Loogle query IsUnit, RingHom, and rg over Mathlib,
   lean/Sheaf and upstream Lean found normalization machinery, ordinary finite-presentation
   and morphism descent, section-component results, and global-section descent, but no
   exact residual. PointedSectionStageDescent handles only map descent, not a smooth
   geometrically connected family model. Neither residual can be closed by one of these
   existing declarations in a few minutes. Their source proofs and node signatures match.
4. PASS. The proof uses existing absolute approximation and actual base-change limit
   constructions; no shorter exact library result was found. Proof-only new imports are
   plain imports. The two removed direct imports and all three removed original DAG
   edges are listed under No longer needed and are retained below the new residuals.
   No module is globally pruned. Read sk-prop-input-spreading.json: its realized entries
   are empty in the repository; no delivery changes them, and the unit's limit-reduction
   step remains the route taken. The report correctly counts this as a decomposition:
   one original hole closed, two holes added, net -1, not a completed geometric proof.
5. PASS. Compared all three node lean.statement fields verbatim with the Lean signatures.
   The parent proof steps and proof_deps follow the implemented reduction, and each new
   node has its source, statement and proof dependencies, source proof origin, searches,
   split status, creation record, blueprint ancestry, chapter, unit and Lean record.
   The original node's other fields are preserved.

Second reading changed only this review report and the two new nodes' search records to
record the independently worded duplicate searches. No mathematical repair was needed.
An attempted removal of the local unusedVariables suppression in a scratch copy exposed
warnings on the unchanged existential proof binders in the original signature; the
suppression was therefore retained and the delivered proof was left unchanged.
