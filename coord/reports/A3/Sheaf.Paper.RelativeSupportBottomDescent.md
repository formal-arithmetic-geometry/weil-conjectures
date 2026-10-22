## What changed

`Sheaf.Paper.RelativeSupportBottomDescent` derives the specified bottom support edge,
its restriction naturality, pro-etale comparison and arbitrary-cover descent from
relative smooth-pair lower vanishing. The returned E2 repair adds the explicit finite
ambient-stalk hypothesis described below.
Private helpers prove finite-limit preservation by the kernel of left-exact functors, naturality
of the canonical Grothendieck edge from its injective-resolution cocycle formula,
and invertibility from the spectral object's interval exact sequences. The proved
public `module_cohomology_conventions` supplies injective abelian evaluation
acyclicity without exposing private source-library proof imports. No arbitrary
orientation is substituted for the specified canonical edge. The final descent
uses actual global support classes and the cohomology sheaf's separation property.

The genuinely separate geometric assertion is stated in the new module
`Sheaf.Paper.RelativeSupportVanishing`. It requires no chosen global equations or
frame and states only lower vanishing, not an edge, comparison, or descent result.
The DAG follows this separation and the actual spectral-object argument. Existing
support and scalar-forgetting interfaces retain their values and signatures.
The final inferred result types and three ordinary/derived evaluation comparison
types are annotated explicitly. The canonical
natural-number/integer cohomology comparison has a named isomorphism with explicit
endpoints, and the edge uses that same comparison under evaluation. A reflexive
coefficient isomorphism and its derived pro-etale comparison isomorphism make the
coefficient identification explicit before deriving; pro-etale edge and restriction
are composed using that isomorphism. The inserted derived image of the reflexive
isomorphism is the identity, so these are the same canonical maps. Local transparency
attributes hide comparison implementations during instance search as soon as
their invertibility APIs have been proved. The support-kernel implementation is
hidden after ordinary evaluation has been identified, with explicit unfolding in
the remaining kernel constructions. A proved private generic base-change
lemma replaces three expansions of the same derived comparison formula at
concrete sheaf categories. The local cohomology sheaf is hidden after its
comparison API and unfolded explicitly only to transport the lower-vanishing
input. This performance
repair is recorded in `coord/changes/A3-relative-support-explicit-result-types.md`.

The repair of reviewer C-c9702 E2 (returned head c9702ffff3f) requires
`ringKrullDim (V.presheaf.stalk (i z)) ≠ ⊤` for every support point in both
`relative_support_bottom_descent` and `relative_support_vanishing`. The parent
passes this hypothesis to its lower-vanishing input. The frame-independence
consumer receives the same hypothesis; its concrete frame product and canonical
support transport keep their signatures and values. LocalizedTopChern keeps all
signatures: its universal vector-bundle total spaces are locally of finite type
over k, and their stalks are Noetherian local rings of finite Krull dimension.
Its proof docstring and node record this justification.

All three repaired node statements and their exact Lean statements match the
finite-stalk convention. Their statement_change records include every current
DAG citer. The exact-name downstream audit finds no external Lean applications
of the changed theorem signatures, so there are no further call-site edits.
The requested consumer edit is mathematical preparation of its unfinished proof,
not a response to an existing compiler error. No other group's held module is
adapted and no source-library declaration is edited.

Edge cases: for empty Z the new condition is vacuous; at c=0 it imposes no change
to the negative-degree and identity-edge arguments; at a support stalk of infinite
Krull dimension it fails as intended. Finite-type ambient k-schemes, including
singular ones, satisfy it by the checked Noetherian-local-ring argument.

## Proved and sorry left

The corrected `AlgebraicGeometry.Etale.relative_support_bottom_descent` has a complete
Lean proof from the named finite-stalk lower-vanishing theorem, with complete Lean
proofs of the edge, restriction, comparison and descent clauses. The item originally
had one hole; none remains in the item module. This is a repair and decomposition
of the corrected statement, not a claim to prove the disputed former statement.

Added one hole:
`AlgebraicGeometry.Etale.relative_support_vanishing` in
`Sheaf.Paper.RelativeSupportVanishing`, node `lem-pur-relative-support-vanishing`.
This is a decomposition (one hole closed, one added; net zero), not a complete
proof of smooth-pair purity. No definition, instance, private helper, or anonymous
proof contains a hole. The new result covers the first clause alone, so it is
strictly a part of the argument rather than a renamed whole theorem.

The returned packet's one split hole is retained, not newly split during this
repair. Existing consumer holes remain unchanged:

- `WeilConjectures.PurityFiniteSetting.frameClass_independent`
  (`lem-pur-frame-independence`), with the corrected finite hypothesis;
- `WeilConjectures.PurityFiniteSetting.localizedChernTwistSucc_eq`;
- `WeilConjectures.PurityFiniteSetting.localizedChernTwistMapEtaleRaw_realization`;
- `WeilConjectures.PurityFiniteSetting.localizedChernOrdinary_realization`;
- `WeilConjectures.PurityFiniteSetting.localized_top_chern`
  (the four LocalizedTopChern holes belong to `thm-pur-localized-top-chern`).

Thus the packet has six named holes across four modules: zero in the assigned
item, one split lower-vanishing hole, one pre-existing frame-independence hole and
four pre-existing LocalizedTopChern holes. This repair adds no hole relative to
the returned packet and closes no additional hole relative to that packet.

## No longer needed

Replaced the private `import all` of
`WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison` with
the ordinary proof import `Sheaf.AlgebraicGeometry.ModuleCohomologyConventions`,
whose proved first clause has exactly the required acyclicity statement. The
existing public source import and every adopted source declaration remain.

Removed the following proof imports from the item:

- `Sheaf.CategoryTheory.FirstQuadrantLowestRowEdge`;
- `Sheaf.AlgebraicGeometry.KunnethSupported`;
- `Sheaf.Paper.RelativeSupportCoordinateModel`;
- `Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates`;
- `Sheaf.Paper.PurTwistSheafLocallyFree`;
- `Sheaf.Paper.PurityRankOneLocalCalculation`;
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`;
- `Sheaf.AlgebraicGeometry.GeometricStalkCohomology`.

The edge proof needs the existing canonical spectral object's exact intervals,
not the general lowest-row theorem or the general Cartan--Eilenberg spectral
sequence existence theorem `thm-sp-grothendieck`. The geometric coordinate and
stalk results remain dependencies of the separate vanishing node; their removal
from this item's imports does not claim that the project no longer needs them.
The finite-type coordinate support orientation supplies concentration on the
field model along the affine-line Kummer unit route. No module or declaration is
withdrawn, and the unit's realized route is preserved.

Deleted obsolete direct `tool_uses` approvals from the parent node for:
`lem-pur-smooth-pair-local-coordinates`, `lem-kun-stalks-of-cohomology`,
`lemma-weil-pbc-geometric-stalk-conservative`, `lem-pur-twist-sheaf-locally-free`,
`thm-sp-grothendieck`, `lem-kun-04ca`, `lemma-openclosed-stalk-lowerstar`,
`prop-weil-pbc-geometric-stalks-exact`, and `prop-weil-pbc-inverse-image-exact`.
The remaining approvals keep their order. Geometry and stalk tools that are still
needed are listed in the vanishing node's proof dependencies, not silently pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old dimension convention allowed infinite ambient stalk
values. In WithBot ENat, infinity=infinity+c does not distinguish c. Reviewer E2
requests finite ambient stalks before this equation is used for supported-degree
vanishing, and this packet implements that requirement explicitly in the item,
its separate vanishing input and the frame-independence consumer. At a point of
the reviewer's infinite polynomial local-ring example the new hypothesis fails.
The repair preserves all conclusions and does not silently claim that adding a
hypothesis proves the old statement. The original broad convention in the frame
product definition remains harmless for constructing the explicit product; no
vanishing assertion is part of that definition.

The dispute comments precede the theorem docstrings, keeping the blueprint tag
and proof in words attached directly to each declaration.

The earlier report's assertion that no statement was changed or disputed is
superseded by this E2 repair. The earlier decomposition, canonical spectral-object
proof, coefficient normalization and performance repairs are retained. No unit
statement, realized unit step, or target signature changes. The corrected results
still follow the same affine-line Kummer and normal-coordinate route.

Change records: `coord/changes/A3-relative-support-finite-stalks.md` and
`coord/changes/A3-relative-support-explicit-result-types.md`.

## New nodes

`lem-pur-relative-support-vanishing`, module `Sheaf.Paper.RelativeSupportVanishing`,
is the lower-vanishing part of the source normal-coordinate argument. Its proof
uses relative smooth-pair charts, the relative normal coordinate model, the
finite-type field orientation, exponent comparison, exact scalar forgetting,
and geometric-stalk conservativity. The corrected statement includes finite ambient
stalk dimensions, negative degrees, empty support and codimension zero. The node records the three Mathlib searches
and preserves the parent node's chapter and affine-line Kummer unit.

Change records: `coord/changes/A3-relative-support-explicit-result-types.md` and
`coord/changes/A3-relative-support-finite-stalks.md`.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
